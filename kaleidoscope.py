import re

# --------------------------------------------------------------------
# Lexer

tokdefs = [
    ('whitespace', r'\s+'),
    ('comment', r'#.*'),
    ('identifier', r'[a-zA-Z][a-zA-Z0-9]*'),
    ('number', r'[0-9.]+'),
    ('other', r'.'),
]

regexps = ['(?P<%s>%s)' % (kind, regexp) for kind, regexp in tokdefs]
pattern = re.compile('|'.join(regexps))

def lex(string):
    for match in pattern.finditer(string):
        kind = match.lastgroup
        value = match.group(kind)
        if kind in ('whitespace', 'comment'):
            continue
        elif kind == 'identifier':
            if value in ('def', 'extern'):
                yield value,
            else:
                yield kind, value
        elif kind == 'number':
            yield kind, float(value)
        else:
            yield value,
    yield 'eof',

# --------------------------------------------------------------------
# Parser

class ParseError(Exception):
    pass

class Parser:

    def __init__(self, stream):
        self.stream = stream
        self.next()

    def next(self):
        self.token = self.stream.next()

    @property
    def kind(self):
        return self.token[0]

    @property
    def value(self):
        return self.token[1]

    binop_precedence = {
        '<': 10,
        '+': 20,
        '-': 20,
        '*': 40,
    }

    def precedence(self, op):
        return self.binop_precedence.get(op, -1)

    def identifier_expr(self):
        """identifier_expr
        ::= identifier
        ::= identifier '(' expression* ')'
        """
        identifier = self.value
        self.next()
        if self.kind != '(':
            return 'variable', identifier
        self.next()
        args = []
        if self.kind != ')':
            while True:
                arg = self.expression()
                args.append(arg)
                if self.kind == ')':
                    break
                if self.kind != ',':
                    raise ParseError("expected ')' or ',' in argument list")
                self.next()
        self.next()
        return 'call', identifier, args

    def number_expr(self):
        """number_expr ::= number"""
        result = self.token
        self.next()
        return result

    def paren_expr(self):
        """paren_expr ::= '(' expression ')'"""
        self.next()
        result = self.expression()
        if self.kind != ')':
            raise ParseError("expected ')'")
        self.next()
        return result

    def primary(self):
        """primary
        ::= identifier_expr
        ::= number_expr
        ::= paren_expr
        """
        kind = self.kind
        if kind == 'identifier':
            return self.identifier_expr()
        elif kind == 'number':
            return self.number_expr()
        elif kind == '(':
            return self.paren_expr()
        else:
            raise ParseError("unknown token when expecting an expression")

    def binop_rhs(self, expr_prec, lhs):
        """binop_rhs ::= ('+' primary)*"""
        while True:
            # If this is a binop, find its precedence.
            op = self.kind
            token_prec = self.precedence(op)
            # If this is a binop that binds at least as tightly as the current
            # binop, consume it, otherwise we are done.
            if token_prec < expr_prec:
                return lhs
            self.next()
            # Parse the primary expression after the binary operator.
            rhs = self.primary()
            # If BinOp binds less tightly with RHS than the operator after RHS,
            # let the pending operator take RHS as its LHS.
            next_prec = self.precedence(self.kind)
            if token_prec < next_prec:
                rhs = self.binop_rhs(token_prec+1, rhs)
            # Merge LHS/RHS.
            lhs = 'binary', op, lhs, rhs

    def expression(self):
        """expression ::= primary binop_rhs"""
        lhs = self.primary()
        return self.binop_rhs(0, lhs)

    def prototype(self):
        """prototype ::= identifier '(' identifier* ')'"""
        if self.kind != 'identifier':
            raise ParseError("expected function name in prototype")
        identifier = self.value
        self.next()
        if self.kind != '(':
            raise ParseError("expected '(' in prototype")
        self.next()
        args = []
        while self.kind == 'identifier':
            args.append(self.value)
            self.next()
        if self.kind != ')':
            raise ParseError("expected ')' in prototype")
        self.next()
        return 'prototype', identifier, args

    def definition(self):
        """definition ::= 'def' prototype expression"""
        self.next()
        prototype = self.prototype()
        expression = self.expression()
        return 'function', prototype, expression

    def toplevel(self):
        """toplevel ::= expression"""
        expression = self.expression()
        prototype = 'prototype', '', []
        return 'function', prototype, expression

    def extern(self):
        """extern ::= 'extern' prototype"""
        self.next()
        return self.prototype()

# --------------------------------------------------------------------
# Code Generation

from llvm import LLVMException
from llvm.core import Module, Type, Constant, Function, Builder
from llvm.core import FCMP_ULT

the_module = Module.new('Kaleidoscope')
named_values = {}
double_type = Type.double()

class CodegenError(Exception):
    pass

def codegen_expr(builder, expr):
    kind = expr[0]
    if kind == 'number':
        number = expr[1]
        return Constant.real(double_type, number)
    elif kind == 'variable':
        name = expr[1]
        try:
            return named_values[name]
        except KeyError:
            raise CodegenError("unknown variable name")
    elif kind == 'binary':
        op, lhs, rhs = expr[1], expr[2], expr[3]
        lhs_val = codegen_expr(builder, lhs)
        rhs_val = codegen_expr(builder, rhs)
        if op == '+':
            return builder.add(lhs_val, rhs_val, 'addtmp')
        elif op == '-':
            return builder.sub(lhs_val, rhs_val, 'subtmp')
        elif op == '*':
            return builder.mul(lhs_val, rhs_val, 'multmp')
        elif op == '<':
            i = builder.fcmp(FCMP_ULT, lhs_val, rhs_val, 'cmptmp')
            return builder.uitofp(i, 'booltmp')
        else:
            raise CodegenError("invalid binary operator")
    elif kind == 'call':
        name, args = expr[1], expr[2]
        try:
            callee = Function.get(the_module, name)
        except LLVMException:
            raise CodegenError("unknown function referenced")
        if len(callee.args) != len(args):
            raise CodegenError("incorrect # arguments passed")
        arg_vals = []
        for arg in args:
            arg_val = codegen_expr(builder, arg)
            arg_vals.append(arg_val)
        return builder.call(callee, arg_vals, 'calltmp')

def codegen_proto(proto):
    name, args = proto[1], proto[2]
    double_types = [double_type] * len(args)
    func_type = Type.function(double_type, double_types)
    try:
        func = Function.get(the_module, name)
        if func.basic_block_count:
            raise CodegenError("redefinition of function")
        if len(func.args) != len(args):
            raise CodegenError("redefinition of function with different # args")
    except LLVMException:
        func = Function.new(the_module, func_type, name)
    for arg, name in zip(func.args, args):
        arg.name = name
        named_values[name] = arg
    return func

def codegen_func(func):
    proto, body = func[1], func[2]
    named_values.clear()
    func = codegen_proto(proto)
    bb = func.append_basic_block('entry')
    builder = Builder.new(bb)
    try:
        ret_val = codegen_expr(builder, body)
        builder.ret(ret_val)
        func.verify()
        return func
    except:
        func.delete()
        raise

# --------------------------------------------------------------------
# Top-Level parsing and JIT Driver

def handle_definition(parser):
    func = parser.definition()
    func_val = codegen_func(func)
    print func_val

def main():
    while True:
        line = raw_input('ready> ')
        lexer = lex(line)
        parser = Parser(lexer)
        kind = parser.kind
        if kind == 'def':
            handle_definition(parser)

if __name__ == '__main__':
    main()
