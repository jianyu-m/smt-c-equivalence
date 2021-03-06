#-----------------------------------------------------------------
# pycparser: explore_ast.py
#
# This example demonstrates how to "explore" the AST created by
# pycparser to understand its structure. The AST is a n-nary tree
# of nodes, each node having several children, each with a name.
# Just read the code, and let the comments guide you. The lines
# beginning with #~ can be uncommented to print out useful
# information from the AST.
# It helps to have the pycparser/_c_ast.cfg file in front of you.
#
# Eli Bendersky [https://eli.thegreenplace.net/]
# License: BSD
#-----------------------------------------------------------------
from __future__ import print_function
import sys

# This is not required if you've installed pycparser into
# your site-packages/ with setup.py
#
sys.path.extend(['.', '..'])

from pycparser import c_parser, c_ast
import z3

# This is some C source to parse. Note that pycparser must begin
# at the top level of the C file, i.e. with either declarations
# or function definitions (this is called "external declarations"
# in C grammar lingo)
#
# Also, a C parser must have all the types declared in order to
# build the correct AST. It doesn't matter what they're declared
# to, so I've inserted the dummy typedef in the code to let the
# parser know Hash and Node are types. You don't need to do it
# when parsing real, correct C code.


# Create the parser and ask to parse the text. parse() will throw
# a ParseError if there's an error in the code
#

def make_variable(t, var):
    if t == 'int':
        return z3.Int(var)
    assert(False)

def unpack_variable(t):
    ptr_layer = 0
    while type(t) is c_ast.PtrDecl:
        ptr_layer = ptr_layer + 1
        t = t.type
    return (ptr_layer, t)

class Memory:
    def __init__(self):
        self.mem = {}
        self.count = 0
    def malloc(self):
        index = self.count
        self.count = index + 1
        # use None to mark a value is deallocated
        self.mem[index] = 0
        return index

    def free(self, index):
        if index in self.mem:
            self.mem[index] = None

    def set(self, index, value):
        if self.mem[index] is None:
            print("out of bound")
            assert(False)
        self.mem[index] = value

    def get(self, index):
        if index not in self.mem:
            print("out of bound")
            assert(False)
        return self.mem[index]

class Stack(Memory):
    def __init__(self):
        super().__init__()
        self.current_stack_start = 0
    
    def push_stack(self):
        self.current_stack_start = self.count
        return self

    def pop_stack(self):
        for i in range(self.count - self.current_stack_start):
            self.free(i + self.current_stack_start)
        return self

class Context:
    def __init__(self, prev, cond = None, heap = None, stack = None):
        if cond is None:
            self.vars = {}
            self.func = {}
        else:
            self.vars = prev.vars
            self.func = prev.func
        self.prev = prev
        self.heap = prev.heap if heap is None else heap
        self.stack = prev.stack if stack is None else stack
        self.reference = False
        if prev is not None and prev.ifcond is not None:
            if cond is True:
                self.ifcond = prev.ifcond
            else:
                self.ifcond = z3.And(prev.ifcond, cond)
        else:
            self.ifcond = cond

    def cond(self, icond):
        return Context(self, icond)

    def lvalue(self):
        self.reference = True
        return self

    def reset_lvalue(self):
        self.reference = False


    def solve_now(self):
        s = z3.Solver()
        s.reset()
        for k, var in self.vars.items():
            s.add(make_variable(var['t'], k) == var['v'])
        return s

def process_decl(node):
    var_name = node.name
    var_type = node.type
    # var_value = process_node(node.init, context)
    print(var_name)
    return {
        'name': var_name,
        'type': var_type,
        'value': var_name
    }

def process_node(node, context):
    if node is None:
        return None
    t = type(node)
    print(t)
    r = None
    if t is c_ast.FuncDef:
        new_context = Context(context)
        # return type process
        # process_node(node.decl.type.args, new_context)
        context.func[node.decl.type.type.declname] = node.decl.type.type.type
        process_node(node.decl.type.args, new_context)
        return process_node(node.body, new_context)
    elif t is c_ast.ParamList:
        for var in node.params:
            process_node(var, context)
    elif t is c_ast.DeclList:
        for var in node.decls:
            process_node(var, context)
    elif t is c_ast.Decl:
        var_name = node.name
        var_unpack = unpack_variable(node.type)
        var_type = var_unpack[1].type.names[0]
        var_ptr_layer = var_unpack[0]
        # var_type = node.type.type.names[0]
        var_value = process_node(node.init, context)
        var_init = make_variable(var_type, var_name) if var_value is None else var_value
        mem_idx = context.stack.malloc()
        context.stack.set(mem_idx, var_init)
        context.vars[var_name] = {
            't': var_type,
            'v': mem_idx,
            'ptr': var_ptr_layer
        }
    elif t is c_ast.Compound:
        # process a list of statement and 
        # get the return value
        for item in node.block_items:
            ret = process_node(item, context)
            if ret is not None and type(ret) is tuple:
                return ret[1]
    elif t is c_ast.ParamList:
        node.show()
    elif t is c_ast.If:
        cond = process_node(node.cond, context)
        true_r = process_node(node.iftrue, context.cond(cond))
        false_r = process_node(node.iffalse, context.cond(z3.Not(cond)))
        if true_r is not None and false_r is not None:
            r = z3.If(cond, true_r, false_r)
        return r
    elif t is c_ast.While:
        cond = process_node(node.cond, context)
        s = context.solve_now()
        s.add(cond)
        c = 0
        while True:
            if s.check() == z3.unsat:
                break
            c += 1
            context = context.cond(cond)
            process_node(node.stmt, context)
            cond = process_node(node.cond, context)
            s = context.solve_now()
            s.add(cond)
        print("unrolling " + str(c))
    elif t is c_ast.For:
        process_node(node.init, context)
        cond = process_node(node.cond, context)
        s = context.solve_now()
        s.add(cond)
        c = 0
        while True:
            if s.check() == z3.unsat:
                break
            c += 1
            context = context.cond(cond)
            process_node(node.stmt, context)
            process_node(node.next, context)
            cond = process_node(node.cond, context)
            s = context.solve_now()
            s.add(cond)
        print("unrolling " + str(c))
    elif t is c_ast.Assignment:
        assign = process_node(node.rvalue, context)
        value_idx, old_value = process_node(node.lvalue, context.lvalue())
        context.reset_lvalue()
        if node.op == "+=":
            assign = old_value + assign
        elif node.op == "-=":
            assign = old_value - assign
        # should we swap the if condition?
        if context.ifcond is not None:
            if context.ifcond == True:
                context.stack.set(value_idx, assign)
            elif context.ifcond == False:
                context.stack.set(value_idx, old_value)
            else:
                context.stack.set(value_idx, z3.If(context.ifcond, assign, old_value))
        else:
            context.stack.set(value_idx, assign)
        return assign
    elif t is c_ast.Return:
        return 0, process_node(node.expr, context)
    elif t is c_ast.BinaryOp:
        r = None
        lr = process_node(node.left, context)
        rr = process_node(node.right, context)
        if node.op == "+":
            r = lr + rr
        elif node.op == "-":
            r = lr - rr
        elif node.op == "<<":
            r = lr << rr
        elif node.op == ">>":
            r = lr >> rr
        elif node.op == "&":
            r = lr & rr
        elif node.op == "|":
            r = lr | rr
        elif node.op == "^":
            r = lr ^ rr
        elif node.op == "&&":
            r = z3.And(lr, rr)
        elif node.op == "||":
            r = z3.Or(lr, rr)
        # elif node.op == "*":
        #     r = process_node(node.left, context) * \
        #     process_node(node.right, context)
        # elif node.op == "/":
        #     r = process_node(node.left, context) / \
        #     process_node(node.right, context)
        elif node.op == "==":
            r = lr == rr
        elif node.op == "<":
            return lr < rr
        elif node.op == "<=":
            r = lr <= rr
        elif node.op == ">":
            r = lr > rr
        elif node.op == ">=":
            r = lr >= rr
        else:
            print(node.op)
            assert(False)
        return r
    elif t is c_ast.UnaryOp:
        u_expr = process_node(node.expr, context)
        if node.op == "!":
            return z3.Not(u_expr)
        elif node.op == "~":
            return ~u_expr
        elif node.op == "&":
            idx, v = process_node(node.expr, context.lvalue())
            context.reset_lvalue()
            return idx
        elif node.op == "*":
            if context.reference:
                if type(u_expr) is tuple:
                    ptr = context.stack.get(u_expr[0])
                    return ptr, context.stack.get(ptr)
                else:
                    assert(False)
            ptr = context.stack.get(u_expr)
            return context.stack.get(ptr)
        elif node.op == "p++":
            idx, v = process_node(node.expr, context.lvalue())
            context.reset_lvalue()
            context.stack.set(idx, v + 1)
            return u_expr
        else:
            assert(False)
    elif t is c_ast.Constant:
        if node.value[0] == '\'':
            return ord(node.value[1])
        return int(node.value)
    elif t is c_ast.ID:
        v = None
        idx = -1
        if node.name in context.vars:
            idx = context.vars[node.name]['v']
        else:
            assert(False)
        if context.reference:
            return idx, context.stack.get(idx)
        return context.stack.get(idx)
    else:
        print(type(node))
        assert(False)
    return None

if __name__ == "__main__":
    with open("sample.c", 'r') as f:
        text = f.read()

    parser = c_parser.CParser()
    ast = parser.parse(text, filename='sample.c')
    ast.ext[0].show()
    print("\n------------------\n")
    r = process_node(ast.ext[0], Context(None, heap = Memory(), stack = Stack()))
    solver = z3.Solver()
    solver.add(r != r)
    print(r)
    print(solver.check())
# func = 
# ast.show(showcoord=True)