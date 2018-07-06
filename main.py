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


class Context:
    def __init__(self, prev):
        self.vars = {}
        self.prev = prev
        self.func = {}

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
    elif t is c_ast.Decl:
        var_name = node.name
        var_type = node.type
        # var_value = process_node(node.init, context)
        context.vars[var_name] = {
            't': var_type,
            'v': var_name
        }
    elif t is c_ast.Compound:
        # process a list of statement and 
        # get the return value
        for item in node.block_items:
            ret = process_node(item, context)
            if ret is not None:
                return ret
    elif t is c_ast.ParamList:
        node.show()
    elif t is c_ast.Assignment:
        print(type(node.lvalue))
    elif t is c_ast.Return:
        return process_node(node.expr, context)
    elif t is c_ast.BinaryOp:
        return process_node(node.left, context) + \
            node.op + process_node(node.right, context)
    elif t is c_ast.ID:
        v = ""
        if node.name in context.vars:
            v = context.vars[node.name]['v']
        return v
    else:
        print(type(node))
        print("should not reach here\n")
    return None

if __name__ == "__main__":
    with open("sample.c", 'r') as f:
        text = f.read()

    parser = c_parser.CParser()
    ast = parser.parse(text, filename='sample.c')
    ast.ext[0].show()
    print("\n------------------\n")
    r = process_node(ast.ext[0], Context(None))
    print(r)
# func = 
# ast.show(showcoord=True)