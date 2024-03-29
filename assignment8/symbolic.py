import multiprocessing as mp
from dataclasses import dataclass
from typing import Dict

from z3 import *
from mini_py import *



class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()

# a symbolic execution engine.


# exercise 5: Run the code below, which is the data model
# of symbolic memory. Symbolic execution memory model will store arguments,
# symbolic values and path condition and concrete values.
# Make sure you understand the model and you don't need to write any code here.

# symbolic execution memory model will store arguments, symbolic values and path condition
@dataclass
class Memory:
    args: List[str]
    symbolic_memory: Dict[str, Expr]
    path_condition: List[Expr]

    def __str__(self):
        arg_str = ",".join(self.args)
        expr_str = "\n".join([f"\t{var} = {value}" for var, value in self.symbolic_memory.items()])
        cond_str = ",".join([str(cond) for cond in self.path_condition])
        return (f"Arguments: {arg_str}\n"
                f"Path Condition: {cond_str}\n"
                f"Symbol Table: \n"
                f"{expr_str}\n")


#####################
#  symbolic execution
def symbolic_expr(memory, expr):

    if isinstance(expr, ExprNum):
        return expr
    if isinstance(expr, ExprVar):

        # exercise 6: get variable's symbolic value from symbolic memory
        # be careful when deal with parameter variables. the result should
        # only contain parameters or constants
        #
        # Your code here：
        if expr.var in memory.symbolic_memory.keys():
            sym = memory.symbolic_memory[expr.var]
            if not isinstance(sym, ExprBop):
                return memory.symbolic_memory[expr.var]

            temp = sym
            # NOTE: Try to get the deepest expression
            while isinstance(temp, ExprBop):
                right = temp.right
                if isinstance(right, ExprVar) and right.var == expr.var:
                    pass
                else:
                    right = symbolic_expr(memory, right)
                temp = temp.left
            return sym
        else:
            return expr

        # raise Todo("exercise 6: please fill in the missing code.")

    if isinstance(expr, ExprBop):
        left = symbolic_expr(memory, expr.left)
        right = symbolic_expr(memory, expr.right)
        return ExprBop(left, right, expr.bop)


def symbolic_stmt(memory, stmt, rest_stmts, results):
    if isinstance(stmt, StmtAssign):
        memory.symbolic_memory[stmt.var] = symbolic_expr(memory, stmt.expr)
        return symbolic_stmts(memory, rest_stmts, results)

    if isinstance(stmt, StmtIf):
        # exercise 6: process the if-statement by split the symbolic memory,
        # use the python multiprocessing module to do this work. the target function
        # wil be the symbolic_stmts, read it carefully.
        #
        # Your code here：
        p1 = mp.Process(target=symbolic_stmts, args=(memory, stmt.then_stmts, results, symbolic_expr(memory, stmt.expr)))
        p2 = mp.Process(target=symbolic_stmts, args=(memory, stmt.else_stmts, results, symbolic_expr(memory, neg_exp(stmt.expr))))

        p1.start()
        p2.start()

        p1.join()
        p2.join()


def symbolic_stmts(memory, stmts, results, condition=None):
    if condition:
        memory.path_condition.append(symbolic_expr(memory, condition))

    if not stmts:
        results.put(memory)
    else:
        symbolic_stmt(memory, stmts[0], stmts[1:], results)

    return results


def symbolic_function(func):
    # init memory
    init_params = [ExprVar(arg) for arg in func.args]
    memory = Memory(func.args, dict(zip(func.args, init_params)), [])

    results = symbolic_stmts(memory, func.stmts, mp.SimpleQueue())
    result_list = []

    while not results.empty():
        result = results.get()
        print(result)
        result_list.append(result)

    return result_list


#####################
# compile AST expression to Z3
def expr_2_z3(expr):
    # exercise 7: converts path conditions (AST nodes) to equivalent
    # Z3 constraints. it will used by check_cond function which you
    # need to read.
    #
    # Your code here：
    
    if isinstance(expr, ExprNum):
        return expr.num
    if isinstance(expr, ExprVar):
        return Int(expr.var)
    if isinstance(expr, ExprBop):
        if expr.bop is Bop.ADD:
            return expr_2_z3(expr.left) + expr_2_z3(expr.right)
        if expr.bop is Bop.MIN:
            return expr_2_z3(expr.left) - expr_2_z3(expr.right)
        if expr.bop is Bop.MUL:
            return expr_2_z3(expr.left) * expr_2_z3(expr.right)
        if expr.bop is Bop.DIV:
            return expr_2_z3(expr.left) / expr_2_z3(expr.right)
        if expr.bop is Bop.EQ:
            return expr_2_z3(expr.left) == expr_2_z3(expr.right)
        if expr.bop is Bop.NE:
            return expr_2_z3(expr.left) != expr_2_z3(expr.right)
        if expr.bop is Bop.GT:
            return expr_2_z3(expr.left) > expr_2_z3(expr.right)
        if expr.bop is Bop.GE:
            return expr_2_z3(expr.left) >= expr_2_z3(expr.right)
        if expr.bop is Bop.LT:
            return expr_2_z3(expr.left) < expr_2_z3(expr.right)
        if expr.bop is Bop.LE:
            return expr_2_z3(expr.left) <= expr_2_z3(expr.right)

    return []

    # raise Todo("exercise 7: please fill in the missing code.")

# negate the condition
def neg_exp(expr: Expr):
    assert isinstance(expr, ExprBop), "negate the bop expression"
    if expr.bop is Bop.EQ:
        return ExprBop(expr.left, expr.right, Bop.NE)
    if expr.bop is Bop.NE:
        return ExprBop(expr.left, expr.right, Bop.EQ)
    if expr.bop is Bop.GT:
        return ExprBop(expr.left, expr.right, Bop.LE)
    if expr.bop is Bop.GE:
        return ExprBop(expr.left, expr.right, Bop.LT)
    if expr.bop is Bop.LT:
        return ExprBop(expr.left, expr.right, Bop.GE)
    if expr.bop is Bop.LE:
        return ExprBop(expr.left, expr.right, Bop.GT)

# use Z3 to solve conditions
def check_cond(memory, add_cond=None):
    solver = Solver()

    # add path condition
    for cond in memory.path_condition:
        solver.add(expr_2_z3(cond))

    # add additional condition
    if add_cond:
        for cond in add_cond:
            solver.add(expr_2_z3(symbolic_expr(memory, cond)))

    check_result = solver.check()

    return check_result, solver

###############################
# test function:
#
# def f2(a,b):
# 	x = 1
# 	y = 0
# 	if a != 0 :
# 		y = x + 3
# 		if b == 0 :
# 			x = 2 * a + b
# 	return x
#
f1 = Function('f1', ['a', "b"],
              [StmtAssign('x', ExprNum(1)),
               StmtAssign('y', ExprNum(0)),
               StmtIf(ExprBop(ExprVar('a'), ExprNum(0), Bop.NE),
                      [StmtAssign('y', ExprBop(ExprVar('x'), ExprNum(3), Bop.ADD)),
                      StmtIf(ExprBop(ExprVar('b'), ExprNum(0), Bop.EQ),
                             [StmtAssign('x', ExprBop(ExprNum(2), ExprBop(ExprVar('a'), ExprVar('b'), Bop.ADD), Bop.MUL))],
                             [])],
                      [])
               ], ExprVar('x'))


if __name__ == '__main__':
    example_memory = Memory(args=["a", "b", "c"],
                            symbolic_memory={"a": ExprVar("a"),
                                             "b": ExprBop(ExprNum(42), ExprVar("a"), Bop.MIN),
                                             "c": ExprBop(ExprVar("c"), ExprNum(20), Bop.ADD),
                                             "m": ExprBop(ExprVar("b"), ExprNum(5), Bop.MUL),
                                             "n": ExprBop(ExprVar("c"), ExprNum(2), Bop.MUL)},
                            path_condition=[])

    example_exp = ExprBop(ExprVar("m"), ExprVar("n"), Bop.EQ)

    # Should output:
    #
    # [m == n]  ===>  [((42 - a) * 5) == ((c + 20) * 2)]
    #
    print(f"[{example_exp}]  ===>  [{symbolic_expr(example_memory, example_exp)}]\n")
    # Should output(order can be different):
    #
    # Arguments: a,b
    # Path Condition: a == 0
    # Symbol Table:
    #   a = a
    #   b = b
    #   x = 1
    #   y = 0
    #
    # Arguments: a,b
    # Path Condition: a != 0, b != 0
    # Symbol Table:
    #   a = a
    #   b = b
    #   x = 1
    #   y = 1 + 3
    #
    # Arguments: a,b
    # Path Condition: a != 0, b == 0
    # Symbol Table:
    #   a = a
    #   b = b
    #   x = 2 * (a + b)
    #   y = 1 + 3
    #
    result_memories = symbolic_function(f1)

    # Should output:
    #
    # Conditions: [a != 0, b == 0, 2*(a + b) - 4 == 0]
    # SAT Input: a = 2, b = 0
    #

    # check: x - y = 0
    check_conditions = [ExprBop(ExprBop(ExprVar('x'), ExprVar('y'), Bop.MIN), ExprNum(0), Bop.EQ)]

    for result_memory in result_memories:
        ret, s = check_cond(result_memory, check_conditions)
        if ret == sat:
            print(f"Conditions: {s}")
            print(f"SAT Input: {s.model()}")
