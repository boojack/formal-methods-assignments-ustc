"""N-queens puzzle

The  N-queens problem is about placing N chess queens on an N*N chessboard so that
no two queens threaten each other. A solution requires that no two queens share the
same row, column diagonal or anti-diagonal.The problem's target is try to find how
many solutions exist.

"""

import time
from z3 import *


class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()


def n_queen_la(board_size: int, verbose: bool = False) -> int:
    solver = Solver()
    n = board_size

    # Each position of the board is represented by a 0-1 integer variable:
    #   ...    ...    ...    ...
    #   x_2_0  x_2_1  x_2_2  ...
    #   x_1_0  x_1_1  x_1_2  ...
    #   x_0_0  x_0_1  x_0_2  ...
    #
    board = [[Int(f"x_{row}_{col}") for col in range(n)] for row in range(n)]

    # only be 0 or 1 in board
    for row in board:
        for pos in row:
            solver.add(Or(pos == 0, pos == 1))

    # @exercise 11: please fill in the missing code to add
    # the following constraint into the solver:
    # raise Todo("exercise 11: please fill in the missing code.")
    #   each row has just 1 queen,
    for row in board:
        solver.add(sum(row) == 1)
    #   each column has just 1 queen,
    for i in range(n):
        col_exp = []
        for row in board:
            col_exp.append(row[i])
        solver.add(sum(col_exp) == 1)
    #   each diagonal has at most 1 queen,
    for d in range(-n+1, n):
        dia_exp = []
        for i in range(n):
            for j in range(n):
                if j-i == d:
                    dia_exp.append(board[i][j])
        solver.add(sum(dia_exp) <= 1)
    #   each anti-diagonal has at most 1 queen.
    for d in range(n*2-1):
        dia_exp = []
        for i in range(n):
            for j in range(n):
                if j+i == d:
                    dia_exp.append(board[i][j])
        solver.add(sum(dia_exp) <= 1)

    # count the number of solutions
    solution_count = 0

    start = time.time()
    while solver.check() == sat:
        solution_count += 1
        model = solver.model()

        if verbose:
            # print the solution
            print([(row_index, col_index) for row_index, row in enumerate(board)
                   for col_index, flag in enumerate(row) if model[flag] == 1])

        # generate constraints from solution
        solution_cons = [(flag == 1) for row in board for flag in row if model[flag] == 1]

        # add solution to the solver to get new solution
        solver.add(Not(And(solution_cons)))

    print(f"n_queen_la solve {board_size}-queens by {(time.time() - start):.6f}s")
    return solution_count


# 回溯算法 backtrack
def n_queen_bt(board_size: int, verbose: bool = False) -> int:
    n = board_size
    solutions = [[]]

    def is_safe(col, solution):
        same_col = col in solution
        same_diag = any(abs(col - j) == (len(solution) - i) for i, j in enumerate(solution))

        return not (same_col or same_diag)

    start = time.time()
    for row in range(n):
        solutions = [solution + [col] for solution in solutions for col in range(n) if is_safe(col, solution)]
    print(f"n_queen_bt solve {board_size}-queens by {(time.time() - start):.6f}s")

    if verbose:
        # print the solutions
        for solution in solutions:
            print(list(enumerate(solution)))

    return len(solutions)


def n_queen_la_opt(board_size: int, verbose: bool = False) -> int:
    solver = Solver()
    n = board_size

    # We know each queen must be in a different row.
    # So, we represent each queen by a single integer: the column position
    # the q_i = j means queen in the row i and column j.
    queens = [Int(f"q_{i}") for i in range(n)]

    # each queen is in a column {0, ... 7 }
    solver.add([And(0 <= queens[i], queens[i] < n) for i in range(n)])

    # one queen per column
    solver.add([Distinct(queens)])

    # at most one for per anti-diagonal & diagonal
    solver.add([If(i == j, True, And(queens[i] - queens[j] != i - j, queens[i] - queens[j] != j - i))
                for i in range(n) for j in range(i)])

    # count the number of solutions
    solution_count = 0
    start = time.time()

    while solver.check() == sat:
        solution_count += 1
        model = solver.model()

        if verbose:
            # print the solutions
            print([(index, model[queen]) for index, queen in enumerate(queens)])

        # generate constraints from solution
        solution_cons = [(queen == model[queen]) for queen in queens]

        # add solution to the solver to get new solution
        solver.add(Not(And(solution_cons)))

    print(f"n_queen_la_opt solve {board_size}-queens by {(time.time() - start):.6f}s")

    return solution_count


if __name__ == '__main__':
    # 8-queen problem has 92 solutions
    n_queen_la(8)
    
    # @exercise 12: Try to compare the backtracking with the LA algorithms,
    # by changing the value of the chessboard size to other values,
    # which one is faster? What conclusion you can draw from the result?
    n_queen_bt(8)
    n_queen_la_opt(8)
    n_queen_bt(12)
    # # raise Todo("exercise 12: please fill in the missing code.")

    # # @exercise 13: Try to compare the efficiency of n_queen_la_opt() method
    # # with your n_queen_la() method.
    # # What's your observation? What conclusion you can draw?
    # raise Todo("exercise 13: please fill in the missing code.")
    n_queen_la_opt(12)
    n_queen_la(12)

    # NOTE:
    # 现象：
    # 当n=8时，bt用了0.07s，la_opt用了0.99s，la用了3s
    # 当n=12时，bt用了60s，la_opt用了400+s，la用了---s（很慢很慢）
    # 总体时间效率上：bt > la_opt > la
    #
    # 结论：
    # 回溯法在每次选择后，会摒弃无法实现的路径，从而大量减少需要计算的数据量，因此效率大于la
