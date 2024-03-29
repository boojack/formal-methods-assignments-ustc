""" Knapsack problem


The knapsack problem is a typical optimization problem，which has been
studied for hundred of years. The problem is: given a set of items, each
item has a weight and a value, determine the number of items such that the
total weight is less than a given limit and the total value is as large
as possible. There are a number of sub-problems of the knapsack problem:
0-1 knapsack problem, complete knapsack problem, multiply knapsack problem,
multi-dimensional knapsack problem and so on.

This problem is NPC, and for more background information of the
knapsack problem, please refer to:
https://en.wikipedia.org/wiki/Knapsack_problem
"""

import time
from pathlib import Path

from z3 import *


class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()


# 0-1 Knapsack problem
#
# The 0-1 knapsack problem is
# There are n items, with specific weight
#   W = {w1, ..., wn}
# and value:
#   V = {v1, ..., vn}
# For a given knapsack of maximum capacity C, how to choose some items
# such that:
#   wi+...+wk <= C
# and with maximum value
#   max(vi+...+vk).

# Here is a concrete example:
#   W = {4, 6, 2, 2, 5, 1}
#   V = {8, 10, 6, 3, 7, 2}
# the result is: we should select the first, second, and third items, and
# the total value is:
#   8+10+6 = 24

# The 0-1 knapsack problem is often solved by the dynamic
# programming, and here is a DP algorithm:
def zero_one_knapsack_dp(weights, values, cap):
    def knapsack_dp_do(rest_cap, index):
        if rest_cap <= 0 or index <= 0:
            return 0

        if weights[index - 1] > rest_cap:
            return knapsack_dp_do(rest_cap, index - 1)

        value_1 = knapsack_dp_do(rest_cap, index - 1)
        value_2 = knapsack_dp_do(rest_cap - weights[index - 1], index - 1)

        if value_1 >= (value_2 + values[index - 1]):
            return value_1

        return value_2 + values[index-1]

    start = time.time()
    result = knapsack_dp_do(cap, len(weights))
    print(f"zero_one_knapsack_dp solve {len(weights)} items by time {(time.time() - start):.6f}s")
    return result


# But it's more natural and much easier to solve knapsack with the 0-1 ILP theory:
def zero_one_knapsack_lp(weights, values, cap, verbose=False):
    # create a new solver, but
    solver = Optimize()

    # the decision variables
    flags = [Int(f"x_{i}") for i in range(len(weights))]
    # print(flags)

    # flags are 0-1
    for flag in flags:
        solver.add(Or(flag == 0, flag == 1))

    # @exercise 15: solve the 0-1 knapsack problem by using 0-1 ILP
    # construct the constraint
    #   \sum_i weights[i] * flags[i] <= cap
    # and the the target
    #   \sum_i values[i] * flags[i]
    # Your code here:
    # @begin
    wei_list = []
    val_list = []
    for i in range(len(flags)):
        wei_list.append(weights[i] * flags[i])
        val_list.append(values[i] * flags[i])
    cons = [sum(wei_list) <= cap]
    solver.add(cons)
    solver.maximize(sum(val_list))

    # raise Todo("exercise 15: please fill in the missing code.")
    # @end

    start = time.time()
    result = solver.check()
    print(f"zero_one_knapsack_lp solve {len(weights)} items by time {(time.time() - start):.6f}s")

    if result == sat:
        model = solver.model()

        # print the chosen items
        if verbose:
            print("\n".join([f"Index: {index}, Weight: {weights[index]}, Value: {values[index]}"
                             for index, flag in enumerate(flags) if model[flag] == 1]))

        return True, sum([values[index] for index, flag in enumerate(flags) if model[flag] == 1])

    return False, result


# The complete knapsack problem assumes that the number of items of all kinds is unlimited,
# your can choose one kind of item any times.
# So we need to declare a variable for each kind of item have chosen by amount
def complete_knapsack_lp(weights, values, cap, verbose=False):
    solver = Optimize()

    # @exercise 16: solve the complete knapsack problem by using LP
    # note that flags[i] will be a integer and flags[i] >= 0
    # construct the constraint
    #   \sum_i weights[i] * flags[i] <= cap
    # and the the target
    #   \sum_i values[i] * flags[i]
    # Your code here:
    # @begin
    counts = [Int(f"x_{i}") for i in range(len(weights))]

    for count in counts:
        solver.add(count >= 0)
    
    wei_list = []
    val_list = []
    for i in range(len(counts)):
        wei_list.append(weights[i] * counts[i])
        val_list.append(values[i] * counts[i])

    cons = [sum(wei_list) <= cap]
    solver.add(cons)
    solver.maximize(sum(val_list))

    # raise Todo("exercise 16: please fill in the missing code.")
    # @end
    start = time.time()
    result = solver.check()
    print(f"zero_one_knapsack_lp solve {len(weights)} items by time {(time.time() - start):.6f}s")

    if result == sat:
        model = solver.model()
        max_vals = 0
        for index, count in enumerate(counts):
            count = model[count].as_long()
            if count > 0:
                print("Index: " + str(index) + ", Weight: " + str(weights[index]) + ", Value: " + str(values[index]) + ", Amount: " + str(count))
                max_vals += values[index] * count

        return max_vals          

    return False, result


def get_large_test():
    # this test data is fetched from:
    # https://people.sc.fsu.edu/~jburkardt/datasets/knapsack_01/knapsack_01.html
    # the expect maximum value should be: 13549094
    def read_numbers_from_file(file_path):
        with Path(file_path).open(mode="r") as fp:
            content = fp.readlines()
            return [int(x.strip()) for x in content]

    file_folder = Path(__file__).parent.resolve()
    return (read_numbers_from_file(file_folder / "p08_w.txt"),
            read_numbers_from_file(file_folder / "p08_p.txt"))


if __name__ == '__main__':
    # a small test case
    W = [4, 6, 2, 2, 5, 1]
    V = [8, 10, 6, 3, 7, 2]
    C = 12
    print(zero_one_knapsack_dp(W, V, C))
    print(zero_one_knapsack_lp(W, V, C))

    # another test case
    W = [23, 26, 20, 18, 32, 27, 29, 26, 30, 27]
    V = [505, 352, 458, 220, 354, 414, 498, 545, 473, 543]
    C = 67
    print(zero_one_knapsack_dp(W, V, C))
    print(zero_one_knapsack_lp(W, V, C))

    # test case for complete knapsack problem
    # it should print:
    #
    # Index: 0, Weight: 23, Value: 505, Amount: 4
    # Index: 2, Weight: 20, Value: 458, Amount: 2
    # Maximal Value:  2936
    #
    C = 133
    print("Maximal Value: ", complete_knapsack_lp(W, V, C, verbose=True))

    # a large test case
    W, V = get_large_test()
    C = 6404180

    # @exercise 17: compare the efficiency of the DP and the
    # LP algorithm, by running your program on a larger data.
    # what's your observation? What conclusion you can draw from these data?
    # Your code here:
    # @begin
    # raise Todo("exercise 17: please fill in the missing code.")
    zero_one_knapsack_dp(W, V, C)
    # FIXME: lp took too much time
    # zero_one_knapsack_lp(W, V, C)
    print("lp took too much time")
    # @end
    
    # NOTE:
    # 现象：
    # 当在数据量较大时，dp可以在可视时间内运行完成，而lp”卡死“。
    #
    # 结论：
    # 与最小子集问题结论相反，在背包问题上dp效率高于lp算法。原因可能是：
    # 动态规划用空间换取时间效率，线性规划的时间复杂度达到了O(n^3)
    # 
    # (不知道为什么在最小子集和背包问题上，dp和lp的表现相反 :()