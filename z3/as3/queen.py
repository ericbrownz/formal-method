from z3 import *


class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()


def four_queen():
    solver = Solver()
    # the basic data structure:
    N = 10
    # board = [[Bool('b_{}_{}'.format(i, j)) for i in range(N)]
    #          for j in range(N)]
    board = [[Int(f"x_{row}_{col}") for col in range(N)] for row in range(N)]

    for row in board:
        for pos in row:
            solver.add(Or(pos == 0, pos == 1))

    sigma_F = []
    # constraint 1: each row has just one queen:
    # rows = []
    # for i in range(N):
    #     current_row = []
    #     for j in range(N):
    #         current_row.append(board[i][j])
    #         for k in range(N):
    #             if k != j:
    #                 current_row.append(Not(board[i][k]))
    #     rows.append(current_row)
    for i in range(N):
        for j in range(N):
            sigma_F.append(board[i][j])
        solver.add(sum(sigma_F) == 1)
        sigma_F.clear()

    # constraint 2: each column has just one queen:
    for j in range(N):
        for i in range(N):
            sigma_F.append(board[i][j])
        solver.add(sum(sigma_F) == 1)
        sigma_F.clear()

    # constraint 3: each diagonal has at most one queen:
    for d in range(1 - N, N):
        for i in range(max(d, 0), min(N, N + d)):  # d >= 0, i range[d,n); d < 0, i range[0,n+d)
            sigma_F.append(board[i][i - d])
        solver.add(sum(sigma_F) <= 1)
        sigma_F.clear()

    # constraint 4: each anti-diagonal has at most one queen:
    for d in range(0, 2 * N - 1):
        for i in range(max(d - (N - 1), 0), min(d, N)):  # d <= n-1, i range[0,d); d >= n, i range[d-(n-1),n)
            sigma_F.append(board[i][d - i])
        solver.add(sum(sigma_F) <= 1)
        sigma_F.clear()

    res = solver.check()
    if res == sat:
        model = solver.model()
        print(model)
    else:
        print(res)

if __name__ == '__main__':
    # Four Queen should have 2 set of solutions
    four_queen()
