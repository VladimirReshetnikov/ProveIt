"""Independent no-fill fast path for source-reconstructed occurrence matrices.

This helper authenticates ONLY a complete private-column schedule. The caller
must already have reconstructed the matrix from geometric source charts. No
producer is imported. A False return requests the existing general verifier;
it does not reject a legacy non-private schedule.
"""


def private_column_schedule(matrix, moves, allowed_columns, *, check=lambda: None):
    check()
    if type(matrix) is not list or type(moves) is not list or len(moves) != len(matrix):
        return False
    times = [-1] * len(matrix)
    columns = {}
    for t, move in enumerate(moves):
        check()
        if type(move) is not list or len(move) != 2:
            return False
        r, c = move
        if (type(r) is not int or type(c) is not int or not 0 <= r < len(matrix)
                or c not in allowed_columns or c in columns or times[r] != -1):
            return False
        if type(matrix[r]) is not dict or matrix[r].get(c, 0) != 1:
            return False
        times[r] = t
        columns[c] = t
    for r, row in enumerate(matrix):
        check()
        if type(row) is not dict:
            return False
        for c, v in row.items():
            check()
            if type(c) is not int or type(v) is not int or v < 0 or c not in allowed_columns:
                return False
            if v and c in columns and times[r] > columns[c]:
                return False
    return True
