"""Interruptible fraction-free integer determinant shared by exact backends."""


def bareiss(matrix, tick):
    """Fraction-free integer determinant; poll between elimination rows."""
    size = len(matrix)
    if not size:
        return 1
    previous, sign = 1, 1
    for k in range(size - 1):
        tick(size - k)
        pivot = next((i for i in range(k, size) if matrix[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            matrix[k], matrix[pivot] = matrix[pivot], matrix[k]
            sign = -sign
        value = matrix[k][k]
        for i in range(k + 1, size):
            tick(size - k - 1)
            row = matrix[i]
            for j in range(k + 1, size):
                row[j], remainder = divmod(value * row[j] - row[k] * matrix[k][j], previous)
                if remainder:
                    raise ArithmeticError("nonexact fraction-free determinant division")
            row[k] = 0
        previous = value
    return sign * matrix[-1][-1]

