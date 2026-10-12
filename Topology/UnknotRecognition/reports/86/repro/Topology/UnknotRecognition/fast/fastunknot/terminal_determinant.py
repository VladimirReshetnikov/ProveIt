"""Fraction-free terminal kernels with singular interior directions retained.

After rho interior pivots the integer border equals Delta times its Schur
complement. A quotient border of dimension d therefore has cofactor
sign * det(border) / Delta**(d-1). For d=0 the answer is sign * Delta.
This is an exact observer, not an unknot criterion.
"""
from .integer_determinant import bareiss


class IntegerTerminalKernel:
    __slots__ = ('terminals', 'interior', 'nullity', 'scale', 'sign', 'border', 'pivots')

    @classmethod
    def build(cls, laplacian, terminals, *, check=lambda: None):
        n = len(laplacian)
        if not n or any(len(row) != n for row in laplacian):
            raise ValueError('nonempty square matrix required')
        for i, row in enumerate(laplacian):
            check()
            if any(type(x) is not int for x in row):
                raise ValueError('integer matrix required')
            if any(row[j] != laplacian[j][i] for j in range(n)):
                raise ValueError('symmetric matrix required')
        terminals = tuple(terminals)
        if (not terminals or any(type(x) is not int or not 0 <= x < n for x in terminals)
                or len(set(terminals)) != len(terminals)):
            raise ValueError('distinct valid terminals required')
        terminal_set = set(terminals)
        interior = tuple(i for i in range(n) if i not in terminal_set)
        order = interior+terminals[1:]
        matrix = []
        for i in order:
            check()
            matrix.append([laplacian[i][j] for j in order])
        h, size = len(interior), len(order)
        previous, sign, k = 1, 1, 0
        pivots = []
        while k < h:
            position = None
            for i in range(k, h):
                check()
                j = next((j for j in range(k, h) if matrix[i][j]), None)
                if j is not None:
                    position = (i, j)
                    break
            if position is None:
                break
            i, j = position
            pivots.append(position)
            if i != k:
                matrix[k], matrix[i] = matrix[i], matrix[k]
                sign = -sign
            if j != k:
                for row in matrix:
                    row[k], row[j] = row[j], row[k]
                sign = -sign
            pivot = matrix[k][k]
            for i in range(k+1, size):
                check()
                row = matrix[i]
                for j in range(k+1, size):
                    row[j], remainder = divmod(pivot*row[j]-row[k]*matrix[k][j], previous)
                    if remainder:
                        raise ArithmeticError('nonexact terminal elimination division')
            previous, k = pivot, k+1
        result = cls()
        result.terminals, result.interior = terminals, interior
        result.nullity, result.scale, result.sign = h-k, previous, sign
        result.border = tuple(tuple(row[k:]) for row in matrix[k:])
        result.pivots = tuple(pivots)
        check()
        return result

    def query(self, labels, *, check=lambda: None):
        check()
        labels = tuple(labels)
        if len(labels) != len(self.terminals) or any(type(x) is not int for x in labels):
            raise ValueError('one integer label per terminal required')
        names = {}
        labels = tuple(names.setdefault(x, len(names)) for x in labels)
        q, r = len(names)-1, self.nullity
        if r > q:
            return 0
        dimension = r+q
        if dimension == 0:
            return self.sign*self.scale
        owners = tuple(range(r))+tuple(-1 if x == 0 else r+x-1 for x in labels[1:])
        matrix = [[0]*dimension for _ in range(dimension)]
        for i, a in enumerate(owners):
            check()
            if a < 0:
                continue
            for j, b in enumerate(owners):
                if b >= 0:
                    matrix[a][b] += self.border[i][j]
        numerator = self.sign*bareiss(matrix, lambda units: check())
        check()
        denominator = self.scale**(dimension-1)
        result, remainder = divmod(numerator, denominator)
        if remainder:
            raise ArithmeticError('nonintegral terminal quotient')
        check()
        return result


def verify_integer_terminal_kernel(laplacian, kernel, *, check=lambda: None):
    """Independent rational Schur replay of a kernel's recorded pivots.

    Diagnostic source binding, not a new certificate serialization protocol.
    Does not call build() or the integer update recurrence.
    """
    from fractions import Fraction
    n = len(laplacian)
    terminals = kernel.terminals
    if (not terminals or len(set(terminals)) != len(terminals)
            or any(type(x) is not int or not 0 <= x < n for x in terminals)):
        return False
    if any(len(row) != n or any(type(x) is not int for x in row) for row in laplacian):
        return False
    interior = tuple(i for i in range(n) if i not in set(terminals))
    if kernel.interior != interior:
        return False
    order = interior+terminals[1:]
    matrix = [[Fraction(laplacian[i][j]) for j in order] for i in order]
    h, size = len(interior), len(order)
    scale, sign = Fraction(1), 1
    for k, position in enumerate(kernel.pivots):
        check()
        if len(position) != 2 or any(type(x) is not int or not k <= x < h for x in position):
            return False
        i, j = position
        if i != k:
            matrix[k], matrix[i] = matrix[i], matrix[k]
            sign = -sign
        if j != k:
            for row in matrix:
                row[k], row[j] = row[j], row[k]
            sign = -sign
        pivot = matrix[k][k]
        if not pivot:
            return False
        scale *= pivot
        for i in range(k+1, size):
            check()
            for j in range(k+1, size):
                matrix[i][j] -= matrix[i][k]*matrix[k][j]/pivot
    rho = len(kernel.pivots)
    if kernel.nullity != h-rho or kernel.scale != scale or kernel.sign != sign:
        return False
    if any(matrix[i][j] for i in range(rho, h) for j in range(rho, h)):
        return False
    check()
    return kernel.border == tuple(tuple(scale*x for x in row[rho:]) for row in matrix[rho:])
