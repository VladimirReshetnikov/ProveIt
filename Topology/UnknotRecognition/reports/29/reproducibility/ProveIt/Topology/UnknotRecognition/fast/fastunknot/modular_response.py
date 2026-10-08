"""Exact terminal-identification response over a checked odd prime field.

For an integer signed Laplacian, eliminate only nonterminal coordinates.  A
symmetric 1-by-1 / 2-by-2 pivot scheme retains the entire radical of that block.
Consequently an exceptional prime changes the pivot profile, never the answer.
Each grounded terminal quotient is a determinant of size ``nullity + q``, where
q is its number of ungrounded terminal blocks.  It is identically zero when
``nullity > q``; every nontrivial query therefore has size at most ``2*(b-1)``.

Setup is dense: O(n**3) field operations and O(n**2) space in the worst case.
The class does not imply a bound on scanner width, number of stages or queries.
Every public operation accepts a no-argument cancellation/work callback.  A
callback exception propagates; neither a partial kernel nor a partial query is
published or cached.  The caller owns publication and any query cache.
"""


def _noop():
    pass


def validate_prime(prime, check=None):
    """Validate an odd prime at most 2**31-1, deterministically.

    Strong Miller--Rabin bases 2, 7 and 61 are deterministic below
    4,759,123,141, which contains the entire supported range.  Keeping the range
    explicit prevents a probable-prime test from silently becoming a field
    assumption for larger inputs.  No unchecked composite reaches inversion.
    """
    check = _noop if check is None else check
    check()
    if type(prime) is not int or not 3 <= prime <= (1 << 31) - 1 or prime % 2 == 0:
        raise ValueError("prime must be an odd prime at most 2**31-1")
    for divisor in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        check()
        if prime == divisor:
            return prime
        if prime % divisor == 0:
            raise ValueError("modulus is composite")
    exponent, twos = prime - 1, 0
    while exponent % 2 == 0:
        check()
        exponent //= 2
        twos += 1
    for base in (2, 7, 61):
        check()
        if base % prime == 0:
            continue
        value = pow(base, exponent, prime)
        check()
        if value in (1, prime - 1):
            continue
        for _ in range(twos - 1):
            check()
            value = value * value % prime
            if value == prime - 1:
                break
        else:
            raise ValueError("modulus is composite")
    return prime


def _canonical_partition(partition, size, check):
    names, result = {}, []
    for label in partition:
        check()
        if type(label) is not int or label < 0:
            raise ValueError("partition labels must be nonnegative integers")
        if len(result) >= size:
            raise ValueError("partition must label every terminal exactly once")
        result.append(names.setdefault(label, len(names)))
    if len(result) != size:
        raise ValueError("partition must label every terminal exactly once")
    return tuple(result), len(names)


def _determinant(matrix, prime, check):
    """Independent row pivoting for the small query matrix; consumes matrix."""
    determinant = 1
    for column in range(len(matrix)):
        check()
        pivot = None
        for row in range(column, len(matrix)):
            check()
            if matrix[row][column]:
                pivot = row
                break
        if pivot is None:
            return 0
        if pivot != column:
            matrix[column], matrix[pivot] = matrix[pivot], matrix[column]
            determinant = -determinant
        value = matrix[column][column]
        determinant = determinant * value % prime
        inverse = pow(value, -1, prime)
        for row in range(column + 1, len(matrix)):
            check()
            factor = matrix[row][column] * inverse % prime
            matrix[row][column] = 0
            for j in range(column + 1, len(matrix)):
                check()
                matrix[row][j] = (matrix[row][j] - factor * matrix[column][j]) % prime
    return determinant % prime


def _symmetric_swap(matrix, first, second, check):
    if first == second:
        return
    check()
    matrix[first], matrix[second] = matrix[second], matrix[first]
    for row in matrix:
        check()
        row[first], row[second] = row[second], row[first]


class ModularTerminalKernel:
    """A reusable exact response for identifications of specified terminals.

    ``laplacian`` must be a nonempty, square, symmetric integer matrix with
    zero row sums. ``terminals`` is a nonempty list of distinct vertex indices.
    Query labels describe an arbitrary partition in terminal-list order; labels
    need not be consecutive. The first terminal block is the grounded block.
    Input matrices are never mutated. Stored response/coupling arrays are tuples.
    """

    @classmethod
    def build(cls, laplacian, terminals, prime, check=None):
        check = _noop if check is None else check
        check()
        prime = validate_prime(prime, check)
        rows = []
        for row in laplacian:
            check()
            values, total = [], 0
            for value in row:
                check()
                if type(value) is not int:
                    raise ValueError("laplacian entries must be integers")
                values.append(value)
                total += value
            if total:
                raise ValueError("laplacian rows must sum to zero over the integers")
            rows.append(tuple(values))
        size = len(rows)
        if not size:
            raise ValueError("laplacian must be nonempty")
        for row in rows:
            check()
            if len(row) != size:
                raise ValueError("laplacian must be square")
        for i in range(size):
            check()
            for j in range(i):
                check()
                if rows[i][j] != rows[j][i]:
                    raise ValueError("laplacian must be symmetric")
        terminal_list, terminal_set = [], set()
        for vertex in terminals:
            check()
            if (type(vertex) is not int or not 0 <= vertex < size
                    or vertex in terminal_set):
                raise ValueError("terminals must be distinct vertex indices")
            terminal_list.append(vertex)
            terminal_set.add(vertex)
        if not terminal_list:
            raise ValueError("at least one terminal is required")
        interior = []
        for vertex in range(size):
            check()
            if vertex not in terminal_set:
                interior.append(vertex)
        indices = interior + terminal_list
        matrix = []
        for i in indices:
            check()
            row = []
            for j in indices:
                check()
                row.append(rows[i][j] % prime)
            matrix.append(row)
        m, b = len(interior), len(terminal_list)
        eliminated = one_pivots = two_pivots = 0
        factor = 1
        while eliminated < m:
            check()
            k = eliminated
            diagonal = None
            for i in range(k, m):
                check()
                if matrix[i][i]:
                    diagonal = i
                    break
            if diagonal is not None:
                _symmetric_swap(matrix, k, diagonal, check)
                pivot = matrix[k][k]
                inverse = pow(pivot, -1, prime)
                factor = factor * pivot % prime
                for i in range(k + 1, size):
                    check()
                    coefficient = matrix[i][k] * inverse % prime
                    for j in range(i, size):
                        check()
                        value = (matrix[i][j] - coefficient * matrix[k][j]) % prime
                        matrix[i][j] = matrix[j][i] = value
                eliminated += 1
                one_pivots += 1
                continue
            pair = None
            for i in range(k, m):
                check()
                for j in range(i + 1, m):
                    check()
                    if matrix[i][j]:
                        pair = (i, j)
                        break
                if pair is not None:
                    break
            if pair is None:
                break  # Entire residual interior block is zero.
            first, second = pair
            _symmetric_swap(matrix, k, first, check)
            # second > first >= k, so the first swap did not move second.
            _symmetric_swap(matrix, k + 1, second, check)
            pivot = matrix[k][k + 1]
            inverse = pow(pivot, -1, prime)
            factor = -factor * pivot * pivot % prime
            for i in range(k + 2, size):
                check()
                left = matrix[i][k] * inverse % prime
                right = matrix[i][k + 1] * inverse % prime
                for j in range(i, size):
                    check()
                    value = (matrix[i][j] - left * matrix[k + 1][j]
                             - right * matrix[k][j]) % prime
                    matrix[i][j] = matrix[j][i] = value
            eliminated += 2
            two_pivots += 1
        nullity = m - eliminated
        # If no partition can absorb the radical, retain no unnecessary block.
        universal_zero = nullity > b - 1
        coupling, response = [], []
        if not universal_zero:
            for i in range(eliminated, m):
                check()
                row = []
                for j in range(m, size):
                    check()
                    row.append(matrix[i][j])
                coupling.append(tuple(row))
            for i in range(m, size):
                check()
                row = []
                for j in range(m, size):
                    check()
                    row.append(matrix[i][j])
                response.append(tuple(row))
        check()
        result = cls()
        result.prime = prime
        result.terminals = tuple(terminal_list)
        result.factor = factor
        result.nullity = nullity
        result.coupling = tuple(coupling)
        result.response = tuple(response)
        result.universal_zero = universal_zero
        result.stats = dict(matrix_size=size, interior_size=m, terminals=b,
                            eliminated=eliminated, nullity=nullity,
                            one_pivots=one_pivots, two_pivots=two_pivots,
                            universal_zero=universal_zero)
        return result

    def query(self, partition, check=None):
        """Return the quotient graph's tree cofactor modulo the validated prime."""
        check = _noop if check is None else check
        check()
        labels, blocks = _canonical_partition(partition, len(self.terminals), check)
        q, r, prime = blocks - 1, self.nullity, self.prime
        if r > q:
            check()
            return 0
        size = r + q
        matrix = []
        for _ in range(size):
            check()
            row = []
            for _ in range(size):
                check()
                row.append(0)
            matrix.append(row)
        for i in range(r):
            check()
            for terminal, block in enumerate(labels):
                check()
                if block:
                    j = r + block - 1
                    matrix[i][j] = (matrix[i][j] + self.coupling[i][terminal]) % prime
                    matrix[j][i] = matrix[i][j]
        for left, left_block in enumerate(labels):
            check()
            if not left_block:
                continue
            i = r + left_block - 1
            for right, right_block in enumerate(labels):
                check()
                if right_block:
                    j = r + right_block - 1
                    matrix[i][j] = (matrix[i][j] + self.response[left][right]) % prime
        value = self.factor * _determinant(matrix, prime, check) % prime
        check()
        return value
