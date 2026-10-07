"""Exact outward dyadic arithmetic for the local Fredholm certificates.

The verifier uses only Python's standard library.  The optional function
``propose_inverse`` imports mpmath to generate candidate point matrices.  No
mpmath result is trusted: ``inverse_bound`` verifies every candidate by an
outward-rounded integer residual.  Bundled proposals make regeneration optional.
"""
from collections import defaultdict
from fractions import Fraction
import hashlib
import json

P = 220
S = 1 << P
A = (1, 0)
E = (0, 2)


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def ceiling_div(a, b):
    require(b > 0, 'nonpositive integer division denominator')
    return -((-a) // b)


def decimal_endpoint(integer, upper=False, places=20):
    """A finite decimal rounded outward, for display only."""
    scale = 10**places
    numerator = integer * scale
    value = ceiling_div(numerator, S) if upper else numerator // S
    sign = '-' if value < 0 else ''
    value = abs(value)
    return sign + str(value // scale) + '.' + str(value % scale).zfill(places)


class IV:
    __slots__ = ('lo', 'hi')

    def __init__(self, x=0, hi=None, raw=False):
        if raw:
            require(type(x) is int and (hi is None or type(hi) is int),
                    'dyadic endpoints must be integers')
            self.lo, self.hi = x, x if hi is None else hi
        elif isinstance(x, IV):
            self.lo, self.hi = x.lo, x.hi
        else:
            require(not isinstance(x, float), 'binary float forbidden as interval input')
            f = Fraction(x)
            self.lo = f.numerator * S // f.denominator
            self.hi = ceiling_div(f.numerator * S, f.denominator)
        require(self.lo <= self.hi, 'reversed interval endpoints')

    def __add__(self, other):
        other = IV(other)
        return IV(self.lo + other.lo, self.hi + other.hi, True)

    __radd__ = __add__

    def __neg__(self):
        return IV(-self.hi, -self.lo, True)

    def __sub__(self, other):
        return self + -IV(other)

    def __rsub__(self, other):
        return IV(other) + -self

    def __mul__(self, other):
        other = IV(other)
        products = [a*b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return IV(min(products)//S, ceiling_div(max(products), S), True)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = IV(other)
        require(not other.lo <= 0 <= other.hi, 'interval division crosses zero')
        if other.hi < 0:
            return (-self) / (-other)
        floors = [a*S//b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        ceilings = [ceiling_div(a*S, b) for a in (self.lo, self.hi)
                    for b in (other.lo, other.hi)]
        return IV(min(floors), max(ceilings), True)

    def __rtruediv__(self, other):
        return IV(other) / self

    def __pow__(self, exponent):
        require(type(exponent) is int, 'interval exponent must be an integer')
        if exponent < 0:
            return IV(1)/(self**(-exponent))
        value, base = IV(1), self
        while exponent:
            if exponent & 1:
                value = value*base
            base = base*base
            exponent //= 2
        return value

    def abshi(self):
        return IV(max(abs(self.lo), abs(self.hi)), raw=True)

    def certificate(self):
        return {'lo': str(self.lo), 'hi': str(self.hi), 'scale_bits': P,
                'outward_decimal': [decimal_endpoint(self.lo),
                                    decimal_endpoint(self.hi, upper=True)]}


def edges(u):
    x, y = u
    result = [((x + 1, y), 2*x + y - 1)]
    if x:
        result.append(((x - 1, y + 1), x + y - 1))
    if y and u != (0, 1):
        result.append(((x, y - 1), x + 2*y - 1))
    require(all(e >= 0 for _, e in result), 'negative gauged exponent')
    return result


def fold(u):
    current = {(u, 0): 1}
    for _ in range(3):
        nxt = defaultdict(int)
        for (v, exponent), multiplicity in current.items():
            for w, cost in edges(v):
                nxt[w, exponent + cost] += multiplicity
        current = nxt
    return current


def row(u, kind='L'):
    require(kind in ('K', 'L'), 'unknown operator kind')
    result = fold(u)
    if kind == 'L':
        if u == E:
            for (v, e), coefficient in fold(A).items():
                result[v, e + 3] -= coefficient
        result = {(v, e): coefficient for (v, e), coefficient in result.items()
                  if v != A and coefficient}
    return result


def states(height, kind='L'):
    require(kind in ('K', 'L'), 'unknown operator kind')
    return [(x, h - x) for h in range(1, height + 1) for x in range(h + 1)
            if (2*h - x) % 3 == 1 and (kind != 'L' or (x, h - x) != A)]


def matrix(height, z, kind='L'):
    vs = states(height, kind)
    index = {v: j for j, v in enumerate(vs)}
    result = [[IV(int(i == j)) for j in range(len(vs))] for i in range(len(vs))]
    powers = [z**e for e in range(9*height + 20)]
    for i, u in enumerate(vs):
        for (v, e), coefficient in row(u, kind).items():
            if v in index:
                result[i][index[v]] -= coefficient*powers[e]
    return vs, result


def tail_bounds(height, r, kind='L'):
    require(r.lo > 0 and r.hi < S, 'tail radius must be in (0,1)')
    b, c, t = IV(0), IV(0), IV(0)
    powers = [r**e for e in range(9*(height + 20) + 20)]
    for u in states(height + 16, kind):
        inside, outside = IV(0), IV(0)
        for (v, e), coefficient in row(u, kind).items():
            if sum(v) <= height:
                inside += abs(coefficient)*powers[e]
            else:
                outside += abs(coefficient)*powers[e]
        if sum(u) <= height:
            b = IV(max(b.hi, outside.hi), raw=True)
        else:
            c = IV(max(c.hi, inside.hi), raw=True)
            t = IV(max(t.hi, outside.hi), raw=True)
        if sum(u) > height + 3:
            require(inside.hi == 0, 'far tail row unexpectedly reaches core')
    # Heights h>=height+17: <=27 paths, exponent >=3h-6.
    remainder = 27*r**(3*(height + 17) - 6)
    t = IV(max(t.hi, remainder.hi), raw=True)
    require(t.hi < S, 'tail row norm is not a contraction')
    return b, c, t, b*c/(1-t)


def determinant(matrix_):
    work = [r[:] for r in matrix_]
    n, value = len(work), IV(1)
    require(all(len(r) == n for r in work), 'nonsquare interval matrix')
    for j in range(n):
        # Pivot choice is exact. It is only a heuristic; sign checks are rigorous.
        i = max(range(j, n), key=lambda i: abs(work[i][j].lo + work[i][j].hi))
        if i != j:
            work[i], work[j] = work[j], work[i]
            value = -value
        pivot = work[j][j]
        require(not pivot.lo <= 0 <= pivot.hi, 'uncertain determinant pivot')
        value *= pivot
        for k in range(j + 1, n):
            if work[k][j].lo == work[k][j].hi == 0:
                continue
            factor = work[k][j]/pivot
            for l in range(j + 1, n):
                work[k][l] -= factor*work[j][l]
            work[k][j] = IV(0)
    return value


def matrix_fingerprint(matrix_):
    payload = [[[str(a.lo), str(a.hi)] for a in row_] for row_ in matrix_]
    return hashlib.sha256(json.dumps(payload, separators=(',', ':')).encode()).hexdigest()


def point_matrix(data, matrix_):
    n = len(matrix_)
    require(data['matrix_sha256'] == matrix_fingerprint(matrix_),
            'inverse proposal bound to different interval matrix')
    require(data['scale_bits'] == P, 'inverse proposal has wrong precision')
    rows = data['dyadic_point_matrix']
    require(len(rows) == n and all(len(r) == n for r in rows),
            'inverse proposal has wrong dimensions')
    require(all(type(a) is str for r in rows for a in r), 'invalid inverse proposal encoding')
    return [[IV(int(a), raw=True) for a in r] for r in rows]


def inverse_bound(matrix_, proposal):
    """Certify kappa via ||I-B*A||<1, for exact dyadic candidate B."""
    n = len(matrix_)
    b = point_matrix(proposal, matrix_)
    norm_b = IV(max(sum(x.abshi().hi for x in r) for r in b), raw=True)
    columns = [[(k, matrix_[k][j]) for k in range(n)
                if matrix_[k][j].lo or matrix_[k][j].hi] for j in range(n)]
    maximum = 0
    for i in range(n):
        row_sum = 0
        for j in range(n):
            residual = IV(int(i == j))
            for k, a in columns[j]:
                residual -= b[i][k]*a
            row_sum += residual.abshi().hi
        maximum = max(maximum, row_sum)
    epsilon = IV(maximum, raw=True)
    require(epsilon.hi < S, 'inverse residual is not below one')
    return norm_b/(1-epsilon), epsilon, b


def norm(vector):
    return IV(max(x.abshi().hi for x in vector), raw=True)


def solve(matrix_, rhs, kappa, inverse_point):
    """Build an exact point proposal from B and verify its full residual."""
    n = len(matrix_)
    # Midpoint rhs has denominator 2*S; divide the exact product by 2*S.
    x = [IV(sum(inverse_point[i][j].lo*(rhs[j].lo + rhs[j].hi)
                for j in range(n))//(2*S), raw=True) for i in range(n)]
    residuals = []
    for i in range(n):
        residual = rhs[i]
        for j in range(n):
            if matrix_[i][j].lo or matrix_[i][j].hi:
                residual -= matrix_[i][j]*x[j]
        residuals.append(residual)
    error = kappa*norm(residuals)
    return [IV(v.lo-error.hi, v.hi+error.hi, True) for v in x], error


def propose_inverse(matrix_):
    """Optional candidate generation. mpmath is never an acceptance oracle."""
    import mpmath as mp
    mp.mp.dps = 80
    n = len(matrix_)
    midpoint = mp.matrix([[mp.mpf(a.lo+a.hi)/(2*S) for a in r] for r in matrix_])
    inverse = midpoint**-1
    data = {'matrix_sha256': matrix_fingerprint(matrix_), 'scale_bits': P,
            'dyadic_point_matrix': [[str(int(mp.nint(inverse[i, j]*S)))
                                    for j in range(n)] for i in range(n)]}
    inverse_bound(matrix_, data)
    return data
