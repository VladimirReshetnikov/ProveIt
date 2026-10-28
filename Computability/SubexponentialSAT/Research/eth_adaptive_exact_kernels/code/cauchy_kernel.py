"""Independent modular full-orientation Cauchy feature-table algorithms.

All arithmetic is in (Z/2**p Z)[U]/(U**2+U+1), the degree-two
unramified extension.  The product algorithm is a literal implementation
of the mathematical product formula, not imported archive code.  Both
algorithms share identical initialization, batch unit inversion, precision,
and full dense output.  This is a local component, not a SAT solver.
"""
from dataclasses import dataclass


def valuation(n):
    if n == 0:
        return None
    n = abs(n)
    return (n & -n).bit_length() - 1


def split_integer(n):
    v = valuation(n)
    if v is None:
        raise ValueError("zero has no unit part")
    return v, n >> v


def split_pair(x):
    values = [valuation(c) for c in x if c]
    if not values:
        raise ValueError("zero has no unit part")
    v = min(values)
    return v, (x[0] >> v, x[1] >> v)


class Ring:
    def __init__(self, precision):
        if precision < 1:
            raise ValueError("positive precision required")
        self.p = precision
        self.mod = 1 << precision
        self.multiplications = 0
        self.inversions = 0

    def reduce(self, x):
        return (x[0] % self.mod, x[1] % self.mod)

    def add(self, x, y):
        return ((x[0] + y[0]) % self.mod, (x[1] + y[1]) % self.mod)

    def mul(self, x, y):
        self.multiplications += 1
        a, b = x
        c, d = y
        return ((a*c - b*d) % self.mod, (a*d + b*c - b*d) % self.mod)

    def inverse(self, x):
        self.inversions += 1
        a, b = x
        norm = (a*a - a*b + b*b) % self.mod
        if not norm & 1:
            raise ValueError("inverse requires an extension-ring unit")
        inv = pow(norm, -1, self.mod)
        return ((a-b)*inv % self.mod, -b*inv % self.mod)

    def scale_two(self, x, v):
        if v < 0:
            raise ArithmeticError("attempted nonintegral output")
        if v >= self.p:
            return (0, 0)
        return ((x[0] << v) % self.mod, (x[1] << v) % self.mod)

    def batch_inverse(self, values):
        if not values:
            return []
        prefix = [(1, 0)]
        for x in values:
            prefix.append(self.mul(prefix[-1], x))
        suffix_inverse = self.inverse(prefix[-1])
        result = [None] * len(values)
        for j in range(len(values)-1, -1, -1):
            result[j] = self.mul(suffix_inverse, prefix[j])
            suffix_inverse = self.mul(suffix_inverse, values[j])
        return result


@dataclass(frozen=True)
class Parameters:
    a: int
    i: int
    t: int
    zeta: tuple = (0, 1)
    precision: int = 32

    def validate(self):
        if self.a < 1 or not 0 <= self.i < self.a:
            raise ValueError("require a >= 1 and 0 <= i < a")
        if not -(1 << self.a) <= self.t < (1 << self.a):
            raise ValueError("t outside interpolation grid")
        if valuation(self.t) != self.i:
            raise ValueError("wrong valuation of t")
        if len(self.zeta) != 2 or not all(isinstance(c, int) for c in self.zeta):
            raise ValueError("zeta must have two integer coordinates")
        if self.precision < 1:
            raise ValueError("positive precision required")


class Prepared:
    def __init__(self, params):
        params.validate()
        self.params = params
        self.ring = Ring(params.precision)
        self.L = 1 << params.a
        self.R = 1 << params.i
        self.N = self.L // 2
        self.slots = [j % self.R + 2*self.R*(j // self.R) for j in range(self.N)]
        self.E = [2*(b // self.R) - (b // self.R).bit_count() for b in range(self.N)]
        self.T = (params.t + 2*self.L*params.zeta[0], 2*self.L*params.zeta[1])
        self.tv, self.tunit = split_pair(self.T)

        # This is precisely the set of possible slot differences, generated
        # in O(L), not by an N-by-N difference table.
        blocks = self.N // self.R
        differences = [2*self.R*q + r
                       for q in range(1-blocks, blocks)
                       for r in range(1-self.R, self.R)]
        split = {d: split_pair((self.T[0] + d, self.T[1])) for d in differences}
        inverses = self.ring.batch_inverse([split[d][1] for d in differences])
        self.denominators = {d: (split[d][0], inv) for d, inv in zip(differences, inverses)}
        self.prefactor = self._prefactor()
        self.initial_multiplications = self.ring.multiplications
        self.initial_inversions = self.ring.inversions

    def _prefactor(self):
        # Gamma(T)/T = product_{q != 0}(T-q) / product_{q != 0}(-q).
        # This directly cancels the q=0 factor before any modular arithmetic.
        power = 0
        numerator = (1, 0)
        denominator = (1, 0)
        for q in range(-self.L, self.L):
            if not q:
                continue
            term = (self.T[0]-q, self.T[1])
            if term == (0, 0):
                return (0, 0)
            nv, nu = split_pair(term)
            dv, du = split_integer(-q)
            power += nv-dv
            numerator = self.ring.mul(numerator, nu)
            denominator = self.ring.mul(denominator, (du, 0))
        result = self.ring.mul(numerator, self.ring.inverse(denominator))
        return self.ring.scale_two(result, power)

    def emit(self, out, side, b, j, power, unit):
        normalized = self.ring.scale_two(unit, power-self.E[b])
        if side == 0:
            # A_b = (Gamma/T) 2**(2E_b) F_b.
            out[b][j] = self.ring.mul(self.prefactor,
                                     self.ring.scale_two(normalized, 2*self.E[b]))
        else:
            out[b][j] = normalized

    def result(self, target, source, algorithm):
        n = self.N
        return {"target": target, "source": source, "counts": {
            "algorithm": algorithm, "N": n, "L": self.L,
            "stored_ring_elements": 2*n*n,
            "emitted_supported_entries": n*(n+1),
            "unit_denominators": len(self.denominators),
            "ring_multiplications": self.ring.multiplications,
            "unit_inversions": self.ring.inversions,
            "initialization_multiplications": self.initial_multiplications,
            "initialization_inversions": self.initial_inversions,
        }}


def product_tables(params):
    """Fresh product for each feature; shared denominator cache and output."""
    k = Prepared(params)
    n = k.N
    tables = [[[ (0, 0) for _ in range(n)] for _ in range(n)] for _ in range(2)]
    for side in (0, 1):
        for b in range(n):
            pivot = k.slots[b]
            for j in range(b, n):
                x = k.slots[j]
                d = x-pivot if side == 0 else pivot-x
                dv, inv = k.denominators[d]
                power = k.tv-dv
                unit = k.ring.mul(k.tunit, inv)
                for h in range(b):
                    difference = x-k.slots[h] if side == 0 else k.slots[h]-x
                    nv, nu = split_integer(difference)
                    dv, inv = k.denominators[difference]
                    power += nv-dv
                    unit = k.ring.mul(k.ring.mul(unit, (nu, 0)), inv)
                k.emit(tables[side], side, b, j, power, unit)
    return k.result(*tables, "independent product formula")


def recurrent_tables(params):
    """Columnwise consecutive-pivot recurrence, tracking valuation separately."""
    k = Prepared(params)
    n = k.N
    tables = [[[ (0, 0) for _ in range(n)] for _ in range(n)] for _ in range(2)]
    for side in (0, 1):
        for j in range(n):
            x = k.slots[j]
            d = x-k.slots[0] if side == 0 else k.slots[0]-x
            dv, inv = k.denominators[d]
            power = k.tv-dv
            unit = k.ring.mul(k.tunit, inv)
            k.emit(tables[side], side, 0, j, power, unit)
            for b in range(j):
                numerator = x-k.slots[b] if side == 0 else k.slots[b]-x
                difference = x-k.slots[b+1] if side == 0 else k.slots[b+1]-x
                nv, nu = split_integer(numerator)
                dv, inv = k.denominators[difference]
                power += nv-dv
                unit = k.ring.mul(k.ring.mul(unit, (nu, 0)), inv)
                k.emit(tables[side], side, b+1, j, power, unit)
    return k.result(*tables, "consecutive-pivot recurrence")


def expected_multiplications(params, initialization, algorithm):
    """Exact count for this implementation, including target output scaling."""
    n = 1 << (params.a-1)
    targets = n*(n+1)//2
    if algorithm == "product":
        # 2 sides: one initial multiply and 2b product multiplies per entry.
        kernel = n*(n+1)*(2*n+1)//3
    elif algorithm == "recurrent":
        # Two initial multiplies per column; 4 per predecessor step.
        kernel = 2*n*n
    else:
        raise ValueError("unknown algorithm")
    return initialization + kernel + targets
