"""New ratio-fused quadratic Cauchy tables versus matched one-inverse baseline.

This self-authored implementation does not import any reviewed archive code.
The baseline reproduces the late packet's mathematical one-inversion,
two-products-per-transition algorithm. The fused algorithm additionally
caches transition unit ratios and absorbs the common target prefactor once.
"""
from cauchy_kernel import Ring as BasicRing, Parameters, split_pair, split_integer

class MaskRing(BasicRing):
    """Shared power-of-two mask backend for both matched algorithms.

    For every integer x, x % 2**p equals x & (2**p-1), including x<0.
    This backend refinement is inherited practice, not a novelty claim.
    """
    def __init__(self, precision):
        super().__init__(precision)
        self.mask=self.mod-1

    def reduce(self,x):
        return x[0]&self.mask,x[1]&self.mask

    def add(self,x,y):
        return (x[0]+y[0])&self.mask,(x[1]+y[1])&self.mask

    def mul(self,x,y):
        self.multiplications+=1
        a,b=x;c,d=y
        return (a*c-b*d)&self.mask,(a*d+b*c-b*d)&self.mask

    def inverse(self,x):
        self.inversions+=1
        a,b=x;norm=(a*a-a*b+b*b)&self.mask
        if not norm&1:raise ValueError('inverse requires an extension-ring unit')
        v=pow(norm,-1,self.mod)
        return ((a-b)*v)&self.mask,(-b*v)&self.mask

    def scale_two(self,x,v):
        if v<0:raise ArithmeticError('attempted nonintegral output')
        if v>=self.p:return 0,0
        return (x[0]<<v)&self.mask,(x[1]<<v)&self.mask


class Prepared:
    def __init__(self, params):
        params.validate()
        self.params = params
        self.ring = MaskRing(params.precision)
        self.L, self.R, self.N = 1 << params.a, 1 << params.i, 1 << (params.a-1)
        self.slots = [j % self.R + 2*self.R*(j//self.R) for j in range(self.N)]
        self.E = [2*(b//self.R)-(b//self.R).bit_count() for b in range(self.N)]
        self.T = (params.t+2*self.L*params.zeta[0], 2*self.L*params.zeta[1])
        self.tv, self.tunit = split_pair(self.T)
        blocks = self.N//self.R
        self.differences = [2*self.R*q+r for q in range(1-blocks, blocks)
                            for r in range(1-self.R, self.R)]
        split = {d: split_pair((self.T[0]+d, self.T[1])) for d in self.differences}
        # Compute the prefactor's scalar denominator before batch inversion,
        # so the baseline also uses only one inversion, like the late packet.
        pref_v, pref_num, pref_den, zero = 0, (1, 0), 1, False
        for q in range(-self.L, self.L):
            if not q:
                continue
            numerator = (self.T[0]-q, self.T[1])
            if numerator == (0, 0):
                zero = True
            else:
                nv, nu = split_pair(numerator)
                pref_v += nv
                pref_num = self.ring.mul(pref_num, nu)
            dv, du = split_integer(-q)
            pref_v -= dv
            pref_den = (pref_den*du) & self.ring.mask
        values = [split[d][1] for d in self.differences]+[(pref_den, 0)]
        inverses = self.ring.batch_inverse(values)
        self.denominators = {d: (split[d][0], inv) for d, inv in zip(self.differences, inverses)}
        self.pref_unit = self.ring.mul(pref_num, inverses[-1])
        self.pref_v = pref_v
        if zero:
            self.pref_unit, self.pref_v = (0, 0), params.precision
        elif self.pref_v < params.a+1-params.i:
            raise ArithmeticError("prefactor valuation failed")
        self.common_preparation_mults = self.ring.multiplications

    def result(self, target, source, table_start, algorithm, ratio_entries=0):
        return {"target": target, "source": source, "counts": {
            "algorithm": algorithm, "N": self.N, "L": self.L,
            "precision": self.params.precision,
            "unit_inversions": self.ring.inversions,
            "unique_denominators": len(self.differences),
            "ratio_cache_entries": ratio_entries,
            "common_preparation_multiplications": self.common_preparation_mults,
            "preparation_multiplications": table_start,
            "table_multiplications": self.ring.multiplications-table_start,
            "total_multiplications": self.ring.multiplications,
        }}


def baseline_tables(params):
    """One inverse, two multiplications per transition, one per target output."""
    k = Prepared(params)
    n, ring = k.N, k.ring
    target = [[(0, 0)]*n for _ in range(n)]
    source = [[(0, 0)]*n for _ in range(n)]
    table_start = ring.multiplications
    for j in range(n):
        x = k.slots[j]
        for sign, table in ((1, target), (-1, source)):
            dv, inv = k.denominators[sign*x]
            power, unit = k.tv-dv, ring.mul(k.tunit, inv)
            for b in range(j+1):
                if sign == 1:
                    table[b][j] = ring.scale_two(ring.mul(k.pref_unit, unit),
                                                  k.pref_v+power+k.E[b])
                else:
                    table[b][j] = ring.scale_two(unit, power-k.E[b])
                if b < j:
                    numerator = sign*(x-k.slots[b])
                    difference = sign*(x-k.slots[b+1])
                    nv, nu = split_integer(numerator)
                    dv, inv = k.denominators[difference]
                    power += nv-dv
                    unit = ring.mul(ring.mul(unit, (nu, 0)), inv)
    if ring.multiplications-table_start != (5*n*n+n)//2:
        raise ArithmeticError("baseline operation count failed")
    return k.result(target, source, table_start, "matched one-inversion quadratic baseline")


def fused_tables(params):
    """One cached ratio product per transition; target prefactor paid once."""
    k = Prepared(params)
    n, ring = k.N, k.ring
    # Consecutive missing-bit slot gaps are 1 or R+1. For R=1 only 2 occurs.
    gaps = (2,) if k.R == 1 else (1, k.R+1)
    ratios = {}
    for d in k.differences:
        if d < 0:
            continue
        for gap in gaps:
            # Target: denominator T+d, numerator d+gap.
            # Source: denominator T-d, numerator -d-gap.
            nv, nu = split_integer(d+gap)
            dv, inv = k.denominators[d]
            ratios[(d, gap, 1)] = (nv-dv, ring.mul((nu, 0), inv))
            dv, inv = k.denominators[-d]
            ratios[(d, gap, -1)] = (nv-dv, ring.mul((-nu, 0), inv))
    target_seed = ring.mul(k.pref_unit, k.tunit)
    target = [[(0, 0)]*n for _ in range(n)]
    source = [[(0, 0)]*n for _ in range(n)]
    table_start = ring.multiplications
    for j in range(n):
        x = k.slots[j]
        for sign, table in ((1, target), (-1, source)):
            dv, inv = k.denominators[sign*x]
            power = k.tv-dv
            unit = ring.mul(target_seed if sign == 1 else k.tunit, inv)
            for b in range(j+1):
                if sign == 1:
                    table[b][j] = ring.scale_two(unit, k.pref_v+power+k.E[b])
                else:
                    table[b][j] = ring.scale_two(unit, power-k.E[b])
                if b < j:
                    gap = k.slots[b+1]-k.slots[b]
                    difference = x-k.slots[b+1]
                    increment, ratio = ratios[(difference, gap, sign)]
                    power += increment
                    unit = ring.mul(unit, ratio)
    if ring.multiplications-table_start != n*n+n:
        raise ArithmeticError("fused operation count failed")
    return k.result(target, source, table_start, "ratio-fused recurrence", len(ratios))
