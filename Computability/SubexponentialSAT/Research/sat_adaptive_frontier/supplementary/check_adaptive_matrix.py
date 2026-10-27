#!/usr/bin/env python3
"""Exact finite checks and rational interval certificates for adaptive MM.

No floating-point value is used in a mathematical assertion.  The script
checks the new covariance identities, the triangle algorithm on finite
fixtures, paid table cardinalities, and the displayed asymptotic constants.
It is not an implementation of the upstream SAT contraction engine.
"""
from fractions import Fraction as F
from itertools import combinations
from math import factorial, isqrt
from pathlib import Path
import json
import random


def require(ok, message):
    if not ok:
        raise ArithmeticError(message)


def partitions(r):
    k = r // 3
    vertices = tuple(range(r))
    # Labelled partitions: necessary for an unbiased covariance average.
    for a in combinations(vertices, k):
        aset = set(a)
        rest = tuple(v for v in vertices if v not in aset)
        for b in combinations(rest, k):
            bset = set(b)
            c = tuple(v for v in rest if v not in bset)
            colors = [0] * r
            for v in b:
                colors[v] = 1
            for v in c:
                colors[v] = 2
            yield tuple(colors)


def class_of(edge, colors):
    a, b = sorted((colors[edge[0]], colors[edge[1]]))
    return {(0, 1): 0, (0, 2): 1, (1, 2): 2}.get((a, b), -1)


def covariance_check(r):
    k = r // 3
    edges = list(combinations(range(r), 2))
    rows = [[class_of(e, p) for e in edges] for p in partitions(r)]
    n = len(rows)
    require(n == factorial(r) // factorial(k) ** 3, "partition count")
    coeff = [F(4*k*k, r*(r-1)),
             F(2*k*k*(k-2), r*(r-1)*(r-2)),
             -F(8*k*k*(k-1), r*(r-1)*(r-2)*(r-3))]
    e0 = edges.index((0, 1))
    representatives = [e0, edges.index((0, 2)), edges.index((2, 3))]
    def y(cls):
        return int(cls == 0) - int(cls == 1)
    for idx, want in zip(representatives, coeff):
        got = F(sum(y(row[e0])*y(row[idx]) for row in rows), n)
        require(got == want, f"r{r} covariance mismatch")
    c0, c1, c2 = coeff
    lam = F(2*k**3, (r-1)*(r-2))
    require(c0 + (r-4)*c1 - (r-3)*c2 == lam, "lambda formula")
    require(c1 >= c2, "incidence coefficient sign")
    require(c0 + 2*(r-2)*c1 + F((r-2)*(r-3), 2)*c2 == 0,
            "constant vector not annihilated")
    beta2 = F(8*k*(8*k-5), 25*(3*k-1)*(3*k-2))
    avec = F(4, 5)*F(2*k, r-1)
    require((avec*avec*r*(r-1)+F(12,25)*lam)/(r*r) == beta2,
            "adaptive coefficient simplification")
    rng = random.Random(6719 + r)
    fixtures = [[1]*len(edges), [int(0 in e) for e in edges],
                [int(e[0] < k and e[1] < k) for e in edges]]
    fixtures += [[int(j == i) for j in range(len(edges))]
                 for i in representatives]
    fixtures += [[rng.randrange(17) for _ in edges] for _ in range(30)]
    for x in fixtures:
        total = sum(x)
        norm2 = sum(a*a for a in x)
        ev_sum = F(0)
        y2_sum = 0
        best = None
        for row in rows:
            h = [0, 0, 0]
            for w, cls in zip(x, row):
                if cls >= 0:
                    h[cls] += w
            s = sum(h)
            ev_sum += sum(a*a for a in h) - F(s*s, 3)
            y2_sum += (h[0]-h[1])**2
            cost = s - F(3, 5)*min(h)
            best = cost if best is None else min(best, cost)
        ev = ev_sum / n
        require(ev == F(y2_sum, n), "variance-class symmetry")
        m = len(edges)
        require(ev <= lam*(norm2 - F(total*total, m)),
                "covariance quadratic bound")
        # Interpret x as symmetric directed weights x/2: ||h||²=||x||²/2.
        require(best*best <= F(r*r, 2)*beta2*norm2,
                "adaptive triangle upper bound")
    return {"r": r, "labelled_partitions": n,
            "unlabelled_partitions": n//6, "fixtures": len(fixtures),
            "covariances": [str(a) for a in coeff],
            "lambda": str(lam), "triangle_beta_squared": str(beta2)}


def merger(r, k):
    if k <= 1:
        return F(0)
    a, b = k//2, k-k//2
    classes = [2*a*(r-k), 2*a*b, 2*b*(r-k)]
    cost = sum(classes) - F(21,25)*min(classes)
    return max(cost, merger(r, a), merger(r, b))


class Interval:
    """Closed intervals with Fraction endpoints and outward sqrt rounding."""
    def __init__(self, lo, hi=None):
        self.lo = F(lo)
        self.hi = F(lo if hi is None else hi)
        require(self.lo <= self.hi, "reversed interval")
    def __add__(self, other):
        other = interval(other)
        return Interval(self.lo+other.lo, self.hi+other.hi)
    __radd__ = __add__
    def __neg__(self):
        return Interval(-self.hi, -self.lo)
    def __sub__(self, other):
        return self + -interval(other)
    def __rsub__(self, other):
        return interval(other) + -self
    def __mul__(self, other):
        other = interval(other)
        vals = [a*b for a in (self.lo,self.hi)
                for b in (other.lo,other.hi)]
        return Interval(min(vals),max(vals))
    __rmul__ = __mul__
    def __truediv__(self, other):
        other = interval(other)
        require(not (other.lo <= 0 <= other.hi), "interval division by zero")
        return self * Interval(1/other.hi,1/other.lo)
    def __rtruediv__(self, other):
        return interval(other) / self
    def sqrt(self):
        require(self.lo >= 0, "negative sqrt")
        q = 10**65
        low = isqrt(self.lo.numerator*q*q//self.lo.denominator)
        high = isqrt(self.hi.numerator*q*q//self.hi.denominator)+1
        return Interval(F(low,q),F(high,q))
    def decimal_bounds(self, digits=15):
        q = 10**digits
        low = self.lo.numerator*q//self.lo.denominator
        high = -((-self.hi.numerator*q)//self.hi.denominator)
        def show(n):
            return f"{n//q}.{n%q:0{digits}d}"
        return [show(low),show(high)]


def interval(x):
    return x if isinstance(x, Interval) else Interval(x)


def arctan_interval(inv, terms=120):
    x = F(1,inv)
    total = sum(((-1)**j)*x**(2*j+1)/F(2*j+1) for j in range(terms))
    next_term = ((-1)**terms)*x**(2*terms+1)/F(2*terms+1)
    return Interval(min(total,total+next_term),max(total,total+next_term))


def log_from_atanh(x, terms=150):
    x = F(x)
    total = 2*sum(x**(2*j+1)/F(2*j+1) for j in range(terms))
    remainder = 2*x**(2*terms+1)/(F(2*terms+1)*(1-x*x))
    return Interval(total,total+remainder)


def constants_check():
    pi = 16*arctan_interval(5)-4*arctan_interval(239)
    ln2 = log_from_atanh(F(1,3))
    ln3 = log_from_atanh(F(1,2))
    log9 = 2*ln3/ln2
    kap = pi*interval(2).sqrt()/ln2
    A = 1/(20*log9)
    W = F(5,6)*(F(1,36)-A)
    K0 = kap/A.sqrt()
    K1 = 2*kap/(9*W.sqrt())
    a9,b9,j9 = F(4,9),2*interval(229).sqrt()/45,F(2,3)
    a12,b12,j12 = interval(22).sqrt()/12,interval(102).sqrt()/15,F(2,3)
    gamma = 1/interval(6).sqrt()
    require((a12/(1-gamma)).hi < b12.lo, "tail inner maximum")
    root = b9*K0
    tail = a9*K0+b12*K1
    require(tail.hi < root.lo, "root is not dominant")
    space0,space1 = j9*K0,j12*K1
    require(space1.hi < space0.lo, "space maximum")
    require(root.hi < F(34326,1000), "eventual time ceiling")
    require(space0.hi < F(34025,1000), "eventual space ceiling")
    oldtime = pi*interval(24339).sqrt()/(20*ln2)
    oldspace = pi*interval(915).sqrt()/(4*ln2)
    require(root.hi < oldtime.lo and space0.hi < oldspace.lo,
            "incoming certificate comparison")
    require(12**100 < 2**359, "tail degree exponent gate")
    require(6**3 < 5**4, "positive depth exponent")
    require(F(9,10)+F(359,100)/36 == 1-F(1,3600),
            "rational margin arithmetic")
    return {name:value.decimal_bounds() for name,value in
            [("time_root",root),("time_tail",tail),("space_root",space0),
             ("space_tail",space1),("incoming_time",oldtime),
             ("incoming_space",oldspace),("A",A),("W",W)]}


def main():
    matrix = {}
    for r in (9,12):
        k = r//3
        numerator = merger(r,k)
        require(numerator == {9:F(916,25),12:F(1632,25)}[r],
                "binary merge ledger")
        beta2 = F(8*k*(8*k-5),25*(3*k-1)*(3*k-2))
        require(beta2 < numerator/(r*r), "triangle does not fit merge budget")
        matrix[str(r)] = {"merge_squared_numerator":str(numerator),
                          "merge_beta_squared":str(numerator/(r*r)),
                          "max_boundary":2*k*(r-k)}
    output = {"status":"passed", "covariance":[covariance_check(6),covariance_check(9)],
              "matrix_ledger":matrix, "interval_certificates":constants_check(),
              "limitations":["No complete SAT engine is implemented.",
                              "Finite checks supplement the all-size proofs.",
                              "Fast matrix multiplication backend is imported, not implemented."]}
    out = Path(__file__).with_name('adaptive_matrix_checks.json')
    out.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output,indent=2))

if __name__ == '__main__':
    main()
