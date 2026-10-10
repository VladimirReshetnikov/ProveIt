"""Exact rational proximity enclosures for frozen Gaussian candidates.

Python integers and fractions.Fraction are used throughout the certificate.
No decimal approximation is a premise.  A zero-containing residual interval
is a proximity result, never a proof of the proposed identity.

The analytic bound is proved in s6_notes.tex: for the N-term Euler transform
of f_n=H_{2n}^{(b)}/(2n+1)^a, the omitted tail lies between
-(N+1)*H_2^{(b)}/(3^a*2^N) and zero.  For S_p, replace H_2^{(b)} by 1.
This is the manuscript's direct one-sided Euler bound, rederived here.
"""
from __future__ import annotations
from fractions import Fraction as Q
from math import gcd, lcm
from pathlib import Path
from functools import reduce
import argparse
import json
import sys
import time

sys.set_int_max_str_digits(1000000)
BASE = Path(__file__).resolve().parent


class Interval:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        self.lo = Q(lo)
        self.hi = Q(lo if hi is None else hi)
        if self.lo > self.hi:
            raise ValueError("Reversed interval")

    def __add__(self, other):
        if not isinstance(other, Interval):
            other = Interval(other)
        return Interval(self.lo+other.lo, self.hi+other.hi)

    __radd__ = __add__

    def __mul__(self, other):
        if not isinstance(other, Interval):
            other = Interval(other)
        corners = [x*y for x in (self.lo, self.hi)
                   for y in (other.lo, other.hi)]
        return Interval(min(corners), max(corners))

    __rmul__ = __mul__

    def __pow__(self, n):
        if n < 0 or self.lo < 0:
            raise ValueError("Only nonnegative powers of positive intervals used")
        return Interval(self.lo**n, self.hi**n)

    def record(self):
        return {"lower": [str(self.lo.numerator), str(self.lo.denominator)],
                "upper": [str(self.hi.numerator), str(self.hi.denominator)]}


class ExactEuler:
    def __init__(self, N):
        self.N = N
        self.scale = 1 << N
        # Every denominator below divides D, including the largest 2N-1.
        self.D = lcm(*range(1, 2*N+1))
        self.weights = []
        tail = self.scale-1
        c = 1
        for n in range(N):
            self.weights.append((-1)**n*tail)
            c = c*(N-n)//(n+1)
            tail -= c
        assert tail == 0

    def gaussian(self, a, b):
        assert a >= 1 and b >= 1
        num = 0
        harmonic = 0
        for n, weight in enumerate(self.weights):
            if n:
                harmonic += (self.D//(2*n-1))**b+(self.D//(2*n))**b
            num += weight*harmonic*(self.D//(2*n+1))**a
        E = Q(num, self.scale*self.D**(a+b))
        bound = Q(self.N+1, self.scale*3**a)*(1+Q(1, 2**b))
        return Interval(E-bound, E)

    def mixed(self, p):
        assert p >= 1
        num = 0
        harmonic = 0
        for n, weight in enumerate(self.weights):
            if n:
                harmonic += self.D//n
            num += weight*harmonic*(self.D//(2*n+1))**p
        E = Q(num, self.scale*self.D**(p+1))
        return Interval(E-Q(self.N+1, self.scale*3**p), E)

    def single(self, s, odd):
        assert s >= 1
        num = sum(weight*(self.D//(2*n+1 if odd else n+1))**s
                  for n, weight in enumerate(self.weights))
        E = Q(num, self.scale*self.D**s)
        # The coefficients are Hausdorff moments with mass one.
        return Interval(E, E+Q(1, self.scale))

    def beta(self, s):
        return self.single(s, True)

    def zeta(self, s):
        assert s > 1
        return self.single(s, False)*Q(2**(s-1), 2**(s-1)-1)


def arctangent_inverse(q, terms):
    partial = sum((Q((-1)**n, (2*n+1)*q**(2*n+1))
                   for n in range(terms)), Q())
    next_term = Q(1, (2*terms+1)*q**(2*terms+1))
    if terms % 2:
        return Interval(partial-next_term, partial)
    return Interval(partial, partial+next_term)


def elementary_intervals():
    # Machin: pi=16 atan(1/5)-4 atan(1/239); power-series remainder.
    pi = 16*arctangent_inverse(5, 600)+(-4)*arctangent_inverse(239, 600)
    # log 2 = 2 atanh(1/3); replace the omitted denominators by their first.
    terms = 800
    partial = sum((Q(2, (2*n+1)*3**(2*n+1))
                   for n in range(terms)), Q())
    log2 = Interval(partial, partial+Q(9, 4*(2*terms+1)*3**(2*terms+1)))
    return pi, log2


def load_candidates():
    data = json.loads((BASE/"gaussian_candidates.json").read_text())
    return [{"p": r["p"], "basket": r["basket"], "vector": r["vector"]}
            for r in data["candidates"]]


def run(N, include_s12):
    start = time.monotonic()
    e = ExactEuler(N)
    pi, log2 = elementary_intervals()
    print("Exact Euler weights and elementary intervals ready", flush=True)
    results = []
    discarded = None
    betas = {}
    zetas = {}
    for rec in load_candidates():
        p = rec["p"]
        if p == 12 and not include_s12:
            continue
        vector = rec["vector"]
        assert vector[0] != 0 and reduce(gcd, vector) == 1
        vals = [e.mixed(p)]
        for a in range(p, 1, -2):
            vals.append(e.gaussian(a, p+1-a))
        vals.append(pi**(p+1))
        for j in range(1, p//2):
            if 2*j not in betas:
                betas[2*j] = e.beta(2*j)
            z = p+1-2*j
            if z not in zetas:
                zetas[z] = e.zeta(z)
            vals.append(betas[2*j]*zetas[z])
        if p not in betas:
            betas[p] = e.beta(p)
        vals.append(betas[p]*log2)
        assert len(vals) == len(vector) == len(rec["basket"])
        residual = sum((v*Q(c, vector[0])
                        for v, c in zip(vals, vector)), Interval(0))
        contains_zero = residual.lo <= 0 <= residual.hi
        certified_bound = Q(1, 10**650)
        inside_bound = -certified_bound < residual.lo and residual.hi < certified_bound
        rec.update({"status": "certified proximity; equality remains conjectural"
                   if contains_zero and inside_bound else "residual audit",
                   "normalization": "integer vector divided by its S_p coefficient",
                   "contains_zero": contains_zero,
                   "proved_absolute_bound": "10^-650" if inside_bound else None,
                   "normalized_residual": residual.record(),
                   "basket_intervals": [v.record() for v in vals]})
        results.append(rec)
        if p == 12:
            source = json.loads((BASE/"gaussian_candidates.json").read_text())
            old = source["discarded_candidates"][0]["vector"]
            bad = sum((v*c for v, c in zip(vals, old)), Interval(0))
            assert -Q(2191, 10**277) < bad.lo < bad.hi < -Q(2190, 10**277) < 0
            discarded = {"vector": old,
                         "normalization": "unnormalized integer dot product",
                         "rejected": True,
                         "proved_bracket": ["-2191/10^277", "-2190/10^277"],
                         "exact_residual": bad.record()}
        print(f"S{p}: contains zero={contains_zero}; strictly inside +/-1e-650={inside_bound}",
              flush=True)
    out = {"arithmetic": "exact Python int and fractions.Fraction only",
           "source_snapshot": "3447bc59b78d138a7f0d536b66ac6e5cc5d5e49f",
           "Euler_terms": N, "pi_arctangent_terms_each": 600,
           "log2_atanh_terms": 800,
           "meaning": "Finite proximity statements, not proofs of identities.",
           "results": results, "elapsed_seconds": round(time.monotonic()-start, 3)}
    if discarded is not None:
        out["discarded_S12_candidate"] = discarded
    path = BASE/"gaussian_proximity_certificate.json"
    path.write_text(json.dumps(out, indent=2)+"\n")
    print(f"Saved {path.name}; {out['elapsed_seconds']} seconds", flush=True)
    assert all(r["contains_zero"] and r["proved_absolute_bound"] for r in results)


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--terms", type=int, default=2200)
    ap.add_argument("--s12", action="store_true")
    args = ap.parse_args()
    run(args.terms, args.s12)
