#!/usr/bin/env python3
"""Exact finite checks illustrating the torsion theorem and its sharp boundaries.

These computations illustrate the proof. They do not verify the infinite-family
theorem, which is established mathematically in the report.
Requires Python 3 and SymPy. Run from the archive root.
"""
from fractions import Fraction
from itertools import product
import json
import math
from pathlib import Path
import sympy as sp


def ordp(n, p):
    n = abs(int(n))
    if not n: return None
    v = 0
    while n % p == 0: v += 1; n //= p
    return v


def positive_excess_checks():
    # The coordinate-step inequality max(a-c,0) <= a-b follows from b<=a,c.
    checked = 0
    for b, a, c in product(range(8), repeat=3):
        if b <= a and b <= c:
            assert max(a-c, 0) <= a-b
            checked += 1
    # Positive variation is subadditive along coordinate changes.
    paths = 0
    for x in product(range(6), repeat=4):
        assert max(x[-1]-x[0], 0) <= sum(max(x[i+1]-x[i], 0) for i in range(3))
        paths += 1
    return {"coordinate_inequality_cases": checked, "variation_paths": paths}


def maximal_order_counterexamples():
    # In Q_p(zeta_{p^m}), v(zeta^a-zeta^b) depends only on v_p(a-b).
    # The difference vanishes if a=b mod p^m. All computations are rational.
    rows = []
    for p in [2, 3, 5, 7]:
        for m in [2, 3, 4]:
            n = p**m
            baseline = Fraction(1, p**(m-1))
            values = []
            infinities = 0
            for b in range(1, n):
                if b % p == 0: continue
                val = Fraction(0)
                zero = False
                for a in range(1, p):
                    d = (b-a) % n
                    if d == 0: zero = True; break
                    j = ordp(d, p)
                    val += Fraction(1, p**(m-j-1)*(p-1))
                if zero: infinities += 1
                else:
                    assert val >= 2*baseline and val > baseline
                    values.append(val)
            assert baseline < 1
            rows.append({"p": p, "m": m, "augmentation_valuation": str(baseline),
                         "primitive_characters": int(sp.totient(n)),
                         "zero_values": infinities,
                         "minimum_finite_primitive_valuation": str(min(values))})
    return rows


def resultant_examples():
    # For integral rational coefficients P, all primitive p^h evaluations are
    # Galois conjugate. Their common v_p is v_p(resultant)/phi(p^h).
    # P_j(T)=Phi_{2^j}(1+T), j=1,2,3, witness T=4. Each has witness valuation 1.
    t, z = sp.symbols("t z")
    polynomials = [sp.Poly(sp.cyclotomic_poly(2**j, 1+t), t) for j in [1,2,3]]
    baseline = [ordp(P.eval(4), 2) for P in polynomials]
    assert baseline == [1,1,1]
    rows = []
    for h in range(1, 7):
        C = sp.cyclotomic_poly(2**h, z)
        vals = []
        for P in polynomials:
            res = sp.resultant(C, P.as_expr().subs(t, z-1), z)
            e = ordp(res, 2)
            vals.append(None if e is None else Fraction(e, int(sp.totient(2**h))))
        excess = None if None in vals else sum(max(v-b,0) for v,b in zip(vals,baseline))
        rows.append({"order_exponent": h, "valuations": ["infinity" if v is None else str(v) for v in vals],
                     "total_positive_excess": "infinity" if excess is None else str(excess)})
    assert rows[0]["total_positive_excess"] == "infinity"
    assert rows[1]["total_positive_excess"] == "infinity"
    assert rows[2]["total_positive_excess"] == "infinity"
    assert rows[3]["total_positive_excess"] == "0"
    return {"polynomials": [str(P.as_expr()) for P in polynomials],
            "witness": 4, "baseline_valuations": baseline, "rows": rows}


def illustrative_bound():
    # Use a rigorously verified rational harmonic certificate at moderate size.
    p, s0, rho, budget, eps = 2, 1, Fraction(1), Fraction(0), Fraction(1)
    delta = min(eps, 1) / (s0+2)
    H, harmonic = 0, Fraction(0)
    while not budget+1 < delta*harmonic:
        H += 1
        r = Fraction(1, p**(H-1)*(p-1))
        if r <= rho: harmonic += Fraction(1,H+1)
    assert budget+1 < delta*harmonic
    # A larger example is deliberately reported in log scale rather than
    # allocating the astronomically large grid or truncation polynomial.
    log_H_example = math.log(3) + 24
    return {"exact_small_case": {"p":p,"s0":s0,"rho":str(rho),"B":str(budget),"epsilon":str(eps),
                                 "delta":str(delta),"H":H,"harmonic_sum":str(harmonic),
                                 "torsion_order":str(p**H)},
            "large_case": {"p":2,"s0":1,"rho":"1/2","B":1,"epsilon":"1/4",
                           "sufficient_H_lower_scale_approx": math.exp(log_H_example),
                           "description":"H may be taken above 3 exp(24); the order is 2^H. Approximate scale only."}}


if __name__ == "__main__":
    result = {"status":"exact finite checks, not a proof of the analytic theorem",
              "positive_excess": positive_excess_checks(),
              "maximal_order_counterexamples": maximal_order_counterexamples(),
              "resultant_examples": resultant_examples(),
              "harmonic_bounds": illustrative_bound()}
    print(json.dumps(result,indent=2))
