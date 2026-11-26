"""Classify multiquadratic fields whose completed-zeta zero sum is < 2.

Requires mpmath and sympy. The exterior conductor check is in check_exterior.py. All finite numerical comparisons use interval arithmetic.
Run python classify.py > fields.json.
"""
from functools import lru_cache
import json
from math import gcd

from mpmath import iv
from sympy import kronecker_symbol, mobius

iv.dps = 30
PERIODS = 24


def radicand(d):
    return d // 4 if d % 4 == 0 else d


def discriminant(a):
    return a if a % 4 == 1 else 4 * a


def fundamental(d):
    a = radicand(d)
    return d not in (0, 1) and d == discriminant(a) and mobius(abs(a)) != 0


def multiply(d, e):
    a, b = radicand(d), radicand(e)
    return discriminant(a * b // gcd(a, b)**2)


@lru_cache(None)
def weights(k):
    t = iv.mpf(k)
    return 1/t, iv.log(t)/t


def weight_sum(d):
    """Compute B_chi via Zhao (32) and Euler--Maclaurin with a certified tail."""
    q = abs(d)
    n = PERIODS*q
    chi = [int(kronecker_symbol(d, k)) for k in range(q)]
    assert sum(chi) == 0
    lvalue, logsum = iv.mpf(0), iv.mpf(0)
    for r in range(1, q+1):
        sign = chi[r % q]
        if not sign:
            continue
        s0, s1 = iv.mpf(0), iv.mpf(0)
        for k in range(r, n, q):
            w0, w1 = weights(k)
            s0 += w0
            s1 += w1
        t = iv.mpf(n+r)
        logt = iv.log(t)
        # Integral primitive, half endpoint, and B_2 derivative correction.
        s0 += -logt/q + 1/(2*t) + q/(12*t**2)
        s1 += -logt**2/(2*q) + logt/(2*t) + q*(logt-1)/(12*t**2)
        lvalue += sign*s0
        logsum += sign*s1
    # With the B_4 term omitted, two terms of size <= q^3 |f'''(t)|/720
    # bound the tail per progression. Sum q such bounds and use t >= n.
    unit = iv.mpf([-1,1])/(60*PERIODS**4)
    lvalue += unit
    logsum += unit * iv.log(n+q)
    assert lvalue > 0
    val = iv.log(q/iv.pi) - iv.euler - 2*logsum/lvalue
    if d > 0:
        val -= 2*iv.log(2)
    return val


def below_two(number):
    if number < 2:
        return True
    if number > 2:
        return False
    raise ValueError(f"Undecided interval {number}")


def classify():
    b1 = 2 + iv.euler - iv.log(4*iv.pi)
    candidates = {d: weight_sum(d) for d in range(-551,1202) if fundamental(d)}
    vals = {d:b for d,b in candidates.items() if below_two(b1+b)}
    assert all(v>0 for v in candidates.values())
    layers = [[frozenset({1,d}) for d in sorted(vals)]]
    while layers[-1]:
        seen, new = set(), []
        for group in layers[-1]:
            for d in vals:
                if d in group:
                    continue
                larger = group | frozenset(multiply(d,e) for e in group)
                if larger in seen:
                    continue
                seen.add(larger)
                if all(e==1 or e in vals for e in larger):
                    b = b1 + sum(vals[e] for e in larger if e!=1)
                    if below_two(b):
                        new.append(larger)
        layers.append(new)
    borderline = b1+sum(vals[e] for e in (-15,-24,40))
    return {"global_input":"check_exterior.py and its analytic conductor bound exclude every discriminant outside [-551, 1201].",
            "checked_fundamental_discriminants":len(candidates),
            "discriminants_with_character_weight_below_two":sum(below_two(b) for b in candidates.values()),
            "borderline_biquadratic_enclosure":str(borderline),
            "counts_by_degree_including_Q":{2**k:len(layer) for k, layer in enumerate([[{1}]]+layers)},
            "fields_by_nontrivial_quadratic_discriminants":
                [sorted([sorted(v-{1}) for v in layer]) for layer in layers if layer]}


if __name__ == "__main__":
    print(json.dumps(classify(),indent=2))
