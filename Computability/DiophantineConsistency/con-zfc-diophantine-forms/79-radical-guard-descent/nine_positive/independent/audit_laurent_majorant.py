#!/usr/bin/env python3
"""Independent four-variable integer audit of the proposed direct majorant.

Usage: python3 audit_laurent_majorant.py INPUT_JSON [OUTPUT_JSON]
Only the coefficient data are imported from the construction. No SymPy or
construction algorithm is imported. The mathematical inequality is proved
in MAJORANT_AUDIT.md; this script checks its finite identities and premises.
"""
import hashlib
import json
import sys
from collections import defaultdict
from math import comb
from pathlib import Path

ZERO = (0, 0, 0, 0)


def require(value, message):
    if not value:
        raise ValueError(message)


def const(x):
    return {ZERO: x} if x else {}


def var(k):
    return {tuple(int(j == k) for j in range(4)): 1}


def add(*ps):
    out = defaultdict(int)
    for p in ps:
        for m, v in p.items():
            out[m] += v
    return {m: v for m, v in out.items() if v}


def scale(p, c):
    return {m: v*c for m, v in p.items() if v*c}


def mul(a, b):
    out = defaultdict(int)
    for m, v in a.items():
        for n, w in b.items():
            out[tuple(x+y for x, y in zip(m, n))] += v*w
    return {m: v for m, v in out.items() if v}


def power(p, n):
    z = const(1)
    while n:
        if n & 1:
            z = mul(z, p)
        n >>= 1
        if n:
            p = mul(p, p)
    return z


def subtract(a, b):
    return add(a, scale(b, -1))


def shifted(p, a_shift, c_shift):
    out = defaultdict(int)
    for (a, c, i, z), v in p.items():
        for aa in range(a+1):
            av = comb(a, aa)*a_shift**(a-aa)
            for cc in range(c+1):
                out[(aa, cc, i, z)] += v*av*comb(c, cc)*c_shift**(c-cc)
    return {m: v for m, v in out.items() if v}


def shifted_all(p, offsets):
    result = p
    for axis, shift in enumerate(offsets):
        out = defaultdict(int)
        for m, v in result.items():
            for e in range(m[axis]+1):
                powers = list(m)
                powers[axis] = e
                out[tuple(powers)] += v*comb(m[axis], e)*shift**(m[axis]-e)
        result = {m: v for m, v in out.items() if v}
    return result


def maxdegrees(p):
    return tuple(max(m[k] for m in p) for k in range(4))


def wdegree(p, weights):
    return max(sum(x*y for x, y in zip(m, weights)) for m in p)


def main():
    source = Path(sys.argv[1])
    raw = source.read_bytes()
    data = json.loads(raw)
    P = {tuple(m): int(c) for m, c in data["T_terms"]}
    R = {tuple(m): int(c) for m, c in data["defect_terms"]}
    require(len(P) == len(data["T_terms"]), "duplicate majorant terms")
    require(len(R) == len(data["defect_terms"]), "duplicate defect terms")
    require(all(len(m) == 4 and min(m) >= 0 for m in P), "ordinary polynomial exponents")
    A, C, i, Z = [var(k) for k in range(4)]
    one = const(1)
    A2m = subtract(power(A, 2), one)
    J = add(scale(A, 4), const(-5))
    D = add(mul(A2m, power(C, 2)), one)
    e = mul(mul(i, J), C)
    E = mul(mul(e, D), C)
    F = add(mul(A2m, power(E, 2)), one)
    G = add(A, mul(F, subtract(add(mul(C, D), one), A)))
    H = add(C, mul(F, Z))
    I = add(mul(subtract(power(G, 2), one), power(H, 2)), one)
    Q = mul(mul(D, F), I)
    sigma = scale(power(C, 7), 65536)
    require(data["scale"] == {"numeral": 65536, "C_power": 7}, "scale declaration")
    require(subtract(power(P, 2), mul(power(sigma, 2), Q)) == R,
            "literal defect identity")
    S = sum(abs(v) for v in R.values())
    require(S == 140213210301297074855, "absolute coefficient mass")
    require(maxdegrees(P) == (23, 31, 5, 1), "majorant component degrees")
    require(maxdegrees(R) == (22, 42, 10, 2), "defect component degrees")
    shifted_P = shifted(P, 3, 1)
    require(len(shifted_P) == 1816 and all(v > 0 for v in shifted_P.values()),
            "positive-coefficient shift certificate")
    require(any(m[0] == 0 and m[1] == 0 for m in shifted_P),
            "majorant strictly positive when A=3 and C=1")
    topblock = {m: v for m, v in shifted_P.items() if m[0] == 23}
    expected_topblock = {(23, k, 5, 1): 2**26*comb(31, k) for k in range(32)}
    require(topblock == expected_topblock, "complete leading A-block")
    shifted_R = shifted_all(R, (3, 1, 1, 1))
    require(len(shifted_R) == 32637 and all(v > 0 for v in shifted_R.values()),
            "full four-variable defect positivity certificate")
    require(shifted_R.get(ZERO, 0) > 0, "strictness at every domain boundary")
    correction = {(0, 11, 5, 1): S+1}
    V1 = add(P, correction)
    delta1 = add(R, scale(mul(P, correction), 2), power(correction, 2))
    require(subtract(power(V1, 2), mul(power(sigma, 2), Q)) == delta1,
            "corrected defect identity")
    # Outer substitutions certified by source 71: deg A=16425; deg C=deg i=1;
    # Z=2Rsource+1+(j-1)C has degree 7963. Its leading coefficient is positive.
    weights = (16425, 1, 1, 7963)
    dv = wdegree(V1, weights)
    dd = wdegree(delta1, weights)
    require(dv == 385774 and dd == 393753, "outer weighted degrees")
    topV = {m: v for m, v in V1.items() if sum(x*y for x, y in zip(m, weights)) == dv}
    topD = {m: v for m, v in delta1.items() if sum(x*y for x, y in zip(m, weights)) == dd}
    require(topV == {(23, 31, 5, 1): 2**26}, "majorant weighted leader")
    require(topD == {(23, 42, 10, 2): 2**27*(S+1)}, "corrected defect weighted leader")
    om, e0, v0, d0, a0 = 82360, 16429, 57239, 57240, 114478
    bsmall = max(2*e0, e0+om+max(v0, dv), 2*om+max(d0, dd))
    outer_terms = {
        "Bsmall_squared": 2*bsmall,
        "mixed_term": 2*om+v0+dv+bsmall,
        "delta0_V1_squared_term": 4*om+d0+2*dv,
        "a0_delta1_term": 4*om+a0+dd,
    }
    require(bsmall == 558473, "Bsmall degree")
    require(outer_terms == {"Bsmall_squared": 1116946, "mixed_term": 1166206,
                           "delta0_V1_squared_term": 1158228, "a0_delta1_term": 837671},
            "resolved outer degree terms")
    direct_v = wdegree(P, weights)
    direct_d = wdegree(R, weights)
    direct_b = max(2*e0, e0+om+max(v0, direct_v), 2*om+max(d0, direct_d))
    direct_terms = {"Bsmall_squared": 2*direct_b,
                    "mixed_term": 2*om+v0+direct_v+direct_b,
                    "delta0_V1_squared_term": 4*om+d0+2*direct_v,
                    "a0_delta1_term": 4*om+a0+direct_d}
    require(direct_v == 385774 and direct_d == 377328 and direct_b == 542048,
            "direct majorant degrees")
    require(direct_terms == {"Bsmall_squared": 1084096, "mixed_term": 1149781,
                            "delta0_V1_squared_term": 1158228, "a0_delta1_term": 821246},
            "direct resolved outer degree terms")
    result = {
        "status": "PASS", "checker": "independent standard-library four-tuple sparse ring",
        "input_sha256": hashlib.sha256(raw).hexdigest(),
        "majorant_terms": len(P), "defect_terms": len(R), "shifted_positive_terms": len(shifted_P),
        "coefficient_mass": S, "exact_defect_checked": True, "complete_top_block_checked": True,
        "preliminary_corrected_candidate": {"V1_degree": dv, "delta1_degree": dd,
            "Bsmall_degree": bsmall, "outer_term_degrees": outer_terms,
            "exact_degree": max(outer_terms.values())},
        "strict_defect_positive_terms": len(shifted_R),
        "strict_defect_constant": shifted_R[ZERO],
        "weighted_V1_degree": direct_v, "weighted_delta1_degree": direct_d,
        "Bsmall_degree": direct_b, "outer_term_degrees": direct_terms,
        "exact_outer_degree": max(direct_terms.values()),
        "leading_coefficient_positive": True,
        "scope": "Exact finite identities plus the stated source degree contracts. Universal inequalities and root-recovery reasoning are reviewed in MAJORANT_AUDIT.md."
    }
    out = Path(sys.argv[2]) if len(sys.argv) > 2 else source.with_name("INDEPENDENT_MAJORANT_AUDIT.json")
    out.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
