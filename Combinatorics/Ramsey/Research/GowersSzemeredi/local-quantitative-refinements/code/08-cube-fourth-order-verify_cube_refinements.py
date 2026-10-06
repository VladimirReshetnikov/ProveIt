#!/usr/bin/env python3
"""Exact, finite checks for fourth-order additive-cube refinements.

Python 3.10+, standard library only. These tests supplement the article's
proofs; they are not a formal proof of its general assertions.
Run: python verify_cube_refinements.py --output verification_results.json
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import comb
from pathlib import Path
import json


def vertices(d: int) -> list[tuple[int, ...]]:
    return list(product((0, 1), repeat=d))


def is_parallelogram(points: tuple[tuple[int, ...], ...]) -> bool:
    a, b, c, d = points
    return any(all(u[i] + v[i] == w[i] + z[i] for i in range(len(a)))
               for u, v, w, z in ((a,b,c,d),(a,c,b,d),(a,d,b,c)))


def quartic_counts(d: int) -> dict[str, int]:
    vs = vertices(d)
    rectangular = binary_flat = 0
    for s in combinations(vs, 4):
        rectangular += is_parallelogram(s)
        binary_flat += all(sum(v[i] for v in s) % 2 == 0 for i in range(d))
    p = 2**d
    r = (6**d - 2*4**d + 2**d)//8
    total = p*(p-1)*(p-2)//24
    assert rectangular == r
    assert binary_flat == total
    return {"dimension": d, "quadruples": comb(p,4), "R": r,
            "T": total-r, "F": total}


def triple_checks(d: int) -> int:
    """A unit 2x2 minor after reflecting one vertex to zero."""
    count = 0
    for a,b,c in combinations(vertices(d),3):
        u = [x ^ y for x,y in zip(a,b)]
        v = [x ^ y for x,y in zip(a,c)]
        assert any(abs(u[i]*v[j]-u[j]*v[i]) == 1
                   for i,j in combinations(range(d),2))
        count += 1
    return count


def five_and_six_counts() -> dict[str, object]:
    vs = vertices(3)
    q = [frozenset(s) for s in combinations(vs,4) if is_parallelogram(s)]
    hist = Counter()
    five_circuits = []
    for s in combinations(vs,5):
        found = sum(a.issubset(s) for a in q)
        hist[found] += 1
        if not found:
            five_circuits.append(frozenset(s))
    stars = [frozenset(v for v in vs if sum(x != y for x,y in zip(w,v)) != 1)
             for w in vs]
    assert hist == {1:48, 0:8}
    assert set(stars) == set(five_circuits)
    six = Counter(sum(x != y for x,y in zip(a,b)) for a,b in combinations(vs,2))
    assert six == {1:12, 2:12, 3:4}
    return {"five_subsets_by_parallelogram_count": dict(hist),
            "six_subsets_by_missing_pair_distance": dict(six)}


def cube_coefficients(f: list[int], d: int = 3) -> list[Fraction]:
    """Coefficients c_r of C_d(delta + eta*f)=sum c_r delta^(p-r) eta^r."""
    n = len(f); p = 2**d; vs = vertices(d)
    sums = [0]*(p+1)
    for params in product(range(n), repeat=d+1):
        x, hs = params[0], params[1:]
        values = [f[(x+sum(a*b for a,b in zip(v,hs))) % n] for v in vs]
        coeff = [1]+[0]*p
        for j,value in enumerate(values):
            for r in range(j+1,0,-1):
                coeff[r] += value*coeff[r-1]
        for r,c in enumerate(coeff): sums[r] += c
    return [Fraction(c,n**(d+1)) for c in sums]


def partial_cube(f: list[int], subset: list[tuple[int, ...]]) -> Fraction:
    n = len(f); d = len(subset[0]); total = 0
    for params in product(range(n), repeat=d+1):
        x, hs = params[0], params[1:]
        term = 1
        for v in subset:
            term *= f[(x+sum(a*b for a,b in zip(v,hs))) % n]
        total += term
    return Fraction(total,n**(d+1))


def direct_identity_checks() -> list[dict[str, object]]:
    out = []
    vs = vertices(3)
    star = [(0,0,0),(1,1,0),(1,0,1),(0,1,1),(1,1,1)]
    for n in range(3,10):
        raw = [((i*i+3*i+1) % 7)-3 for i in range(n)]
        total = sum(raw)
        f = [n*x-total for x in raw]
        assert sum(f) == 0
        c = cube_coefficients(f)
        e4 = partial_cube(f,vertices(2))
        e2 = Fraction(sum(x*((-1)**i) for i,x in enumerate(f)),n)**4 if n%2 == 0 else Fraction(0)
        assert c[0] == 1 and c[1:4] == [0,0,0]
        assert c[4] == 12*e4 + 2*e2
        if n%2:
            s5 = partial_cube(f,star)
            assert c[5] == 8*s5
            a6,b6,c6 = [partial_cube(f,[v for v in vs if v not in [(0,0,0),w]])
                         for w in [(0,0,1),(0,1,1),(1,1,1)]]
            a7 = partial_cube(f,[v for v in vs if v != (0,0,0)])
            assert c[6] == 12*a6+12*b6+4*c6
            assert c[7] == 8*a7
        out.append({"cyclic_order":n,"test_function":f,
                    "coefficients":[str(x) for x in c],
                    "E4":str(e4),"E_order_two":str(e2)})
    return out


def spectral_cube_coefficients(n: int, spectrum: dict[int, int], d: int = 3) -> list[Fraction]:
    """Exact Fourier expansion, with coefficients spectrum[k]/2.

    The zero-frequency option stands for delta and is NOT in spectrum.
    Coefficients are accumulated as integers before powers of two are divided.
    """
    vs = vertices(d); p = len(vs); totals = [0]*(p+1)
    freqs = [0]+list(spectrum)
    rows = [[i for i,v in enumerate(vs) if v[j]] for j in range(d)]
    for ks in product(freqs,repeat=p):
        if sum(ks) % n or any(sum(ks[i] for i in row) % n for row in rows):
            continue
        r = 0; sign = 1
        for k in ks:
            if k:
                r += 1; sign *= spectrum[k]
        totals[r] += sign
    return [Fraction(c,2**r) for r,c in enumerate(totals)]


def order_two_checks(max_d: int = 7) -> list[dict[str,int]]:
    out = []
    for d in range(2,max_d+1):
        p = 2**d
        numerator = 2*comb(p,4)+2*(p-1)*comb(p//2,2)
        assert numerator % (2*p) == 0
        coefficient = numerator//(2*p)
        expected = p*(p-1)*(p-2)//24
        assert coefficient == expected
        # Verify all coefficients of degree 1,2,3 disappear.
        assert (2*comb(p,2)-2*(p-1)*(p//2)) == 0
        out.append({"dimension":d,"quartic_coefficient":coefficient})
    return out


def product_group_checks() -> list[dict[str, object]]:
    out = []
    for mods in [(2,2),(2,2,2),(2,3),(3,3)]:
        elements = list(product(*(range(m) for m in mods)))
        n = len(elements); index = {x:i for i,x in enumerate(elements)}
        plus = [[index[tuple((a+b)%m for a,b,m in zip(x,y,mods))]
                 for y in elements] for x in elements]
        raw = [((i*i+3*i+1)%7)-3 for i in range(n)]
        f = [n*z-sum(raw) for z in raw]
        sums = [0]*9
        e4_total = 0
        for x,a,b in product(range(n),repeat=3):
            e4_total += f[x]*f[plus[x][a]]*f[plus[x][b]]*f[plus[plus[x][a]][b]]
        for x,a,b,c in product(range(n),repeat=4):
            ids = [x,plus[x][a],plus[x][b],plus[plus[x][a]][b]]
            ids += [plus[u][c] for u in ids]
            es = [1]+[0]*8
            for j,u in enumerate(ids):
                for r in range(j+1,0,-1): es[r] += f[u]*es[r-1]
            for r,v in enumerate(es): sums[r] += v
        coeff = [Fraction(z,n**4) for z in sums]
        e4 = Fraction(e4_total,n**3)
        e2 = Fraction(0)
        for bits in product(*([(0,1) if m%2 == 0 else (0,) for m in mods])):
            if not any(bits): continue
            e2 += Fraction(sum(f[i]*(-1)**sum(b*x for b,x in zip(bits,z))
                                for i,z in enumerate(elements)),n)**4
        assert coeff[1:4] == [0,0,0]
        assert coeff[4] == 12*e4+2*e2
        out.append({"moduli":mods,"E4":str(e4),"E_order_two":str(e2),
                    "quartic_coefficient":str(coeff[4])})
    return out


def fast_spectral_certificate() -> dict[str, object]:
    allowed = {0,1,10,2,9}
    signs = {1:1,10:1,2:-1,9:-1}
    counts: Counter = Counter()
    for a,b,c,d in product(allowed,repeat=4):
        ks = [a,b,c,d,(-a-b-c)%11,(-a-b-d)%11,(-a-c-d)%11,(2*a+b+c+d)%11]
        if not all(k in allowed for k in ks): continue
        r = sum(k != 0 for k in ks); sign = 1
        for k in ks:
            if k: sign *= signs[k]
        counts[r,sign] += 1
    coefficients = [Fraction(counts[r,1]-counts[r,-1],2**r) for r in range(9)]
    assert coefficients == spectral_cube_coefficients(11,{1:1,-1:1,2:-1,-2:-1})
    ratio = sum(4*coefficients[r]*Fraction(1,6)**(r-4) for r in range(4,9))
    assert ratio == Fraction(15337,1296) < 12
    return {"free_frequency_tuples_checked":625,
            "signed_counts_by_degree": {str(r): [counts[r,1], counts[r,-1]] for r in range(9)},
            "ratio_at_eta_over_delta_one_sixth":str(ratio)}


def main() -> None:
    if not __debug__:
        raise RuntimeError("Run this verifier without -O; assertions must be enabled.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification_results.json"))
    parser.add_argument("--max-d",type=int,default=6,choices=range(2,7))
    args = parser.parse_args()
    results: dict[str,object] = {"arithmetic":"integer and fractions.Fraction only"}
    results["quartic_enumeration"] = [quartic_counts(d) for d in range(2,args.max_d+1)]
    results["triple_checks"] = {str(d):triple_checks(d) for d in range(2,6)}
    results["three_cube_orbits"] = five_and_six_counts()
    results["direct_function_checks"] = direct_identity_checks()
    results["product_group_checks"] = product_group_checks()
    results["fast_spectral_certificate"] = fast_spectral_certificate()
    counterexample = spectral_cube_coefficients(11,{1:1,-1:1,2:-1,-2:-1})
    assert counterexample[:6] == [1,0,0,0,3,Fraction(-1,2)]
    delta = Fraction(1,2); eta = Fraction(1,100)
    difference = sum(counterexample[r]*delta**(8-r)*eta**r for r in range(5,9))
    assert difference < 0
    results["counterexample"] = {"group":"Z/11Z", "h":"cos(2*pi*x/11)-cos(4*pi*x/11)",
                                  "coefficients":[str(x) for x in counterexample],
                                  "delta":str(delta),"eta":str(eta),
                                  "excess_minus_quartic":str(difference)}
    cosine = spectral_cube_coefficients(11,{1:1,-1:1})
    assert cosine[4] == Fraction(3,2)
    results["cosine_three_cube_coefficients"] = [str(x) for x in cosine]
    results["order_two_checks"] = order_two_checks()
    results["status"] = "ALL ASSERTIONS PASSED"
    args.output.write_text(json.dumps(results,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({"status":results["status"],"output":str(args.output),
                      "counterexample":results["counterexample"],
                      "cosine":results["cosine_three_cube_coefficients"]},indent=2))

if __name__ == "__main__":
    main()
