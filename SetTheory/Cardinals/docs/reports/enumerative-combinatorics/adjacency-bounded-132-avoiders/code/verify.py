"""Run standard-library-only exact tests and verify rational PF certificates.

Run from the archive root: python code/verify.py
No network access, CAS, external theorem prover, or floating point is used.
"""
from __future__ import annotations
import json
from fractions import Fraction
from functools import lru_cache
from math import comb
from itertools import permutations
from pathlib import Path
from model import (avoids132, av132, block_counts, c, catalan, counts,
                   edges, endpoint_counts, first_count, majorant_counts, verify_shift)

ROOT = Path(__file__).resolve().parents[1]

if not __debug__:
    raise RuntimeError("Run the exact verifier without Python's -O flag")


@lru_cache(maxsize=None)
def certificate_edges(m: int, component: str = "all"):
    """Independently reconstruct certificate matrices via Catalan convolutions.

    This intentionally does not call model.edges, model.c, or first_count.
    Coefficients of C(x)^j use integer convolution rather than the closed
    binomial formula used by the computational model.
    """
    if component == "all":
        thresholds = list(range(m)) + [None]
        ss = [(p, q) for p in thresholds for q in thresholds]
    elif component == "U":
        ss = [(p, None) for p in range(m)]
    elif component == "V":
        ss = [(p, q) for p in range(m) for q in range(p)]
        ss += [(p, m - 1) for p in range(m - 1)]
    else:
        raise ValueError("Unknown component")
    index = {state: i for i, state in enumerate(ss)}
    cat = [comb(2*n, n)//(n+1) for n in range(m+1)]
    powers = [[1] + [0]*m]
    for j in range(1, m):
        powers.append([sum(powers[-1][i]*cat[n-i] for i in range(n+1))
                       for n in range(m+1)])
    es = []
    for row, (p, q) in enumerate(ss):
        for k in range(1, m+1):
            if q is not None and k > q:
                continue
            target = (m-k, None if q is None else q-k)
            if target not in index:
                continue
            if k == 1:
                multiplicity = 1
            elif p is None:
                multiplicity = cat[k-1]
            else:
                multiplicity = sum(powers[j][k-j-1]
                                   for j in range(1, min(p, k-1)+1))
            if multiplicity:
                es.append((row, index[target], k, multiplicity))
        if p is None or p > 0:
            target = (None if p is None else p-1, m-1)
            if target in index:
                es.append((row, index[target], 1, 1))
    return ss, es


def main() -> None:
    for n in range(8):
        direct = {p for p in permutations(range(1, n + 1)) if avoids132(p)}
        assert direct == set(av132(n))
    print("PASS: direct 132-pattern test vs Catalan generator, n=0..7")

    for n in range(1, 11):
        aa = av132(n)
        assert len(aa) == catalan(n)
        for d in range(1, n + 1):
            assert sum(p[0] == n + 1 - d for p in aa) == first_count(n + 1, d)
    print("PASS: first-entry formula, all Catalan avoiders of length 1..10")

    endpoint_checks = 0
    for m in range(1, 9):
        ss, cc = endpoint_counts(m, 10)
        for n in range(1, 11):
            aa = [p for p in av132(n)
                  if all(abs(a - b) <= m for a, b in zip(p, p[1:]))]
            exact = [[0] * n for _ in range(n)]
            for p in aa:
                exact[n - p[0]][n - p[-1]] += 1
            for row, (u, v) in enumerate(ss):
                real = sum(exact[a][b]
                           for a in range(n if u is None else min(n, u + 1))
                           for b in range(n if v is None else min(n, v + 1)))
                assert real == cc[row][n], (m, n, u, v)
                endpoint_checks += 1
    print(f"PASS: {endpoint_checks} cumulative endpoint counts, m=1..8, n=1..10")

    edge_checks = 0
    for m in range(2, 31):
        for comp in ("U", "V"):
            edge_checks += verify_shift(m, comp)
    print(f"PASS: {edge_checks} weighted edges under the shift, m=2..30, U and V")

    for m in range(2, 13):
        aa = counts(m, 100)
        ub = majorant_counts(m, 100)
        assert all(a <= b for a, b in zip(aa, ub))
        for d in range(1, min(m, 6)):
            lb = block_counts(m, d, 100)
            assert all(b <= a for a, b in zip(aa, lb))
    print("PASS: coefficientwise majorant and skew-block lower bounds through n=100")

    path = ROOT / "data" / "perron_certificates.json"
    if path.exists():
        certs = json.loads(path.read_text())
        rows_checked = 0
        for cert in certs:
            m, comp = cert["m"], cert["component"]
            ss, es = certificate_edges(m, comp)
            assert (ss, es) == edges(m, comp)
            for side in ("lower_radius", "upper_radius"):
                item = cert[side]
                num, den, vector = item["numerator"], item["denominator"], item["vector"]
                assert isinstance(num, int) and isinstance(den, int) and num > 0 and den > 0
                assert len(vector) == len(ss) and all(v > 0 for v in vector)
                vv = [0] * len(ss)
                powers = [num ** k * den ** (m - k) for k in range(m + 1)]
                for a, b, k, coeff in es:
                    vv[a] += coeff * powers[k] * vector[b]
                rhs = [den ** m * v for v in vector]
                if side == "lower_radius":
                    assert all(x < y for x, y in zip(vv, rhs)), (m, comp, side)
                else:
                    assert all(x > y for x, y in zip(vv, rhs)), (m, comp, side)
                rows_checked += len(ss)
        lookup = {(z["m"], z["component"]): z for z in certs}
        def endpoint(z, name):
            e = z[name]
            return Fraction(e["numerator"], e["denominator"])
        for m in sorted({z["m"] for z in certs}):
            u, v = lookup[m,"U"], lookup[m,"V"]
            if m <= 4:
                assert endpoint(u,"upper_radius") < endpoint(v,"lower_radius")
            else:
                assert endpoint(v,"upper_radius") < endpoint(u,"lower_radius")
            if (m-1,"U") in lookup:
                for comp in ("U","V"):
                    assert endpoint(lookup[m,comp],"upper_radius") < endpoint(lookup[m-1,comp],"lower_radius")
        print(f"PASS: {len(certs)} Perron-radius interval certificates; {rows_checked} exact row inequalities")
        print("PASS: disjoint certified intervals prove the component comparison for m=2..20")
    else:
        raise FileNotFoundError("Missing bundled perron_certificates.json")

    gfpath = ROOT / "data" / "generating_functions.json"
    if gfpath.exists():
        def trim(p):
            while len(p)>1 and p[-1]==0:
                p.pop()
            return p
        def add(a,b,scale=1,shift=0):
            out=a.copy()+[0]*max(0,len(b)+shift-len(a))
            for j,v in enumerate(b):
                out[j+shift]+=scale*v
            return trim(out)
        def mul(a,b):
            out=[0]*(len(a)+len(b)-1)
            for i,u in enumerate(a):
                for j,v in enumerate(b):
                    out[i+j]+=u*v
            return trim(out)
        for item in json.loads(gfpath.read_text()):
            mc=item["m"]
            cert=json.loads((ROOT/"data"/f"symbolic_certificate_m{mc}.json").read_text())
            ss,es=certificate_edges(mc)
            assert (ss,es)==edges(mc)
            dd=cert["common_denominator"]
            ppall=cert["state_numerators"]
            assert dd[0]==1 and len(ppall)==len(ss)
            residual=[p.copy() for p in ppall]
            for a,b,k,mult in es:
                residual[a]=add(residual[a],ppall[b],-mult,k)
            assert all(trim(p)==[0]+dd for p in residual)
            lhs=mul(add(dd,ppall[ss.index((None,None))]),item["denominator_ascending"])
            rhs=mul(dd,item["numerator_ascending"])
            assert lhs==rhs
            aa = counts(item["m"], 200)
            pp, qq = item["numerator_ascending"], item["denominator_ascending"]
            for n in range(201):
                conv = sum(q * aa[n-j] for j, q in enumerate(qq) if j <= n)
                assert conv == (pp[n] if n < len(pp) else 0), (item["m"], n)
        print("PASS: exact polynomial matrix certificates for all bundled GFs; coefficients checked through n=200")
        print("PASS: certificate matrices independently reconstructed by Catalan convolution")
    else:
        raise FileNotFoundError("Missing bundled generating_functions.json")
    print("ALL EXACT CHECKS PASSED")


if __name__ == "__main__":
    main()
