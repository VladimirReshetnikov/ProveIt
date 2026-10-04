#!/usr/bin/env python3
"""Fresh static exact-arithmetic checks. No source code or fixtures are loaded."""
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent


def sectors(n):
    return [sum(comb(n, r) * comb(n, k-r) * (1 << (r*(k-r)))
                for r in range(max(0, k-n), min(n, k)+1))
            for k in range(2*n+1)]


def main():
    records = []
    counts = {"indices": 0, "complements": 0, "recurrences": 0,
              "lower_bounds": 0, "sector_ratios": 0,
              "tail_maxima_a": 0, "tail_maxima_c": 0,
              "leading_sector_bounds": 0}
    for n in range(1, 129):
        p = sectors(n)
        s = [F(v, 1 << (n*k)) for k, v in enumerate(p)]
        assert sum(p) == sum(comb(n, j)*(1+(1 << j))**n for j in range(n+1))
        for k in range(2*n+1):
            assert s[2*n-k] == F(p[k], 1 << (n*n))
            counts["complements"] += 1
        for k in range(2*n):
            weighted = 0
            for r in range(max(0, k-n), min(n, k)+1):
                c = k-r
                w = comb(n, r)*comb(n, c)*(1 << (r*c))
                weighted += w*((n-r)*(1 << c)+(n-c)*(1 << r))
            assert (k+1)*p[k+1] == weighted
            counts["recurrences"] += 1
            # Square a nonnegative inequality to remove its square root.
            assert ((k+1)*p[k+1])**2 >= ((2*n-k)*p[k])**2*(1 << k)
            counts["lower_bounds"] += 1
            if n >= 32:
                assert s[k+1]*2*(n+1) <= 3*s[k]
                counts["sector_ratios"] += 1
        h = [F(0)]
        running = p[0]
        for ell in range(1, 2*n):
            h.append(F(running, p[ell]))
            running += p[ell]
        j = [F(0)] + [h[ell]+F(1, p[ell]) for ell in range(1, 2*n)]
        am = max(h)
        cm = max(j)
        a_arg = [ell for ell, value in enumerate(h) if value == am]
        c_arg = [ell for ell, value in enumerate(j) if value == cm]
        if n >= 32:
            assert a_arg == [3]
            assert am == F(3*(3*n*n+n+1), n*(13*n*n-15*n+2))
            assert c_arg == [1] and cm == F(1, n)
            counts["tail_maxima_a"] += 1
            counts["tail_maxima_c"] += 1
        if n <= 32 or n in (64, 128):
            records.append({"n": n, "a_max_l": a_arg,
                "a_max_excess": str(am), "n_a_max_excess": str(n*am),
                "c_merged_max_l": c_arg, "c_merged_max_excess": str(cm)})
        for k in range(min(n, 20)+1):
            alpha = sum(F(1 << (r*(k-r)), factorial(r)*factorial(k-r))
                        for r in range(k+1))
            ratio = F(p[k], 1)/(alpha*n**k)
            assert 0 < ratio <= 1
            assert ratio >= 1-F(k*(k-1), 2*n)
            counts["leading_sector_bounds"] += 1
        counts["indices"] += 1
    result = {"status": "PASS", "arithmetic": "integers and exact rational numbers",
              "counts": counts, "selected_maxima": records,
              "limits": "Finite corroboration; infinite-n claims use PROOF.md."}
    with (HERE / "evidence/mathematics.json").open("x") as f:
        json.dump(result, f, indent=2)
        f.write("\n")
    print(json.dumps({"status": "PASS", "counts": counts}, indent=2))
    print("Small-index maximizers:", [(r["n"], r["a_max_l"], r["c_merged_max_l"])
                                      for r in records if r["n"] <= 32])


if __name__ == "__main__":
    main()
