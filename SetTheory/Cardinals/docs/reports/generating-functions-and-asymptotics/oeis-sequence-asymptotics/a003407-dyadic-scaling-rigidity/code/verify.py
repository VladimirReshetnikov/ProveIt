#!/usr/bin/env python3
"""Reproduce arithmetic certificates and small 3AP-free counts.

Python >= 3.10, standard library only.  Large counts are externally supplied
OEIS A003407 data, NOT independently certified by this script.  Assertions
check consequences of those data; the independent subset DP checks n <= max_n.
See article.tex for the mathematical distinction and proof of the DP.
"""
from __future__ import annotations
import argparse
import json
import time
from decimal import Decimal, localcontext
from functools import lru_cache
from itertools import permutations
from pathlib import Path
from typing import Dict, Tuple

ROOT = Path(__file__).resolve().parent


def load_counts(path: Path) -> Dict[int, int]:
    data: Dict[int, int] = {}
    for line_no, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        fields = line.split()
        if len(fields) != 2:
            raise ValueError(f"{path}:{line_no}: expected n and count")
        n, value = map(int, fields)
        if n < 0 or value <= 0 or n in data:
            raise ValueError(f"{path}:{line_no}: invalid or duplicate entry")
        data[n] = value
    if set(data) != set(range(201)):
        raise ValueError("Expected exactly the indices 0 through 200")
    return data


def count_avoiding(n: int) -> Tuple[int, int]:
    """Exact subset-state DP. Returns (count, number of reached states).

    An endpoint pair symmetric about the next value y must be wholly used
    or wholly unused. Splitting that pair would force a later forbidden AP.
    Only prefixes satisfying this invariant are generated.
    """
    if not 0 <= n <= 36:
        raise ValueError("Independent Python verification is limited to 0 <= n <= 36")
    pairs = tuple(tuple((1 << (y-d)) | (1 << (y+d))
                        for d in range(1, min(y, n-1-y)+1))
                  for y in range(n))
    full = (1 << n) - 1

    @lru_cache(maxsize=None)
    def completions(used: int) -> int:
        if used == full:
            return 1
        total, remaining = 0, full ^ used
        while remaining:
            bit = remaining & -remaining
            remaining -= bit
            y = bit.bit_length() - 1
            if all((used & pair) in (0, pair) for pair in pairs[y]):
                total += completions(used | bit)
        return total

    value = completions(0)
    states = completions.cache_info().currsize
    completions.cache_clear()
    return value, states


def brute_force(n: int) -> int:
    triples = tuple((i,j,k) for i in range(n) for j in range(i+1,n)
                    for k in range(j+1,n))
    return sum(all(p[i]+p[k] != 2*p[j] for i,j,k in triples)
               for p in permutations(range(1,n+1)))


def extremum(data: Dict[int, int], N: int, c: int, maximum: bool) -> int:
    """Select an extremum of (c*data[n])**(1/n) by integer comparisons."""
    best = N
    for n in range(N+1, 2*N+1):
        left, right = (c*data[n])**best, (c*data[best])**n
        if (left > right) if maximum else (left < right):
            best = n
    return best


def rational_root_enclosure(value: int, n: int, digits: int = 8) -> dict:
    """Enclose value**(1/n) strictly between adjacent decimal rationals."""
    scale = 10**digits
    lo, hi = 0, 22*scale
    target = value * scale**n
    if hi**n <= target:
        raise ValueError("Root lies above the configured search range")
    while hi - lo > 1:
        mid = (lo+hi)//2
        if mid**n < target:
            lo = mid
        else:
            hi = mid
    # None of the endpoints used in this report is an exact grid root.
    assert lo**n < target < hi**n
    with localcontext() as ctx:
        ctx.prec = 75
        approximation = (Decimal(value).ln()/n).exp()
    return {"lower_numerator": lo, "upper_numerator": hi,
            "denominator": scale, "approximation": str(approximation)}


def verify(max_n: int) -> dict:
    data = load_counts(ROOT / "data" / "counts.txt")
    assert data[0] == data[1] == 1 and data[2] == 2
    for n in range(2,201):
        product = data[n//2]*data[(n+1)//2]
        assert 2*product <= data[n] <= 21*product, ("recurrence", n)
    # Ho's nonconstancy certificate, checked without logarithms or floats.
    assert (2*data[64])**75 > (21*data[75])**64
    assert (2*data[128])**162 > (21*data[162])**128
    # Explicit 2:1 gluing loss and gain certificates from Section 6.
    negative_num, negative_den = (21*data[192])**2, (2*data[128])**3
    assert negative_num * 50**128 < negative_den * 49**128
    positive_num, positive_den = (2*data[129])**4, (21*data[172])**3
    assert positive_num * 20**172 > positive_den * 21**172
    # Phase-gap certificate: exp(P(0)) > 2.28, while exp(P(t)) < 2.25
    # on t in [1/4,1/2]. The associated real x interval lies in [152,182].
    assert 2*data[128]*25**128 > 57**128
    assert 19**4 < 2*16**4  # 152 < 128 * fourth_root(2)
    assert 128**2 * 2 < 182**2
    for n in range(152,183):
        assert 21*data[n]*4**n < 9**n, ("phase gap",n)
    bands = {}
    for N in (32,64,100):
        entries = {}
        for name,c,is_max in (("rho_min_lower",2,False),
                              ("rho_min_upper",21,False),
                              ("rho_max_lower",2,True),
                              ("rho_max_upper",21,True)):
            n = extremum(data,N,c,is_max)
            entries[name] = {"index": n, "factor": c,
                            **rational_root_enclosure(c*data[n],n)}
        bands[str(N)] = entries
    # Independent finite checks, not just consistency checks on the table.
    dp = []
    for n in range(max_n+1):
        start = time.perf_counter()
        value, states = count_avoiding(n)
        assert value == data[n], ("independent DP",n,value,data[n])
        dp.append({"n": n, "count": str(value), "states": states,
                   "seconds": round(time.perf_counter()-start,6)})
    for n in range(9):
        assert brute_force(n) == data[n], ("brute force",n)
    return {
        "status": "all executed checks passed",
        "data_scope": "OEIS A003407, 0..200; independent DP only through stated limit",
        "independent_dp_max_n": max_n,
        "brute_force_max_n": 8,
        "recurrence_inequalities_checked": 199,
        "exact_integer_certificates": {
            "Ho_64_75_separation": True,
            "Ho_128_162_separation": True,
            "loss_R_less_than_(49_over_50)^128": True,
            "gain_R_greater_than_(21_over_20)^172": True,
            "phase_zero_growth_greater_than_57_over_25": True,
            "31_phase_band_bounds_less_than_9_over_4": True,
            "phase_interval_containment": True},
        "bands": bands,
        "independent_dp": dp}


def main() -> None:
    if not __debug__:
        raise RuntimeError("Run without -O: exact certificate assertions must be enabled")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n",type=int,default=32,
                        help="independent DP endpoint, 0..36 (default 32)")
    parser.add_argument("--output",type=Path,default=ROOT/"verification.json")
    args = parser.parse_args()
    if not 0 <= args.max_n <= 36:
        parser.error("--max-n must be between 0 and 36")
    result = verify(args.max_n)
    args.output.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(result["status"])
    print(f"Independent DP: n=0..{args.max_n}; brute force: n=0..8")
    print("Gluing, nonconstancy, exact-period certificates and three endpoint bands checked.")
    print(f"Detailed record: {args.output}")

if __name__ == "__main__":
    main()
