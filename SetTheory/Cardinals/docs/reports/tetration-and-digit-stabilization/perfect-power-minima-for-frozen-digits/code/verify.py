#!/usr/bin/env python3
"""Independent exact checks and all finite certificates used by the proof."""
from __future__ import annotations
import csv
from fractions import Fraction
from functools import lru_cache
import json
from pathlib import Path
import platform
import sys
import time
from tetration_minima import (
    valuation, c2, c5, speed, speed_of_power, restricted_minimum,
    minimum_root, rho, strict_minimum_root, strict_rho, idempotent_tail, predicted_tail,
    minus_one_roots5, nonfive_lower_bound, write_root_table,
)

HERE = Path(__file__).resolve().parent
DATA = HERE.parent / "data"


def reference_piecewise_speed(a: int) -> int:
    """Independent transcription of the formula in MO question 487698.

    Attribution: Marco Ripa, MathOverflow, February 2025; underlying
    congruence-speed formula: Notes Number Theory Discrete Math. 27 (2021).
    """
    if a in (0, 1): return 0
    if a % 10 == 0: raise ValueError("base divisible by ten")
    d, e = a % 10, a % 100
    if e == 1: return min(valuation(a-1, 2), valuation(a-1, 5))
    if e == 51: return min(valuation(a+1, 2), valuation(a-1, 5))
    if d in (2, 8): return valuation(a*a+1, 5)
    if e in (7, 43): return min(valuation(a+1, 2), valuation(a*a+1, 5))
    if e in (57, 93): return min(valuation(a-1, 2), valuation(a*a+1, 5))
    if d == 4: return valuation(a+1, 5)
    if d == 5: return valuation(a*a-1, 2)-1
    if d == 6: return valuation(a-1, 5)
    if e == 49: return min(valuation(a-1, 2), valuation(a+1, 5))
    if e == 99: return min(valuation(a+1, 2), valuation(a+1, 5))
    return 1


def literal_minimum(n: int, cap: int) -> int:
    """Brute-force search using actual powers and the published formula."""
    for x in range(2, cap+1):
        if x % 10 and reference_piecewise_speed(pow(x, n)) == n:
            return x
    raise AssertionError(f"no solution for n={n}, cap={cap}")


def is_perfect_power(x: int) -> bool:
    """Independent exact test by binary integer roots; x > 1."""
    if x < 4: return False
    for exponent in range(2, x.bit_length()):
        lo, hi = 2, 1 << ((x.bit_length()+exponent-1)//exponent)
        while lo <= hi:
            mid = (lo+hi)//2
            value = pow(mid, exponent)
            if value == x: return True
            if value < x: lo=mid+1
            else: hi=mid-1
    return False


@lru_cache(maxsize=None)
def phi25(m: int) -> int:
    """Euler phi for a modulus whose only possible primes are 2 and 5."""
    if m == 1: return 1
    answer, residual = m, m
    for p in (2, 5):
        if residual % p == 0:
            answer = answer // p * (p-1)
            while residual % p == 0: residual //= p
    if residual != 1: raise ValueError("unsupported prime divisor")
    return answer


@lru_cache(maxsize=None)
def tower_capped(a: int, h: int, cap: int) -> int:
    """min(T_h(a), cap), without computing a value above cap."""
    if cap <= 1: return cap
    if h == 0: return 1
    threshold, q = 0, 1
    while q < cap:
        q *= a
        threshold += 1
    exponent = tower_capped(a, h-1, threshold)
    if exponent >= threshold: return cap
    return min(pow(a, exponent), cap)


@lru_cache(maxsize=None)
def tower_mod(a: int, h: int, modulus: int) -> int:
    """Power tower by Euler reduction plus a proven large-exponent flag."""
    if modulus == 1: return 0
    if h == 0: return 1 % modulus
    period = phi25(modulus)
    exponent = tower_mod(a, h-1, period)
    if tower_capped(a, h-1, period) >= period:
        exponent += period
    return pow(a, exponent, modulus)


def tail_density(exponent: int, threshold: int) -> Fraction:
    s = threshold - valuation(exponent, 2)
    t = threshold - valuation(exponent, 5)
    if s < 2 or t < 1: raise ValueError("outside stated theorem")
    return (Fraction(2, 5*(1 << s)) + Fraction(2, 5**t)
            + Fraction(8, (1 << s)*5**t))


def main() -> None:
    started = time.monotonic()
    DATA.mkdir(exist_ok=True)
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    report: dict[str, object] = {"python": platform.python_version(), "checks": {}}
    checks = report["checks"]
    assert isinstance(checks, dict)

    count = 0
    for a in range(2, 20001):
        if a % 10:
            assert speed(a) == reference_piecewise_speed(a), a
            count += 1
    checks["compact_vs_published_formula_bases_2_to_20000"] = count

    count = 0
    for x in range(2, 501):
        if x % 10:
            for n in range(1, 31):
                assert speed_of_power(x, n) == reference_piecewise_speed(pow(x, n)), (x, n)
                count += 1
    checks["power_transfer_vs_actual_integer_powers"] = count

    brute = []
    for n in range(1, 21):
        r = minimum_root(n)
        got = literal_minimum(n, r)
        assert got == r, (n, got, r)
        brute.append({"n": n, "root": r, "integers_in_search_interval": r-1})
    report["literal_minimum_checks"] = brute
    checks["exhaustive_minimum_indices"] = "1 through 20 inclusive"

    strict_results=[]
    for n in range(1,16):
        cap=strict_minimum_root(n)
        for x in range(2,cap+1):
            if x%10 and reference_piecewise_speed(pow(x,n))==n and not is_perfect_power(x):
                assert x==cap, (n,x,cap)
                strict_results.append({"n":n,"root":x})
                break
        else: raise AssertionError((n,"strict minimum missing"))
    assert strict_rho(3)==166375
    for s in range(2,201):
        assert is_perfect_power(restricted_minimum(s)) == (s==3), s
    checks["restricted_roots_perfect_power_test_s_2_through_200"] = True
    report["strict_minimum_exhaustive_checks"] = strict_results

    small = []
    exceptions = []
    for n in range(3, 25):
        s, t = n-valuation(n,2), n-valuation(n,5)
        r = minimum_root(n)
        margin = 5**t-r*r-1
        small.append({"n":n,"s":s,"t":t,"root":r,"barrier_margin":margin,
                      "floor_ratio":5**t//(r*r+1)})
        if margin <= 0: exceptions.append(n)
    assert exceptions == [3,5,7,9,10,15]
    report["small_range_barrier"] = small

    certs = []
    for n,k in [(3,3),(5,4),(7,5),(9,7),(10,7),(15,8)]:
        r, other = minus_one_roots5(k)
        modulus = 5**k
        target = minimum_root(n)
        assert k <= n-valuation(n,5)
        assert (r*r+1)%modulus == 0 and (other*other+1)%modulus == 0
        assert r > target and modulus-1 > target
        certs.append({"n":n,"k":k,"modulus":modulus,"minimum_root":target,
                      "smaller_square_root_minus_one":r,"other_square_root":other,
                      "certificate_quotient":(r*r+1)//modulus})
    report["finite_hensel_certificates"] = certs

    margin25 = 5**25 - 25*((3*2**25+1)**2+1)
    assert margin25 > 0
    report["uniform_bound_base_case_margin"] = margin25
    for n in range(3, 10001):
        r = minimum_root(n)
        assert r%10 == 5
        assert speed_of_power(r,n) == n
    checks["formula_admissibility_indices"] = "3 through 10000 inclusive"

    expected50 = [2,7,25,5,95,95,385,95,1535,1535,6145,1025,24575,24575,
                  98305,4095,393215,393215,1572865,262145,6291455,6291455,
                  25165825,6291455,100663295,100663295,402653185,67108865,
                  1610612735,1610612735,6442450945,402653185,25769803775,
                  25769803775,103079215105,17179869185,412316860415,
                  412316860415,1649267441665,412316860415,6597069766655,
                  6597069766655,26388279066625,4398046511105,105553116266495,
                  105553116266495,422212465065985,17592186044415,
                  1688849860263935,1688849860263935]
    assert [minimum_root(n) for n in range(1,51)] == expected50
    checks["agreement_with_Alekseyev_50_term_list"] = True

    assert idempotent_tail(10) == 8212890625
    for n in range(3, 2001):
        for d in sorted({1, min(n,10), min(n,30)}):
            assert pow(minimum_root(n),n,10**d) == predicted_tail(n,d), (n,d)
    checks["decimal_tail_indices"] = "3 through 2000 inclusive; d=1,min(n,10),min(n,30)"

    raw_count = 0
    for a,maxh in [(2,5),(3,3),(4,3),(5,3),(6,3)]:
        value = 1
        for h in range(maxh+1):
            if h: value = pow(a,value)
            for digits in (1,3,12,40):
                assert tower_mod(a,h,10**digits) == value%(10**digits)
                raw_count += 1
    checks["tower_mod_vs_literal_towers"] = raw_count

    tower_rows = []
    for a in (2,3,4,5,6,7,8,9,11,15,25,49,51,95,125,807,1001):
        digits = 160
        residues = [tower_mod(a,h,10**digits) for h in range(15)]
        ds=[]
        for h in range(14):
            difference = (residues[h+1]-residues[h])%(10**digits)
            assert difference != 0, (a,h,"precision exhausted")
            ds.append(min(valuation(difference,2),valuation(difference,5)))
        slopes=[ds[h]-ds[h-1] for h in range(1,len(ds))]
        assert slopes[-4:] == [speed(a)]*4, (a,ds,slopes)
        tower_rows.append({"base":a,"predicted_speed":speed(a),"d_0_through_d_13":ds})
    report["independent_modular_tower_checks"] = tower_rows

    density_rows=[]
    for k,m in [(1,2),(1,3),(2,3),(5,3),(10,4),(4,4)]:
        s,t=m-valuation(k,2),m-valuation(k,5)
        period=(1<<s)*5**t
        actual=sum(1 for x in range(2,period+2) if x%10 and speed_of_power(x,k)>=m)
        expected=tail_density(k,m)
        # Use representatives 2..period+1: x=period+1 represents the
        # admissible class 1, whereas x=1 itself is an isolated exception.
        assert Fraction(actual,period) == expected, (k,m,actual,period,expected)
        density_rows.append({"exponent":k,"threshold":m,"period":period,
                             "count":actual,"density":str(expected)})
    report["density_checks"] = density_rows

    write_root_table(DATA/"minimum_roots_1_1000.csv",1000)
    with (DATA/"rho_1_50.txt").open("w",encoding="utf-8") as f:
        f.write("# n rho(n)\n")
        for n in range(1,51): f.write(f"{n} {rho(n)}\n")
    with (DATA/"finite_certificates.csv").open("w",newline="",encoding="utf-8") as f:
        w=csv.DictWriter(f,fieldnames=list(certs[0]))
        w.writeheader();w.writerows(certs)
    with (DATA/"small_range.csv").open("w",newline="",encoding="utf-8") as f:
        w=csv.DictWriter(f,fieldnames=list(small[0]))
        w.writeheader();w.writerows(small)
    report["elapsed_seconds"] = round(time.monotonic()-started,3)
    report["status"] = "ALL CHECKS PASSED"
    (DATA/"verification.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(report,indent=2))


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Verification requires assertions; do not use python -O or PYTHONOPTIMIZE.")
    main()
