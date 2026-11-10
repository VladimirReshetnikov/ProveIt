"""Finite exact-definition checks, not a formal arithmetic proof.

Run from any directory with Python 3.10+:
    python3 tests/check_arithmetic.py

All construction values come from code/arithmetic_model.py.  Host arithmetic
appears only in independent expected values and bounded test enumeration.
There is no semantic shortcut replacing Pred, V, K, or I during evaluation.
"""

import json
import sys
from pathlib import Path
from time import perf_counter

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "code"))
import arithmetic_model as a


def main() -> dict:
    started = perf_counter()
    checks: dict[str, int] = {}

    def equal(group, actual, expected, witness):
        if actual != expected:
            raise AssertionError(f"{group} failed at {witness}: {actual} != {expected}")
        checks[group] = checks.get(group, 0) + 1

    for n in range(9):
        equal("successor_and_shifted_selector", a.S(n), n + 1, n)
        for x in range(3):
            for y in range(3):
                equal("successor_and_shifted_selector", a.C(n, x, y), x + 1 if n == 0 else y, (n,x,y))
        equal("finite_swap", a.pulse(n), 2 if n == 0 else 1 if n == 1 else 0, n)
        equal("finite_swap", a.one_indicator(n), int(n == 1), n)
        equal("finite_swap", a.J(n), 1 if n == 0 else 0 if n == 1 else n, n)
        equal("finite_swap", a.J(a.J(n)), n, n)

    updates = [a.S, a.Z, a.twice_successor, a.parameter_update(0), a.parameter_update(2)]
    for h_index, h in enumerate(updates):
        value = 0
        for n in range(7):
            equal("zero_iteration", a.K(n,h), value, (h_index,n))
            equal("zero_iteration", a.K(n+1,h), h(a.K(n,h)), (h_index,n,"step"))
            value = h(value)

    for n in range(9):
        equal("affine_terms", a.d(n), 2*n, n)
        equal("affine_terms", a.D(n), 2*n+1, n)
        equal("affine_terms", a.A3(n), 3*n+2, n)
        equal("parity_and_ramp", a.even(n), int(n % 2 == 0), n)
        equal("parity_and_ramp", a.M(n), n % 3, n)
        equal("parity_and_ramp", a.F(n), (3*n)//2, n)
        equal("parity_and_ramp", a.M(a.F(n)), a.N(n), (n,"invariant"))
        equal("parity_and_ramp", a.F(a.S(a.S(n))), a.S(a.S(a.S(a.F(n)))) , (n,"shift"))
        equal("parity_and_ramp", a.S(a.F(a.D(n))), a.A3(n), (n,"odd_affine"))
        equal("parity_and_ramp", a.F(a.A3(n)), a.T(a.A3(a.F(n)),a.N(n)), (n,"triple_affine"))
        equal("H_affine", a.H(a.D(n)), a.A3(n), (n,"odd"))
        equal("H_affine", a.H(a.A3(n)), a.A3(a.H(n)), (n,"commute"))
        for m in range(5):
            equal("affine_terms", a.T(n,m), n+m+1, (n,m))
    equal("H_affine",a.H(0),0,"zero")

    for x in range(4):
        equal("strict_comparator",a.E(x),2**x-1,(x,"power"))
        equal("strict_comparator",a.V(x,0),0,(x,"zero"))
        for y in range(5):
            equal("strict_comparator",a.V(x,y),int(x<y),(x,y,"meaning"))
    for y in range(4):
        equal("strict_comparator",a.V(0,y+1),1,(0,y+1,"positive"))
        for x in range(3):
            equal("strict_comparator",a.V(x+1,y+1),a.V(x,y),(x,y,"diagonal"))
            equal("strict_comparator",a.R(y+1,a.d(a.E(x+1)),a.H),a.A3(a.R(y,a.d(a.E(x)),a.H)),(x,y,"orbit_affine"))

    for m in range(4):
        for t in range(4):
            equal("saturation",a.W(t,m),min(t,m),(t,m,"meaning"))
            equal("saturation",a.W(t+1,m+1),a.S(a.W(t,m)),(t,m,"shift"))
        equal("saturation",a.W(m,m),m,(m,"diagonal"))
        equal("saturation",a.W(m+1,m),m,(m,"extra"))
    for n in range(5):
        equal("predecessor",a.Pred(n),max(0,n-1),n)
    for n in range(4):
        equal("predecessor",a.Pred(a.S(n)),n,(n,"successor"))

    # These updates keep their outputs at most 3, so the exact predecessor
    # expansion remains small. D is additionally tested through two steps.
    iterator_updates = [a.Z, a.parameter_update(0), a.parameter_update(1), a.parameter_update(2)]
    for h_index,h in enumerate(iterator_updates):
        for seed in range(3):
            value=seed
            for n in range(4):
                equal("initialized_iteration",a.I(n,seed,h),value,(h_index,seed,n))
                if n < 3:
                    equal("initialized_iteration",a.I(n+1,seed,h),h(a.I(n,seed,h)),(h_index,seed,n,"step"))
                value=h(value)
    for n,expected in enumerate([0,1,3]):
        equal("initialized_iteration",a.I(n,0,a.D),expected,("D",n))

    return {
        "status":"PASS",
        "scope":"finite evaluation of exact R expressions in the standard natural numbers; not a formal proof",
        "arithmetic_shortcuts":False,
        "checks":checks,
        "total_checks":sum(checks.values()),
        "seconds":round(perf_counter()-started,3),
        "cache_entries":a.cache_sizes(),
    }


if __name__ == "__main__":
    print(json.dumps(main(),indent=2,sort_keys=True))
