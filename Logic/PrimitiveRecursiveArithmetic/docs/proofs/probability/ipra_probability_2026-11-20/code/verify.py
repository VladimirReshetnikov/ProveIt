"""Reproduce exact finite checks. These checks are not universal proofs."""
import json
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
from probability_kernel import (
    Cylinder, cantor_prefix, uniform_midpoints, independent_pair,
    normal_cdf_at_one, smooth_step, wlln_sample_size,
    strong_sample_size, clt_sample_size,
)


def run():
    counts = {}

    def check(group, claim):
        if not claim:
            raise AssertionError(group)
        counts[group] = counts.get(group, 0)+1

    for m in range(1, 7):
        u, c = uniform_midpoints(m), cantor_prefix(m)
        check("uniform_moments", u.expectation() == Q(1, 2))
        check("uniform_moments", u.map(lambda x: (x-Q(1, 2))**2).expectation()
              == (1-Q(1, 4**m))/12)
        check("cantor_moments", c.expectation() == (1-Q(1, 3**m))/2)
        for n in range(m, 8):
            check("uniform_refinement", u.d1(uniform_midpoints(n)) <= Q(1, 2**(m+1)))
            check("cantor_refinement", c.d1(cantor_prefix(n)) <= Q(1, 3**m))

    f = Cylinder(4, tuple(Q(i*i-7*i+2, 5) for i in range(16)))
    g = Cylinder(3, tuple(Q((-1)**i*i, 3) for i in range(8)))
    for n in range(6):
        cf = f.conditional(n)
        check("conditional_expectation", cf.expectation() == f.expectation())
        check("conditional_expectation", cf.d1(g.conditional(n)) <= f.d1(g))
        for m in range(6):
            check("tower", cf.conditional(m).d1(f.conditional(min(m, n))) == 0)

    x, y = independent_pair(uniform_midpoints(3), cantor_prefix(2))
    check("independence", x.combine(y, lambda a,b:a*b).expectation()
          == x.expectation()*y.expectation())
    xa, ya = independent_pair(uniform_midpoints(2), cantor_prefix(1))
    check("independence", xa.d1(x) <= Q(1, 8))
    check("independence", ya.d1(y) <= Q(1, 3))

    grid = [Q(i, 4) for i in range(-12, 13)]
    for k in [Q(0), Q(1, 2), Q(1), Q(2)]:
        for a,b in product(grid, repeat=2):
            upper = max(1, 2*k)*min(1, abs(a-b)) + max(0, abs(a)-k) + max(0, abs(b)-k)
            check("clipping_bound", abs(a-b) <= upper)

    # Exact random-walk tables audit the finite first-crossing inequality.
    for n in range(1, 9):
        outcomes = list(product([-1, 1], repeat=n))
        for threshold in range(1, 5):
            bad = 0
            for increments in outcomes:
                total = 0
                crossed = False
                for increment in increments:
                    total += increment
                    crossed = crossed or abs(total) >= threshold
                bad += int(crossed)
            check("kolmogorov_finite", threshold**2 * Q(bad, 2**n) <= n)

    for j in range(101):
        u = Q(j, 100)
        check("smoothing_polynomial", 0 <= smooth_step(u) <= 1)
        third = -60+360*u-360*u*u
        check("smoothing_polynomial", third == 30-360*(u-Q(1,2))**2)
        check("smoothing_polynomial", abs(third) <= 60)

    enclosures = normal_cdf_at_one()
    zlo,zhi = enclosures["Z"]
    plo,phi = enclosures["Phi1"]
    check("normal_enclosure", Q(5,2) < zlo <= zhi < Q(251,100))
    check("normal_enclosure", Q(841,1000) < plo <= phi < Q(842,1000))

    budgets = {
        "WLLN_V1_eps1over10_delta1over20": wlln_sample_size(1,Q(1,10),Q(1,20)),
        "strong_V1_eps1over10_delta1over20": strong_sample_size(1,Q(1,10),Q(1,20)),
        "CLT_B2_delta1over10": clt_sample_size(2,Q(1,10)),
    }
    check("budgets", budgets["WLLN_V1_eps1over10_delta1over20"] == 2000)
    check("budgets", budgets["strong_V1_eps1over10_delta1over20"] == 8000)
    check("budgets", budgets["CLT_B2_delta1over10"] == 40960000000000)
    return {"status":"pass", "arithmetic":"integers and fractions only",
            "scope":"finite regression and certificate checks; not universal proofs",
            "checks":counts,"total_checks":sum(counts.values()),
            "normal_intervals":{k:list(map(str,v)) for k,v in enclosures.items()},
            "sample_size_examples":budgets}


if __name__ == "__main__":
    result = run()
    target = Path(__file__).resolve().parents[1]/"validation"/"exact_checks.json"
    target.parent.mkdir(exist_ok=True)
    target.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))
