#!/usr/bin/env python3
"""Additional exact checks for the finite shape and closed profile theorems."""
from fractions import Fraction
from pathlib import Path
import json
from anchor_selection import (class_loss, choose, first_mode, affine_first_mode,
                              balanced_minimax_profile, minimax_profile)


def main() -> None:
    checks = dict(closed_profile_comparisons=0, marginal_shape_cases=0,
                  second_difference_identities=0, affine_quadratic_caps=0)
    for m in range(1, 14):
        for r in range(m+1):
            for t in range(1, 7):
                vals = [class_loss(m, r, t, s) for s in range(m+1)]
                a = vals.index(max(vals))
                assert all(vals[s+1] >= vals[s] for s in range(a))
                assert all(vals[s+1] <= vals[s] for s in range(a, m))
                assert all(vals[s+2]-2*vals[s+1]+vals[s] <= 0
                           for s in range(a-1))
                checks['marginal_shape_cases'] += 1
                for q in range(1, 5):
                    v, _ = balanced_minimax_profile(m, q, r, t)
                    w, _ = minimax_profile(m, q, r, t)
                    assert v == w, (m, q, r, t, v, w)
                    checks['closed_profile_comparisons'] += 1
                if 1 <= t <= r < m:
                    pref = Fraction(r*(m-r), m*m*(m-1)*choose(m-2,r-1))
                    for s in range(m-1):
                        actual = vals[s+2]-2*vals[s+1]+vals[s]
                        expected = pref*(t*choose(s,t)*choose(m-s-2,r-t-1)
                            -(t+1)*choose(s,t-1)*choose(m-s-2,r-t))
                        assert actual == expected, (m,r,t,s)
                        if r > t:
                            factor = Fraction(choose(s,t-1)*choose(m-s-2,r-t-1),r-t)
                            factored = pref*factor*((r+1)*(s+2)-(t+1)*(m+1))
                            assert actual == factored, (m,r,t,s)
                        checks['second_difference_identities'] += 1
    for m in range(1, 65):
        for r in range(m+1):
            assert affine_first_mode(m,r) == first_mode(m,r,2), (m,r)
            checks['affine_quadratic_caps'] += 1
    report = {'status':'all checks passed',
              'arithmetic':'exact Python integers, integer square root, Fraction',
              'checks':checks,'total_checked_cases':sum(checks.values()),
              'scope':'Finite tests supplement the general mathematical proofs; no Lean verification.'}
    destination = Path(__file__).resolve().parents[1]/'certificates'/'balanced_verification.json'
    destination.parent.mkdir(parents=True,exist_ok=True)
    destination.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__ == '__main__':
    main()
