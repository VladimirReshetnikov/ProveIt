#!/usr/bin/env python3
"""Apply both rectangular backends fairly to the prior three-plan portfolios."""
from fractions import Fraction as F
import argparse
import json
from pathlib import Path
from adaptive_rectangular import data, supports, dot
from schedules import bound_schedule, fixed_beta2


def uniform_three_beta(n, plans, backend):
    menus = [supports(n, p, backend) for p in plans]
    norms = [[dot(v, v) for v in a] for a in menus]
    ab = [[2*dot(v, w) for w in menus[1]] for v in menus[0]]
    ac = [[2*dot(v, w) for w in menus[2]] for v in menus[0]]
    bc = [[2*dot(v, w) for w in menus[2]] for v in menus[1]]
    maximum = total = count = 0
    witness = None
    for i in range(len(menus[0])):
        for j in range(len(menus[1])):
            base = norms[0][i] + norms[1][j] + ab[i][j]
            for k in range(len(menus[2])):
                value = base + norms[2][k] + ac[i][k] + bc[j][k]
                if value > maximum:
                    maximum, witness = value, (i, j, k)
                total += value
                count += 1
    beta2 = F(2*maximum, backend["denominator"]**2 * 9 * n*n)
    return beta2, {"r": n, "Q": maximum, "beta_squared": str(beta2),
                   "tuples": count, "norm_sum": total, "witness": witness}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = data()
    answer = {"status": "PASS", "comparisons": {}}
    for name, backend in payload["backends"].items():
        beta2 = {r: fixed_beta2(r, backend) for r in (3, 4, 5, 6, 7, 8)}
        certs = []
        for r in (9, 13):
            beta2[r], record = uniform_three_beta(r, payload["prior_menus"][str(r)], backend)
            certs.append(record)
        original, _, _ = bound_schedule(
            [9, 13], [F(63, 4000), F(9, 800)], 7, F(77, 16200), F(4, 9),
            beta2, F(backend["epsilon"]))
        retuned, _, _ = bound_schedule(
            [9, 13, 8, 6, 5, 4, 4, 4],
            [F(1577,100000), F(9,800), F(631,100000), F(107,20000),
             F(219,50000), F(171,50000), F(43,20000), F(17,12500)],
            3, F(30107,10000000), F(77,100), beta2, F(backend["epsilon"]))
        answer["comparisons"][name] = {
            "prior_menu_support_certificates": certs,
            "published_prior_schedule_with_updated_backend": original,
            "prior_menus_with_new_multistage_tail": retuned,
            "scope": "Explicit compatible compositions, not an optimum over all prior methods.",
        }
    encoded = json.dumps(answer, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
