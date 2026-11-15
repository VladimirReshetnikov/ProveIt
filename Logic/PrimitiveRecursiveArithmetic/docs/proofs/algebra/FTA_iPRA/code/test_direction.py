"""Exact finite examples for direction.py; these are checks, not a proof."""
from fractions import Fraction as F
import json
from time import perf_counter
from direction import check_direction, direction


def run_tests():
    # Real axes, all four quadrants, multiple exponents, nonrational moduli.
    cases = [
        ((F(1), F(0)), 1),
        ((F(-1), F(0)), 1),
        ((F(1), F(1)), 2),
        ((F(-1), F(1)), 2),
        ((F(-1), F(-1)), 3),
        ((F(1), F(-1)), 3),
        ((F(3, 7), F(-4, 11)), 5),
    ]
    output = []
    for c, k in cases:
        started = perf_counter()
        w = direction(c, k)
        good = check_direction(c, k, w)
        assert good
        item = {"target": [str(c[0]), str(c[1])], "exponent": k,
                "exact_certificate": good,
                "seconds": round(perf_counter() - started, 3)}
        output.append(item)
        print(json.dumps(item), flush=True)
    return output


if __name__ == "__main__":
    results = run_tests()
    with open("direction_test_results.json", "w", encoding="utf-8") as output:
        json.dump({"status": "all_passed",
                   "scope": "Finite exact-rational examples; these checks do not replace the general proof.",
                   "certificate": "norm2(w) <= 1 and d >= 0 and (b <= 0 or d*d >= b*b*A), where A=norm2(c), b=norm2(w^k)+1-eps^2, d=2*Re(w^k*conj(c)), eps=1/16",
                   "cases": results}, output, indent=2)
        output.write("\n")
