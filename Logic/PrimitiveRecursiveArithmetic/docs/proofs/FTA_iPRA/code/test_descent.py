"""Finite exact checks of the reference local lemma; not a proof of FTA."""
import json
from fractions import Fraction as F
from descent import descent, concise_result


def main():
    cases = [
        ("linear", [(-1, 0), (1, 0)], (0, 0)),
        ("quadratic", [(1, 0), (0, 0), (1, 0)], (0, 0)),
        ("zero leading coefficient", [(1, 0), (0, 1), (0, 0)], (0, 0)),
        ("already a root", [(0, 0), (1, 1), (1, 0)], (0, 0)),
        ("translated input", [(1, 1), (2, -1), (0, 0)], (1, -1)),
        ("last possible plateau center", [(1, 0), (F(1, 1024), 0),
                                         (F(1, 8), 0), (1, 0)], (0, 0)),
    ]
    results = []
    for label, coefficients, start in cases:
        result = {"case": label, **concise_result(descent(coefficients, start))}
        results.append(result)
        print(json.dumps(result), flush=True)
    with open("descent_test_results.json", "w", encoding="utf-8") as output:
        json.dump({"arithmetic": "exact fractions; no floating point",
                   "scope": "local descent checks only", "cases": results}, output, indent=2)
        output.write("\n")


if __name__ == "__main__":
    main()
