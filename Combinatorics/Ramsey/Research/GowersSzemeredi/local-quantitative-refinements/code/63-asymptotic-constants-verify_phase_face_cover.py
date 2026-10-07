"""Exact rational checks of the face-cover theorem (not a proof)."""
from fractions import Fraction as F
from itertools import product
from math import factorial, comb
import json
from pathlib import Path


def check():
    cases = []
    for k in range(1, 5):
        for h in (1, 2, 3):
            for w in sorted({F(1), F(h), F(2 * h - 1, 2)}):
                if not 0 < w <= h:
                    continue
                points = list(product(range(-h, h + 1), repeat=k))
                beta = [w ** j * F(factorial(k - j + 2), factorial(k + 2))
                        for j in range(k + 1)]
                weights = {}
                for c in points:
                    boundary_count = sum(abs(x) == h for x in c)
                    weights[c] = sum(
                        comb(boundary_count, j) * beta[j]
                        / 2 ** (boundary_count - j)
                        for j in range(boundary_count + 1)
                    )
                total = sum(weights.values())
                stated_total = sum(
                    comb(k, j) * 2 ** j * (2 * h) ** (k - j) * beta[j]
                    for j in range(k + 1)
                )
                assert total == stated_total
                kappa = F(2 ** (k + 1), factorial(k + 2)) * w ** (k + 2)
                offsets = [d for d in product(range(-int(w) - 1, int(w) + 2), repeat=k)
                           if sum(abs(x) for x in d) < w]
                minimum = None
                for a in points:
                    convolution = F(0)
                    for d in offsets:
                        center = tuple(a[i] - d[i] for i in range(k))
                        if center in weights:
                            convolution += weights[center] * (w - sum(abs(x) for x in d)) ** 2
                    assert convolution >= kappa, (k, h, w, a, convolution, kappa)
                    if minimum is None or convolution < minimum:
                        minimum = convolution
                cases.append({
                    "k": k, "h": h, "w": str(w), "targets": len(points),
                    "total": str(total), "kappa": str(kappa),
                    "minimum_convolution": str(minimum),
                })

    constants = []
    for k in [1, 2, 3, 4, 5, 8, 10, 20, 50, 100]:
        new = sum(F(comb(k, j)) * F(2, 3 * k) ** j
                  * F(factorial(k - j + 2), factorial(k + 2))
                  for j in range(k + 1))
        old = sum(F(comb(k, j)) * F(2, 3 * k) ** j * F(2, factorial(j + 2))
                  for j in range(k + 1))
        assert new <= old
        constants.append({"k": k, "D_face": str(new), "D_previous": str(old),
                          "fraction_of_ceiling": float(1 / new)})
    return {"arithmetic": "exact rational, except decimal presentation",
            "cover_cases": cases,
            "cover_target_checks": sum(c["targets"] for c in cases),
            "constant_comparisons": constants}


if __name__ == "__main__":
    result = check()
    destination = Path(__file__).resolve().parents[1] / "data" / "verify_phase_face_cover.json"
    destination.parent.mkdir(exist_ok=True)
    destination.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Verified {len(result['cover_cases'])} cases and "
          f"{result['cover_target_checks']} lattice target points; wrote {destination}")
