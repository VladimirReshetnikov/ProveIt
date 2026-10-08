"""Small exact polynomial checks for the finite Jones-evaluation menu."""
from itertools import product
import json
from pathlib import Path


def trim(poly):
    out = list(poly)
    while out and not out[-1]:
        out.pop()
    return out


def multiply(left, right):
    if not left or not right:
        return []
    out = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i + j] += a * b
    return trim(out)


def quadratic(q):
    return [1, 2 - q, 1]


def remainder(poly, monic):
    out = trim(poly)
    while len(out) >= len(monic):
        offset, leading = len(out) - len(monic), out[-1]
        for i, coefficient in enumerate(monic):
            out[offset + i] -= leading * coefficient
        out = trim(out)
    return out


def main():
    exhausted = products = intervals = 0
    for coefficients in product((-1, 0, 1), repeat=5):
        # t^2(V-1), with V supported on degrees -2,...,2.
        p = list(coefficients)
        p[2] -= 1
        menu_equal = all(not remainder(p, quadratic(q)) for q in range(5, 8))
        assert menu_equal == (coefficients == (0, 0, 1, 0, 0))
        exhausted += 1
    for n in range(1, 21):
        p = [1]
        for q in range(5, 2 * n + 5):
            p = multiply(p, quadratic(q))
        assert len(p) - 1 == 4 * n
        assert all(not remainder(p, quadratic(q)) for q in range(5, 2 * n + 5))
        assert remainder(p, quadratic(2 * n + 5))
        products += 1
    for n in range(101):
        for writhe in range(-n, n + 1, 2):
            lower = -((-3 * (writhe - n)) // 4)
            upper = 3 * (writhe + n) // 4
            width = upper - lower
            assert lower <= 0 <= upper
            assert width <= 3 * n // 2
            count = width // 2 + 1
            assert 2 * count > width
            assert count <= 3 * n // 4 + 1
            intervals += 1
    result = {"status": "PASS", "small_laurent_polynomials": exhausted,
              "degree_counting_products": products, "refined_writhe_intervals": intervals,
              "scope": "Polynomial identities, not a production Jones menu or knot decisions"}
    Path(__file__).with_name("jones_finite_menu_checks.json").write_text(
        json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
