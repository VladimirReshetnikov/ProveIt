"""Finite witnesses for the all-size lacunary-current obstruction."""
import json
from math import comb, isqrt


def square_current(m):
    return m if m and isqrt(abs(m)) ** 2 == abs(m) else 0


def check(limit=64):
    result = []
    for H in range(limit + 1):
        n = (H + 1) ** 2
        difference = sum((-1) ** j * comb(H, j) * square_current(n - j)
                         for j in range(H + 1))
        if difference != n:
            raise ArithmeticError("finite-pole nonlocality witness failed")
        result.append({"pole_order": H, "witness_index": n, "coefficient": difference})
    return {"status": "PASS", "scope": "witnesses; the uniform proof is in ANTHROPIC_REVIEW.md",
            "witnesses": result}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
