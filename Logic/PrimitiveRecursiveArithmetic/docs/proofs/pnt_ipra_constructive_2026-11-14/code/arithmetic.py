"""Executable arithmetic definitions for the PNT/iPRA research package.

All loops below are explicitly bounded.  These programs implement the
definitions, not a proof of the universal prime number theorem.
"""

from fractions import Fraction
from math import factorial


def prime(n: int) -> bool:
    """Bounded trial-division definition, including the cases 0 and 1."""
    return n >= 2 and all(n % d != 0 for d in range(2, n))


def prime_count(n: int) -> int:
    return sum(prime(j) for j in range(n + 1))


def nat_distance(a: int, b: int) -> int:
    return max(a - b, 0) + max(b - a, 0)


def denominator(n: int) -> int:
    return factorial(n * n)


def logarithm_numerator(n: int) -> int:
    """D(n) times H_(n^2)-H_n; n=0 is assigned the value zero."""
    d = denominator(n)
    return sum(d // j for j in range(n + 1, n * n + 1))


def logarithm_lower(n: int) -> Fraction:
    """For n>=1 this lies between log(n)-1/n and log(n)."""
    return sum((Fraction(1, j) for j in range(n + 1, n * n + 1)), Fraction())


def pnt_matrix(k: int, n: int) -> bool:
    """The quantifier-free matrix k*|pi(n) A(n)-n D(n)| <= n D(n)."""
    d = denominator(n)
    a = logarithm_numerator(n)
    return k * nat_distance(prime_count(n) * a, n * d) <= n * d


def contraction_parameters(q: int) -> dict[str, int]:
    """Integer descriptions of the finite envelope iteration; q>=1."""
    if q < 1:
        raise ValueError("q must be positive")
    d = (1 << 20) * q**3
    return {"q": q, "D": d, "H": (1 << 10) * q,
            "J": 4 * d - d // q, "Cs": 1 << 18}


def threshold_step(t: int, q: int) -> int:
    p = contraction_parameters(q)
    return 16 * (t + p["H"]) + p["D"] * (16 * t + p["Cs"]) + 1


def modulus_description(k: int) -> dict[str, int | str]:
    """Symbolic description only: never try to materialize this huge number.

    The natural-number function denoted by this expression is primitive
    recursive (indeed elementary).  Its outer exponentials are intentionally
    not evaluated by this diagnostic program.
    """
    if k < 1:
        return {"k": k, "expression": "2"}
    q = 8 * k
    d = contraction_parameters(q)["D"]
    return {"k": k, "q": q, "D": d,
            "inner_exponent": d * d + 2,
            "expression": "2^(2^(D^2+2))"}


if __name__ == "__main__":
    import json
    print(json.dumps({"prime_count_100": prime_count(100),
                      "logarithm_lower_10": str(logarithm_lower(10)),
                      "modulus_k_1": modulus_description(1)}, indent=2))
