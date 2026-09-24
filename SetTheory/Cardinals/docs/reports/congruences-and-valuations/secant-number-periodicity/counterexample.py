"""Standalone finite disproof of the periodicity conjecture in OEIS A000364.

Python 3.8+; standard library only. This checker does not use the general
period or preperiod formulas developed in the article.
"""

from math import comb


def main() -> None:
    values = [1]
    for n in range(1, 20):
        value = sum(
            (1 if j % 2 else -1) * comb(2 * n, 2 * j) * values[n - j]
            for j in range(1, n + 1)
        )
        values.append(value)

    print("a(19) =", values[19])
    print("a(1) mod 27 =", values[1] % 27)
    print("a(19) mod 27 =", values[19] % 27)
    if values[1] % 27 == values[19] % 27:
        raise RuntimeError("The claimed counterexample failed")
    print("Conjecture disproved: 1 != 10 modulo 27.")


if __name__ == "__main__":
    main()
