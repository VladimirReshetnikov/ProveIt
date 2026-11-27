"""Check the Krawtchouk recurrence and a lower bound, using exact rationals."""
from fractions import Fraction
from math import comb


def moment(positive, negative, k):
    """Mean product over all k-subsets of a population with the given signs."""
    m = positive + negative
    numerator = sum((-1) ** j * comb(negative, j) * comb(positive, k - j)
                    for j in range(max(0, k - positive), min(negative, k) + 1))
    return Fraction(numerator, comb(m, k))


def main():
    recurrences = bounds = 0
    for m in range(1, 81):
        for negative in range(m // 2 + 1):
            positive = m - negative
            imbalance = positive - negative
            beta = Fraction(imbalance, m)
            means = [moment(positive, negative, k) for k in range(m + 1)]
            assert means[0] == 1 and means[1] == beta
            for k in range(1, m):
                assert (m - k) * means[k + 1] == imbalance * means[k] - k * means[k - 1]
                recurrences += 1
            for k in range(1, int(beta ** 2 * m / 4) + 1):
                assert means[k] >= (beta / 2) ** k
                bounds += 1
    print(f"Exact checks for 1 <= m <= 80 and 0 <= #negative <= floor(m/2):")
    print(f"  {recurrences} recurrence identities and {bounds} lower bounds passed.")


if __name__ == "__main__":
    main()
