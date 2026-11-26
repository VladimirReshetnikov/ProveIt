"""An exact check of the exponentially weighted non-averaging set.

Source: J. Wroblewski, https://www.math.uni.wroc.pl/~jwr/non-ave/DATABASE.TXT
Record: a(143)<=1360, tagged (1092044464 Gavin Theobald).
SOURCE_SLICE gives precisely that row's entries from 878 through 1358.
"""
from itertools import combinations

SOURCE_SLICE = [
    878, 879, 882, 883, 889, 891, 892, 894, 898, 908, 915, 916, 919, 920,
    926, 928, 929, 931, 935, 945, 989, 990, 993, 994, 1000, 1002, 1003,
    1005, 1009, 1019, 1026, 1027, 1030, 1031, 1037, 1039, 1040, 1042,
    1046, 1056, 1211, 1212, 1215, 1216, 1222, 1224, 1225, 1227, 1231,
    1241, 1248, 1249, 1252, 1253, 1259, 1261, 1262, 1264, 1268, 1315,
    1318, 1319, 1322, 1327, 1328, 1331, 1333, 1342, 1345, 1346, 1349,
    1354, 1355, 1358,
]


def main():
    b = {x - 878 for x in SOURCE_SLICE}
    assert (len(b), min(b), max(b)) == (74, 0, 480)
    for first, last in combinations(b, 2):
        assert (first + last) % 2 == 1 or (first + last) // 2 not in b
    a = {0}
    for j in range(7):
        a |= {i + 3**j for i in a}
    n = max(a)
    assert (len(a), n) == (128, 1093)
    # Evaluate exactly at z=127/128, clearing the common denominator.
    def scaled_weight(indices):
        return sum(127**i * 128**(n-i) for i in indices)

    difference = scaled_weight(b) - scaled_weight(a)
    assert difference * 1000 > 16 * 128**n
    assert 100000 * 128 * 127**2187 < 128**2187
    assert 74 * 127 * 1000 < 5 * 2_000_000
    # From x^(2^n) - x, the exact degree counts satisfy sum_{d|n} d*I[d] = 2^n.
    irreducibles = [0] * 481
    for degree in range(1, 481):
        previous = sum(d * irreducibles[d] for d in range(1, degree)
                       if degree % d == 0)
        quotient, remainder = divmod(2**degree - previous, degree)
        assert remainder == 0 and quotient > 0
        irreducibles[degree] = quotient
    bound = 480 + 2_000_000 * sum(irreducibles)
    assert bound + 13 < 2**494
    print("For q=2 the cutoff R_0 satisfies R_0 + 13 < 2^494.")
    print("74 terms, maximum 480, all midpoint tests passed.")
    print("Finite weight gain > 0.016, ternary tail < 0.00001.")
    print("Truncation loss < 0.005 for R = 480 + 2000000 * number_of_smooth_primes.")


if __name__ == "__main__":
    main()
