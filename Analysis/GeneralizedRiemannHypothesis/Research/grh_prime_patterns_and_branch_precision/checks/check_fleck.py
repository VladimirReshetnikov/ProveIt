"""Directly compare Fleck sums over the integers with the Lubin--Tate pole."""
from math import comb

from check_branch_poles import pole


def weighted_sums(n, M, m, modulus):
    result = [[0] * M for _ in range(m)]
    for k in range(n + 1):
        step, u = divmod(k, M)
        coefficient = (-1) ** (n - k) * comb(n, k)
        for j in range(min(step + 1, m)):
            result[j][u] = (result[j][u] + coefficient * comb(step, j)) % modulus
    return result


def main():
    checked = 0
    for p, t in [(2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (5, 1)]:
        M = p**t
        D = M - M // p
        for m in range(1, 5):
            for r in range(1, 7):
                threshold = pole(p, p, [t]*m, r)
                modulus = p**r
                for n in range(threshold + 2):
                    values = weighted_sums(n, M, m, modulus)
                    assert (not any(any(row) for row in values)) == (n >= threshold)
                    if n == threshold - 1:
                        assert not any(any(row) for row in values[:-1])
                        c = values[-1][0]
                        assert c != 0 and values[-1] == [c] * M
                        if threshold == m*M + (r - 1)*D:
                            assert c == (-p)**(r-1)*comb(m+r-2,r-1) % modulus
                    checked += 1
    print(f"Verified {checked} vectors of exact integer sums reduced modulo p^r.")
    for n in [7, 8, 11, 12]:
        modulus = 4 if n < 10 else 8
        vals = weighted_sums(n, 4, 2, modulus)
        print(f"p=2, t=2, m=2, modulus={modulus}, n={n}: {vals}")


if __name__ == "__main__":
    main()
