"""Check componentwise Lubin--Tate recovery by finite observation matrices.

Standard-library Python 3. Uses the multiplicative coordinate over Z_p.
All predicted cutoffs in CASES are explicit test vectors. The test itself
does not divide formal series or compute Eisenstein factors.
"""
from math import comb


def polynomial_product(left, right, length, modulus):
    result = [0] * length
    for i, x in enumerate(left):
        if x:
            for j, y in enumerate(right[:length - i]):
                result[i + j] = (result[i + j] + x * y) % modulus
    return result


def image_log_size(rows, prime, precision):
    """Base-p logarithm of the row span over Z/(p^precision)."""
    modulus = prime**precision
    rows = [list(row) for row in rows]
    answer = 0
    while rows and rows[0]:
        best = None
        for i, row in enumerate(rows):
            for j, a in enumerate(row):
                if a:
                    power = 1
                    while a % (power * prime) == 0:
                        power *= prime
                    if best is None or power < best[0]:
                        best = (power, i, j)
                    if power == 1:
                        break
            if best and best[0] == 1:
                break
        if best is None:
            break
        power, i, j = best
        pivot = rows.pop(i)
        unit = pow(pivot[j] // power, -1, modulus)
        pivot = [(a * unit) % modulus for a in pivot]
        assert pivot[j] == power
        for i, row in enumerate(rows):
            assert row[j] % power == 0
            multiplier = row[j] // power
            row = [(a - multiplier * b) % modulus for a, b in zip(row, pivot)]
            assert row[j] == 0
            # The pivot has least valuation. Column operations then clear
            # its other entries without changing the remaining rows.
            rows[i] = row[:j] + row[j+1:]
        n = modulus // power
        while n > 1:
            answer += 1
            n //= prime
    return answer


def jet_is_determined(branches, cutoffs, prime, precision):
    degree = len(branches)
    length = max(degree, *cutoffs)
    modulus = prime**precision
    terms = [(i, t-i) for t in range(length) for i in range(t+1)]
    observations = []
    for branch, n in zip(branches, cutoffs):
        u = [0]+[comb(branch, k) % modulus if k <= branch else 0
                  for k in range(1, n)]
        powers = [[1]+[0]*(n-1)]
        for _ in range(1, length):
            powers.append(polynomial_product(powers[-1], u, n, modulus))
        observations += [[powers[j][k-i] if i <= k else 0
                          for i, j in terms] for k in range(n)]
    target = [[int(a == i and b == j) for a, b in terms]
              for i, j in terms if i+j < degree]
    # Adding these target rows cuts the kernel exactly if the image size
    # increases. Row and column maps have the same invariant factors.
    return image_log_size(observations, prime, precision) == image_log_size(
        observations+target, prime, precision)


CASES = [
    # (p, r, integral representatives of B, n_b=1+t_b in matching order)
    (2, 1, [0, 2, 6], [5, 7, 7]),
    (2, 2, [0, 2, 6], [5, 9, 9]),
    (2, 3, [0, 2, 6], [7, 11, 11]),
    (2, 4, [0, 2, 6], [7, 13, 13]),
    (2, 2, [0, 1, 2, 3], [6, 6, 6, 6]),
    (3, 2, [0, 3, 6], [9, 9, 9]),
    (3, 3, [0, 3, 6], [9, 9, 9]),
    (3, 2, [0, 1, 2], [3, 3, 3]),
]


if __name__ == "__main__":
    for p, r, directions, n in CASES:
        assert jet_is_determined(directions, n, p, r)
        for b in range(len(directions)):
            reduced = n.copy()
            reduced[b] -= 1
            assert not jet_is_determined(directions, reduced, p, r)
        print(f"p={p} r={r} B={directions}: exact jet cutoffs {n}")
