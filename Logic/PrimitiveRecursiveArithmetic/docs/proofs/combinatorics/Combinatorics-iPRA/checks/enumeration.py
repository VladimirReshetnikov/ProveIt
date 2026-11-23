"""Finite cross-checks using independent object enumerations (Python 3)."""
from collections import Counter
from itertools import combinations, permutations, product
from math import comb, factorial


def partitions(n):
    """Canonical words for set partitions, in order of first label."""
    words = [()]
    for _ in range(n):
        words = [w + (j,) for w in words for j in range(max(w, default=-1) + 2)]
    return words


def kernel(word):
    labels = {}
    return tuple(labels.setdefault(x, len(labels)) for x in word)


def integer_partitions(n, cap):
    if n == 0:
        yield ()
    for j in range(1, min(n, cap) + 1):
        for tail in integer_partitions(n-j, j):
            yield (j,) + tail


def verify_twelvefold():
    for n in range(6):
        s = Counter(len(set(w)) for w in partitions(n))
        ip = Counter(len(w) for w in integer_partitions(n, n))
        for r in range(6):
            classes = [[set() for _ in range(3)] for _ in range(4)]
            for w in product(range(r), repeat=n):
                occ = tuple(w.count(i) for i in range(r))
                reps = (w, occ, kernel(w), tuple(sorted(occ)))
                for j, allowed in enumerate((True, len(set(w)) == n, len(set(w)) == r)):
                    if allowed:
                        for row, a in zip(classes, reps):
                            row[j].add(a)
            weak = comb(n+r-1, r-1) if r else int(n == 0)
            positive = comb(n-1,r-1) if n >= r > 0 else int(n == r == 0)
            expected = [[r**n, factorial(r)//factorial(r-n) if n <= r else 0, factorial(r)*s[r]],
                        [weak, comb(r,n), positive], [sum(s[j] for j in range(r+1)), int(n <= r), s[r]],
                        [sum(ip[j] for j in range(r+1)), int(n <= r), ip[r]]]
            assert [[len(a) for a in row] for row in classes] == expected


def verify_narayana():
    for m in range(1, 8):
        counts = Counter()
        for w in partitions(m):
            crossing = any(w[a] == w[c] != w[b] == w[d] for a,b,c,d in combinations(range(m),4))
            if not crossing:
                counts[len(set(w))] += 1
        for k in range(1, m+1):
            assert m * counts[k] == comb(m, k) * comb(m, k-1)
    for size in range(3, 9):
        # Enumerate diagonal subsets that have not crossed an earlier diagonal.
        diagonals = [(i,j) for i,j in combinations(range(size), 2)
                     if j != i+1 and (i,j) != (0,size-1)]
        dissections = [()]
        for a,c in diagonals:
            dissections += [ds+((a,c),) for ds in dissections
                            if all(not (a<b<c<d or b<a<d<c) for b,d in ds)]
        counts = Counter(map(len,dissections))
        m = size-2
        for d in range(m):
            assert (d+1)*counts[d] == comb(m-1,d)*comb(m+d+1,d)


def verify_partition_and_derangement():
    for n in range(19):
        parts = list(integer_partitions(n,n))
        for h in range(2, min(n+2,9)):
            lhs = sum(all(j % h for j in w) for w in parts)
            rhs = sum(all(v < h for v in Counter(w).values()) for w in parts)
            assert lhs == rhs
    for n in range(9):
        derangements = sum(all(i != j for i,j in enumerate(w)) for w in permutations(range(n)))
        assert derangements == sum((-1)**j*comb(n,j)*factorial(n-j) for j in range(n+1))


if __name__ == "__main__":
    verify_twelvefold()
    verify_narayana()
    verify_partition_and_derangement()
    print("PASS: twelvefold table, Narayana numbers, polygon dissections, Glaisher and derangements")
