"""Check the k-subset theorem and exact odd-orbit bounds by cycle types."""
from itertools import combinations, permutations
from math import comb, gcd, lcm
from functools import reduce


def partitions(total, largest=None):
    if total == 0:
        yield ()
        return
    for part in range(min(total, largest or total), 0, -1):
        for rest in partitions(total - part, part):
            yield (part,) + rest


def invariant_sizes(cycles, power=1):
    # A cycle of length a becomes gcd(a,power) cycles of equal length.
    sums = 1
    for length in cycles:
        count = gcd(length, power)
        for _ in range(count):
            sums |= sums << (length // count)
    return sums


def odd_orbit_limit(n, k):
    worst, witness = 0, ()
    for cycles in partitions(n):
        if (n - len(cycles)) % 2:
            continue
        order = reduce(lcm, cycles, 1)
        odd_part = order // (order & -order)
        # A fixed set of g**j has g-orbit length dividing j.
        for j in range(1, odd_part + 1, 2):
            if odd_part % j == 0 and (invariant_sizes(cycles, j) >> k) & 1:
                if j > worst:
                    worst, witness = j, cycles
                break
        else:
            return None, cycles
    return worst, witness


def literal_check(n):
    # Directly visit orbits, independently of the cycle-partition reasoning.
    for k in range(1, n // 2 + 1):
        sets = list(combinations(range(n), k))
        worst = 0
        for g in permutations(range(n)):
            if sum(x > y for i, x in enumerate(g) for y in g[i + 1:]) % 2:
                continue
            remaining, odd_lengths = set(sets), []
            while remaining:
                subset, length = next(iter(remaining)), 0
                while subset in remaining:
                    remaining.remove(subset)
                    subset = tuple(sorted(g[i] for i in subset))
                    length += 1
                if length % 2:
                    odd_lengths.append(length)
            if not odd_lengths:
                worst = None
                break
            worst = max(worst, min(odd_lengths))
        assert worst == odd_orbit_limit(n, k)[0]


def run():
    for n in range(4, 8):
        literal_check(n)
    for n in range(4, 35):
        even_types = [c for c in partitions(n) if (n-len(c)) % 2 == 0
                      and all(x & (x-1) == 0 for x in c)]
        for k in range(1, n//2 + 1):
            expected = (k & ~n == 0 or n in (2*k, 2*k+1) and k & (k-1) == 0)
            assert expected == all((invariant_sizes(c) >> k) & 1 for c in even_types)
    print("Subset classification checked through n=34; literal actions through n=7.")
    print("n,k,degree,max_min_odd_orbit,witness_cycle_lengths")
    for n in (4, 5, 8, 9, 16, 17, 32, 33):
        k = n // 2
        bound, witness = odd_orbit_limit(n, k)
        print(f"{n},{k},{comb(n,k)},{bound}," + "+".join(map(str,witness)))


if __name__ == "__main__":
    run()
