"""Random cross-check of the default scanner against the generic 0.2 scanner and the 0.1 set algebra.

Usage: python crosscheck.py [count] [seed]
"""
import random
import sys

from fastunknot import Diagram, khovanov_rank


def one_component(strands, word):
    p = list(range(strands))
    for g in word:
        i = abs(g) - 1
        p[i], p[i + 1] = p[i + 1], p[i]
    x, n = p[0], 1
    while x != 0:
        x, n = p[x], n + 1
    return n == strands


def main():
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    done = bad = 0
    while done < count:
        strands = rng.choice((2, 3, 4, 5))
        length = rng.randrange(strands - 1, 16)
        word = [rng.choice((1, -1)) * rng.randrange(1, strands) for _ in range(length)]
        if not one_component(strands, word):
            continue
        done += 1
        d = Diagram.from_braid(strands, word)
        fast = khovanov_rank(d.pd, check_d_squared=done % 4 == 0, tail=done % 3)
        slow = khovanov_rank(d.pd, pivot="lifo", algebra="sets" if done % 2 else "bits")
        if (fast["rank"], fast["by_degree"]) != (slow["rank"], slow["by_degree"]):
            bad += 1
            print("MISMATCH", strands, word, fast["by_degree"], slow["by_degree"])
    print(f"{done} closures, {bad} mismatches")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
