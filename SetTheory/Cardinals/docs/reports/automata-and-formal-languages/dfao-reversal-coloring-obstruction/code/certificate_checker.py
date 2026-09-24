"""Independent certificate verifier; no imports from dfao.py, no word search.

The verifier recomputes all structural conditions.  For cyclic nonmembership it
uses pairwise compatibility of congruences, unlike the producer's iterative CRT.
"""
from __future__ import annotations
import argparse
import json
from collections import Counter
from math import gcd
from pathlib import Path


def in_cyclic_orbit(a: list[int], start: list[int], target: list[int]) -> bool:
    unseen = set(range(len(a)))
    congruences = []
    while unseen:
        q = min(unseen)
        cycle = []
        while q in unseen:
            unseen.remove(q); cycle.append(q); q = a[q]
        length = len(cycle)
        shifts = [s for s in range(length) if all(
            target[cycle[i]] == start[cycle[(i+s) % length]] for i in range(length))]
        if not shifts:
            return False
        # The stabilizer's smallest positive shift is the period.
        period = next(s for s in range(1, length + 1) if all(
            start[cycle[i]] == start[cycle[(i+s) % length]] for i in range(length)))
        residue = shifts[0] % period
        if set(shifts) != {s for s in range(length) if s % period == residue}:
            raise ValueError("Invalid rotation coset.")
        congruences.append((residue, period))
    return all((r-s) % gcd(m, n) == 0
               for r, m in congruences for s, n in congruences)


def verify(cert: dict) -> bool:
    try:
        n, k = cert["n"], cert["k"]
        a, b, tau, target = (cert[x] for x in ("a", "b", "tau", "target"))
        if type(n) is not int or type(k) is not int or not 3 <= k <= n:
            return False
        if any(len(t) != n or any(type(x) is not int or not 0 <= x < n for x in t)
               for t in (a, b)):
            return False
        if any(len(t) != n or any(type(x) is not int or not 0 <= x < k for x in t)
               for t in (tau, target)):
            return False
        pa, pb = len(set(a)) == n, len(set(b)) == n
        case = cert["case"]
        if case == "two_permutations":
            return pa and pb and Counter(tau) != Counter(target)
        if case == "two_singular":
            if pa or pb or target == tau or len(cert["pairs"]) != 2:
                return False
            for t, pair in zip((a, b), cert["pairs"]):
                u, v = pair
                if not 0 <= u < v < n or t[u] != t[v] or target[u] == target[v]:
                    return False
            return True
        if case != "one_permutation" or pa == pb:
            return False
        name = "a" if pa else "b"
        if cert["permutation_letter"] != name:
            return False
        perm, singular = (a, b) if pa else (b, a)
        u, v = cert["pair"]
        if not 0 <= u < v < n or singular[u] != singular[v]:
            return False
        seen = set()
        while tuple(sorted((u, v))) not in seen:
            edge = tuple(sorted((u, v)))
            seen.add(edge)
            if target[u] == target[v]:
                return False
            u, v = perm[u], perm[v]
        if sorted(seen) != sorted(tuple(e) for e in cert["edges"]):
            return False
        return not in_cyclic_orbit(perm, tau, target)
    except (KeyError, TypeError, ValueError, IndexError, StopIteration):
        return False


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("file", type=Path, help="A certificate or list of certificates in JSON")
    args = parser.parse_args()
    data = json.loads(args.file.read_text())
    certificates = data if isinstance(data, list) else [data]
    failures = [i for i, cert in enumerate(certificates) if not verify(cert)]
    if failures:
        raise SystemExit(f"REJECTED certificate indices {failures}")
    print(f"ACCEPTED {len(certificates)} certificate(s)")


if __name__ == "__main__":
    main()
