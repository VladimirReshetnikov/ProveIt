"""Reproduce the exact Python audits and example certificates (standard library)."""
from __future__ import annotations
import json
from itertools import combinations, permutations, product
from math import factorial
from pathlib import Path
import random
from collections import Counter
from dfao import (accessible_and_distinguishable, cycles, cyclic_membership,
                  landau, missing_certificate, orbital_chromatic, orbital_edges,
                  permutation_order, proper, pullback, reverse_orbit)
from certificate_checker import verify, in_cyclic_orbit

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "results"


def save(name: str, obj: object) -> None:
    (OUT / name).write_text(json.dumps(obj, indent=2) + "\n")


def main() -> None:
    OUT.mkdir(exist_ok=True)
    counts = Counter()
    # No symmetry reductions: all ordered map pairs and all six output bijections.
    maps3 = list(product(range(3), repeat=3))
    for a in maps3:
        for b in maps3:
            for tau in permutations(range(3)):
                orbit = reverse_orbit((a, b), tau, 3)
                assert len(orbit) <= 24
                cert = missing_certificate(a, b, tau, 3)
                assert verify(cert)
                assert tuple(cert["target"]) not in orbit
                counts["n3_ordered_pairs_all_surjective_outputs"] += 1
    # Compare both independent cyclic membership algorithms with direct rotation.
    rng = random.Random(20260920)
    for n in range(3, 13):
        for _ in range(50):
            a = list(range(n)); rng.shuffle(a); a = tuple(a)
            tau = tuple(rng.randrange(3) for _ in range(n))
            powers = {tau}; c = pullback(tau, a)
            while c != tau:
                powers.add(c); c = pullback(c, a)
            positive = list(sorted(powers))[rng.randrange(len(powers))]
            for target in (positive, tuple(rng.randrange(3) for _ in range(n))):
                expected = target in powers
                assert cyclic_membership(a, tau, target)["member"] == expected
                assert in_cyclic_orbit(list(a), list(tau), list(target)) == expected
                counts["cyclic_membership_cross_checks"] += 1
    # Check the orbit/relabeling intersection bound directly, for k=3,4,5.
    for n in range(3, 11):
        for k in range(3, min(n, 5) + 1):
            for _ in range(12):
                a = list(range(n)); rng.shuffle(a); a = tuple(a)
                c = list(range(k)) + [rng.randrange(k) for _ in range(n-k)]
                rng.shuffle(c); c = tuple(c)
                recolorings = {tuple(p[x] for x in c) for p in permutations(range(k))}
                orbit = {c}; d = pullback(c, a)
                while d != c:
                    orbit.add(d); d = pullback(d, a)
                assert len(orbit & recolorings) <= landau(k)
                counts["cyclic_relabeling_checks"] += 1
    # Check all pair orbital chromatic formulas through n=5, all permutations, k=3,4.
    for n in range(3, 6):
        colorings = {k: list(product(range(k), repeat=n)) for k in (3, 4)}
        for a in permutations(range(n)):
            for pair in combinations(range(n), 2):
                edges = orbital_edges(a, pair)
                for k in (3, 4):
                    actual = sum(proper(c, edges) for c in colorings[k])
                    assert actual == orbital_chromatic(a, pair, k)
                    counts["orbital_chromatic_checks"] += 1
    # Random finite-orbit audits, balanced across the three generator cases.
    for n in range(3, 9):
        for k in range(3, min(n, 4) + 1):
            for case in range(3):
                for _ in range(10):
                    a = list(range(n)); rng.shuffle(a)
                    b = list(range(n)); rng.shuffle(b)
                    if case >= 1: b[-1] = b[0]
                    if case == 2: a[-1] = a[0]
                    tau = list(range(k)) + [rng.randrange(k) for _ in range(n-k)]
                    rng.shuffle(tau)
                    orbit = reverse_orbit((a, b), tau, k)
                    assert len(orbit) <= k**n - factorial(k) + landau(k)
                    cert = missing_certificate(a, b, tau, k)
                    assert verify(cert) and tuple(cert["target"]) not in orbit
                    counts["random_exact_orbit_audits"] += 1
    # Larger certificate-only tests: these do NOT enumerate the transition monoid.
    for n in range(3, 51):
        for case in range(3):
            for _ in range(10):
                k = rng.randint(3, min(n, 8))
                a = list(range(n)); rng.shuffle(a)
                b = list(range(n)); rng.shuffle(b)
                if case >= 1: b[-1] = b[0]
                if case == 2: a[-1] = a[0]
                # Include nonsurjective output maps in this robustness audit.
                tau = [rng.randrange(k) for _ in range(n)]
                cert = missing_certificate(a, b, tau, k)
                assert verify(cert)
                counts["large_certificate_checks"] += 1
    examples = [
        ((1, 2, 0), (0, 0, 2), (0, 1, 2), 3),
        ((1, 2, 3, 0), (0, 0, 3, 2), (0, 1, 0, 2), 3),
        ((1, 2, 3, 0), (0, 0, 3, 2), (0, 1, 2, 3), 4),
        ((1, 0, 3, 4, 2), (2, 1, 2, 3, 0), (0, 1, 2, 2, 2), 3),
    ]
    records, certs = [], []
    for a, b, tau, k in examples:
        orbit = reverse_orbit((a,b), tau, k)
        cert = missing_certificate(a,b,tau,k)
        assert verify(cert) and tuple(cert["target"]) not in orbit
        certs.append(cert)
        records.append({"n":len(a), "k":k, "a":a, "b":b, "tau":tau,
                        "reverse_states":len(orbit),
                        "minimal_from_state_zero":accessible_and_distinguishable(a,b,tau),
                        "unreachable_example":cert["target"]})
    save("examples.json", records)
    save("certificates.json", certs)
    orbit3 = reverse_orbit(((1,2,0),(0,0,2)), (0,1,2), 3)
    save("sharp_n3_orbit.json", [{"state":c,"word":w} for c,w in sorted(orbit3.items())])
    save("landau_gaps.json", [{"k":k,"g":landau(k),"gap":factorial(k)-landau(k)}
                              for k in range(3, 13)])
    # Independently verify every witness printed by the exhaustive C++ program.
    exhaustive_file = OUT / "exhaustive.json"
    if exhaustive_file.exists():
        for row in json.loads(exhaustive_file.read_text()):
            a,b,tau = (tuple(row[x]) for x in ("a","b","tau"))
            assert len(reverse_orbit((a,b),tau,row["k"])) == row["maximum"]
            assert any(accessible_and_distinguishable(a,b,tau,q) for q in range(row["n"]))
            counts["cpp_maximizing_witnesses_verified_in_python"] += 1
    save("audit_summary.json", {"status":"PASS", "random_seed":20260920,
                               "counts":dict(counts),
                               "limitations":"Finite tests are audits, not a formal proof of the general theorem."})
    print(json.dumps(dict(counts), indent=2))
    print("All exact audits passed.")


if __name__ == "__main__":
    main()
