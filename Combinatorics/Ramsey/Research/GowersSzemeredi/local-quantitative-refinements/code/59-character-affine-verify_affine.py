#!/usr/bin/env python3
"""Exact checks for signed graph identities and affine-rigidity bounds.

Finite enumeration supplements the mathematical proof. It does not prove a
universal theorem or establish publication priority. All arithmetic is integral;
the pseudorandom samples have a fixed seed and are recorded in the report.
"""

from __future__ import annotations

import argparse
import itertools
import json
import random
from collections import Counter
from pathlib import Path

if not __debug__:
    raise SystemExit("Run without -O or -OO; assertions are required.")


class AbelianGroup:
    def __init__(self, factors):
        self.factors = tuple(factors)
        self.elements = list(itertools.product(*(range(n) for n in factors)))
        self.index = {x: i for i, x in enumerate(self.elements)}
        self.n = len(self.elements)
        self.add = [
            [self.index[tuple((a + b) % m for a, b, m in zip(x, y, factors))]
             for y in self.elements]
            for x in self.elements
        ]
        self.neg = [
            self.index[tuple((-a) % m for a, m in zip(x, factors))]
            for x in self.elements
        ]
        self.sub = [[self.add[x][self.neg[y]] for y in range(self.n)]
                    for x in range(self.n)]


def graph_energy(f, domain, target):
    result = 0
    for h in range(domain.n):
        r = Counter(target.sub[f[domain.add[x][h]]][f[x]]
                    for x in range(domain.n))
        result += sum(v * v for v in r.values())
    return result


def set_energy(support, domain):
    r = Counter(domain.sub[x][y] for x in support for y in support)
    return sum(v * v for v in r.values())


def is_nonempty_coset(support, domain):
    """Direct translated-subgroup check, independent of the energy criterion."""
    if not support:
        return False
    translated = {domain.sub[x][support[0]] for x in support}
    return (0 in translated
            and all(domain.neg[x] in translated for x in translated)
            and all(domain.add[x][y] in translated
                    for x in translated for y in translated))


def signed_energy(f, support, domain, target):
    points = [(x, w, sign) for x in support
              for w, sign in ((f[x], 1), (0, -1))]
    convolution = Counter()
    for x, a, sign1 in points:
        for y, b, sign2 in points:
            convolution[(domain.add[x][y], target.add[a][b])] += sign1 * sign2
    return sum(v * v for v in convolution.values())


def statistics(f, domain, target):
    N = domain.n
    support = [x for x in range(N) if f[x] != 0]
    s = len(support)
    counts = Counter(f[x] for x in support)
    M = sum(v * v for v in counts.values())
    A = s * s - M
    C = sum(v * counts[target.neg[a]] for a, v in counts.items())
    Z = sum(ca * cb * counts[target.add[a][b]]
            for a, ca in counts.items() for b, cb in counts.items())
    Z3 = sum(ca * ca * counts[target.neg[a]] for a, ca in counts.items()
             if target.add[target.add[a][a]][a] == 0)
    E = graph_energy(f, domain, target)
    ES = set_energy(support, domain)
    ED = signed_energy(f, support, domain, target)
    return dict(N=N, s=s, M=M, A=A, C=C, Z=Z, Z3=Z3, E=E, ES=ES, ED=ED)


def affine_maps(domain, target):
    possible_slopes = []
    for order in domain.factors:
        eligible = []
        for w in range(target.n):
            z = 0
            for _ in range(order):
                z = target.add[z][w]
            if z == 0:
                eligible.append(w)
        possible_slopes.append(eligible)
    maps = set()
    for slopes in itertools.product(*possible_slopes):
        linear = []
        for x in domain.elements:
            value = 0
            for coefficient, slope in zip(x, slopes):
                for _ in range(coefficient):
                    value = target.add[value][slope]
            linear.append(value)
        for b in range(target.n):
            maps.add(tuple(target.add[v][b] for v in linear))
    return sorted(maps)


def check_function(f, domain, target, counters, affine_family=None):
    p = statistics(f, domain, target)
    N, s, M, A, C, Z, Z3, E, ES, ED = (
        p[k] for k in ("N", "s", "M", "A", "C", "Z", "Z3", "E", "ES", "ED")
    )
    expanded = (N**3 - 4*s*N*N + N*(6*s*s + 4*M + 2*C)
                - 4*s**3 - 8*s*M - 4*s*C + 4*Z + ED)
    assert E == expanded, ("signed identity", f, p)
    assert ED <= 6*ES, ("quartic support bound", f, p)
    assert 0 <= C <= A, ("opposite pairs", f, p)
    assert 2*Z <= s*A, ("Schur bound", f, p)
    assert 2*(Z-Z3) <= s*(A-C), ("torsion-refined Schur", f, p)
    assert 2*Z3 <= s*C, ("order-three concentration", f, p)
    cubic = 4*s*N*N - 10*s*s*N + 6*s**3
    defect = N**3 - E
    support_deficit = s**3 - ES
    kernel_bound = 6*s**3 - 2*s*A + s*C - Z3
    assert ED <= kernel_bound, ("averaged signed-kernel bound", f, p)
    assert ED <= kernel_bound - 3*support_deficit, (
        "averaged kernel support gain", f, p)
    counters["averaged_kernel_support_checks"] += 1
    if s:
        support = [x for x in range(N) if f[x] != 0]
        expected_equality = A == 0 and is_nonempty_coset(support, domain)
        assert (ED == kernel_bound) == expected_equality, (
            "original averaged-kernel equality", f, p)
        counters["averaged_kernel_equality_checks"] += 1
    if 2*s <= N:
        assert defect >= cubic + 6*(s**3-ES) + 2*(N-3*s)*A, (
            "one-third remainder", f, p)
        counters["local_third_checks"] += 1
    if all(m % 3 for m in target.factors):
        assert 2*Z <= s*(A-C), ("no order-three Schur", f, p)
        assert defect >= (cubic + 6*(s**3-ES)
                          + (4*N-10*s)*A + (6*s-2*N)*C), (
            "no order-three remainder", f, p)
        counters["no_three_checks"] += 1
        assert ED <= kernel_bound - 4*support_deficit, (
            "no order-three averaged kernel support gain", f, p)
        counters["no_three_kernel_support_checks"] += 1
        if 0 < 2*s < N:
            assert defect >= (cubic + 4*support_deficit
                              + min(2*N-3*s, 4*N-8*s)*A), (
                "no order-three half-range profile", f, p)
            assert (defect == cubic) == expected_equality, (
                "no order-three half-range equality", f, p)
            counters["half_no_three_profile_checks"] += 1
            counters["half_no_three_equality_checks"] += 1
        if 2*s == N:
            assert defect >= cubic + 4*support_deficit, (
                "no order-three half-range endpoint", f, p)
            assert (defect == cubic) == expected_equality, (
                "no order-three endpoint equality", f, p)
            counters["half_no_three_endpoint_checks"] += 1
    if 9*s < 4*N:
        assert 2*(defect-cubic-3*support_deficit) >= (4*N-9*s)*A, (
            "four-ninths local bound", f, p)
        counters["optional_four_ninths_checks"] += 1
        if s:
            assert (defect == cubic) == expected_equality, (
                "four-ninths equality", f, p)
            counters["four_ninths_equality_checks"] += 1
    if 9*s == 4*N:
        assert defect > cubic, ("strict four-ninths endpoint", f, p)
        assert defect >= cubic + 3*support_deficit, (
            "four-ninths endpoint support gain", f, p)
        counters["four_ninths_endpoint_checks"] += 1
    if affine_family is not None and 9*defect < 2*N**3:
        distances = [sum(x != y for x, y in zip(f, ell))
                     for ell in affine_family]
        d = min(distances)
        assert distances.count(d) == 1, ("global uniqueness", f, p)
        assert 7*d < N, ("global inverse branch", f, p, d)
        assert defect >= 4*d*N*N-10*d*d*N+6*d**3, (
            "global inverse inequality", f, p, d)
        counters["global_recovery_checks"] += 1
    counters["function_checks"] += 1


def kernel(labels, target):
    result = 0
    for bits in itertools.product((0, 1), repeat=4):
        z = 0
        for bit, value in zip(bits, labels):
            if bit:
                z = target.add[z][value]
        if z == 0:
            result += (-1)**sum(bits)
    return result


def check_kernels(target, counters):
    for labels in itertools.product(range(1, target.n), repeat=4):
        K = kernel(labels, target)
        assert K <= 6, ("pointwise kernel", target.factors, labels, K)
        P = sum(target.add[labels[i]][labels[j]] == 0
                for i in range(4) for j in range(i+1, 4))
        if P != 4:
            assert K <= 4, ("unbalanced kernel", target.factors, labels, K)
        if labels[0] == labels[1] == labels[2]:
            a = labels[0]
            if target.add[target.add[a][a]][a] == 0:
                assert K <= 3, ("order-three kernel", labels, K)
        counters["kernel_checks"] += 1


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("affine_checks.json"))
    args = parser.parse_args()
    counters = Counter()
    enumerations = []
    # All maps, not only maps close to an affine map.
    suites = [((n,), (3,)) for n in range(1, 9)]
    suites += [((n,), (5,)) for n in range(1, 6)]
    suites += [((2, 2), (3,)), ((2, 3), (3,)), ((2, 2), (3, 3))]
    for domain_factors, target_factors in suites:
        domain, target = AbelianGroup(domain_factors), AbelianGroup(target_factors)
        family = affine_maps(domain, target)
        before = counters["function_checks"]
        for f in itertools.product(range(target.n), repeat=domain.n):
            check_function(f, domain, target, counters, family)
        enumerations.append(dict(domain=list(domain_factors), target=list(target_factors),
                                 maps=counters["function_checks"]-before))
    for target_factors in ((3,), (5,), (7,), (9,), (3, 3)):
        check_kernels(AbelianGroup(target_factors), counters)

    rng = random.Random(20261007)
    random_suites = [((16,), (3,)), ((17,), (5,)), ((18,), (9,)),
                     ((2, 8), (3, 3)), ((3, 5), (7,)), ((3, 3), (5, 5))]
    for domain_factors, target_factors in random_suites:
        domain, target = AbelianGroup(domain_factors), AbelianGroup(target_factors)
        family = affine_maps(domain, target)
        for _ in range(200):
            f = [rng.randrange(target.n) for _ in range(domain.n)]
            check_function(f, domain, target, counters, family)
            f = list(rng.choice(family))
            for x in rng.sample(range(domain.n), rng.randrange(1, min(6, domain.n))):
                f[x] = rng.randrange(target.n)
            check_function(f, domain, target, counters, family)
    for N in range(16, 41):
        for target_factors in ((3,), (5,), (9,)):
            domain, target = AbelianGroup((N,)), AbelianGroup(target_factors)
            for b in range(1, target.n):
                f = [0]*N
                f[0] = b
                assert graph_energy(f, domain, target) == N**3-4*N*N+10*N-6
                counters["one_point_extremizer_checks"] += 1
    report = dict(status="PASS", arithmetic="exact integers", random_seed=20261007,
                  exhaustive_suites=enumerations, counters=dict(counters),
                  scope=("Finite checks supplement the complete proofs; no finite "
                         "enumeration proves the universal theorem or establishes novelty."))
    args.output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
