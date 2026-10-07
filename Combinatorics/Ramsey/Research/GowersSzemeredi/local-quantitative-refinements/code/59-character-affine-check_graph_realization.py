#!/usr/bin/env python3
"""Exact finite checks for prescribed vertical-defect graph realizations.

Uses k-multisets, so repetitions of vertices are explicitly included. Compares
all integer-domain relation classes with reduction modulo 2k+1, computes the
actual defects, and exhausts subsets to check exact unweighted/weighted optima.
"""
from collections import defaultdict
from itertools import combinations_with_replacement, product
import json

if not __debug__:
    raise SystemExit("Run without -O or -OO; assertions are required.")


def check_case(k, target_moduli):
    elements = list(product(*(range(n) for n in target_moduli)))
    zero = (0,) * len(target_moduli)

    def neg(x):
        return tuple(-a % n for a, n in zip(x, target_moduli))

    def add_labels(indices, labels):
        return tuple(sum(labels[i][j] for i in indices) % n
                     for j, n in enumerate(target_moduli))

    def subtract(a, b):
        return tuple((x - y) % n for x, y, n in zip(a, b, target_moduli))

    representatives = sorted({min(x, neg(x)) for x in elements if x != zero})
    q = len(representatives)
    dimension = (2 * k - 1) * q
    vertices, labels = [], []
    for block, f in enumerate(representatives):
        start = (2 * k - 1) * block
        for j in range(2 * k - 1):
            v = [0] * dimension
            v[start + j] = 1
            vertices.append(tuple(v))
            labels.append(f if j == 0 else zero)
        v = [0] * dimension
        for j in range(2 * k - 1):
            v[start + j] = 1 if j < k else -1
        vertices.append(tuple(v))
        labels.append(zero)
    size = len(vertices)
    assert size == 2 * k * q and len(set(vertices)) == size
    modulus = 2 * k + 1
    assert len({tuple(a % modulus for a in v) for v in vertices}) == size
    integer_classes, finite_classes = defaultdict(list), defaultdict(list)
    value_sums = {}
    multiset_count = 0
    for indices in combinations_with_replacement(range(size), k):
        domain_sum = tuple(sum(vertices[i][j] for i in indices)
                           for j in range(dimension))
        integer_classes[domain_sum].append(indices)
        finite_classes[tuple(a % modulus for a in domain_sum)].append(indices)
        value_sums[indices] = add_labels(indices, labels)
        multiset_count += 1
    integer_partition = {tuple(sorted(xs)) for xs in integer_classes.values()}
    finite_partition = {tuple(sorted(xs)) for xs in finite_classes.values()}
    assert integer_partition == finite_partition

    expected_collisions = {
        tuple(sorted((tuple(range(2*k*i, 2*k*i+k)),
                      tuple(range(2*k*i+k, 2*k*i+2*k))))) for i in range(q)
    }
    collisions = {xs for xs in integer_partition if len(xs) > 1}
    assert collisions == expected_collisions
    actual_defects, bad_supports = set(), set()
    for xs in integer_partition:
        for left, right in product(xs, repeat=2):
            defect = subtract(value_sums[left], value_sums[right])
            if defect != zero:
                actual_defects.add(defect)
                bad_supports.add(sum(1 << i for i in set(left) | set(right)))
    assert actual_defects == set(elements) - {zero}
    assert bad_supports == {((1 << (2*k)) - 1) << (2*k*i) for i in range(q)}

    weights = [(7*i + 3) % 11 for i in range(size)]
    subset_weights = [0] * (1 << size)
    maximum_cardinality = maximum_weight = 0
    valid_subsets = 0
    for mask in range(1 << size):
        if mask:
            bit = mask & -mask
            subset_weights[mask] = subset_weights[mask ^ bit] + weights[bit.bit_length()-1]
        # These support obstructions were computed from all actual relations.
        if any(mask & forbidden == forbidden for forbidden in bad_supports):
            continue
        valid_subsets += 1
        maximum_cardinality = max(maximum_cardinality, mask.bit_count())
        maximum_weight = max(maximum_weight, subset_weights[mask])
    expected_weight = sum(weights) - sum(min(weights[2*k*i:2*k*(i+1)]) for i in range(q))
    assert maximum_cardinality == (2*k-1)*q
    assert maximum_weight == expected_weight
    assert valid_subsets == ((1 << (2*k)) - 1) ** q
    return {"k": k, "target_moduli": target_moduli, "sign_orbits": q,
            "vertices": size, "ambient_dimension": dimension,
            "finite_modulus": modulus, "k_multisets": multiset_count,
            "nontrivial_relation_classes": len(collisions),
            "subsets_checked": 1 << size, "freiman_subsets": valid_subsets,
            "maximum_cardinality": maximum_cardinality,
            "weights": weights, "maximum_weight": maximum_weight}


if __name__ == "__main__":
    cases = [check_case(k, target) for target in [(3,), (5,), (2, 2)]
             for k in (2, 3)]
    print(json.dumps({"status": "PASS", "arithmetic": "exact integers",
                      "scope": "Finite supplements to the general analytic proof",
                      "cases": cases,
                      "k_multisets_checked": sum(x["k_multisets"] for x in cases),
                      "subsets_checked": sum(x["subsets_checked"] for x in cases)},
                     indent=2, sort_keys=True))
