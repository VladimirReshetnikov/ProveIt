"""Exact finite Frobenius coset computations for the three permutation actions."""
from fractions import Fraction
from itertools import permutations
import json


def compose(a, b):
    return tuple(a[j] for j in b)


def inverse(g):
    return tuple(g.index(j) for j in range(len(g)))


def generate(n, generators):
    group = {tuple(range(n))}
    stack = list(group)
    while stack:
        a = stack.pop()
        for b in generators:
            ab = compose(a, b)
            if ab not in group:
                group.add(ab)
                stack.append(ab)
    return group


def example(group):
    identity = tuple(range(len(next(iter(group)))))
    commutators = {compose(compose(a, b), inverse(compose(b, a)))
                   for a in group for b in group}
    derived = generate(len(identity), commutators)
    cosets = {frozenset(compose(a, b) for b in derived) for a in group}
    fix = {g: sum(i == j for i, j in enumerate(g)) for g in group}
    # Conditional means over abelianization cosets.
    residual = Fraction()
    false_decisions = 0
    for coset in cosets:
        mean = Fraction(sum(fix[g] for g in coset), len(coset))
        residual += sum((fix[g] - mean) ** 2 for g in coset)
        positives = int(identity in coset)
        false_decisions += min(positives, len(coset) - positives)
    H = {g for g in group if g[0] == 0}
    HD = {compose(h, d) for h in H for d in derived}
    double_cosets = {frozenset(compose(compose(h, g), k) for h in H for k in H)
                     for g in group}
    abelian_degree = len(group) // len(HD)
    predicted_mse = len(double_cosets) - abelian_degree
    assert residual / len(group) == predicted_mse
    assert false_decisions == int(len(derived) > 1)
    return dict(order=len(group), derived_order=len(derived),
                abelian_subfield_degree=abelian_degree,
                double_cosets=len(double_cosets), mean_square=predicted_mse,
                minimum_split_error=str(Fraction(false_decisions, len(group))))


cases = {
    "cyclic quartic (regular)": generate(4, [(1, 2, 3, 0)]),
    "S3 (three letters)": set(permutations(range(3))),
    "D4 (vertices of square)": generate(4, [(1, 2, 3, 0), (0, 3, 2, 1)]),
    "S4 (four letters)": set(permutations(range(4))),
}
print(json.dumps({name: example(group) for name, group in cases.items()}, indent=2))
