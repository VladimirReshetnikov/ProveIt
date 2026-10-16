#!/usr/bin/env python3
"""Finite HF-set check of the Capture proof issue and tagged repair.

This checks a counterexample to one untagged inference, not to Friedman's
Capture theorem.  The general tagged proof is in data/capture_tagged_proof.md.  No model of
the full class theory is represented by this finite regression.
"""
import json


def union(a):
    return frozenset(x for member in a for x in member)


def iterate_union(a, n):
    for _ in range(n):
        a = union(a)
    return a


def pair(x, y):
    """Kuratowski ordered pair, implemented using unordered HF sets."""
    return frozenset((frozenset((x,)), frozenset((x, y))))


def subsets(a):
    items = tuple(a)
    for mask in range(1 << len(items)):
        yield frozenset(x for i, x in enumerate(items) if mask & (1 << i))


def main():
    ordinals = []
    for _ in range(4):
        ordinals.append(frozenset(ordinals))
    zero, one, two, three = ordinals
    a = frozenset((zero, two))
    relation = ((zero, one), (two, three))

    def untagged(x, y):
        return frozenset((x, frozenset((x, y))))

    b = frozenset(untagged(x, y) for x, y in relation)
    c = frozenset((a,))
    assert c <= b and a <= union(c)
    assert untagged(two, three) not in c
    assert three not in iterate_union(c, 2)
    assert all(x in a for x, _ in relation)
    assert all(any(u == x for u, _ in relation) for x in a)

    a_tag = lambda x: pair(zero, x)
    b_tag = lambda y: pair(one, y)
    a0 = frozenset(a_tag(x) for x in a)
    tagged_b = frozenset(frozenset((a_tag(x), b_tag(y)))
                        for x, y in relation)
    # The tags prevent an output code from covering an input code.
    assert all(a_tag(x) != b_tag(y) for x in a for _, y in relation)
    # A0 can be cut out of a double power set, without Replacement.
    u = a | frozenset((zero, one))
    power_u = frozenset(subsets(u))
    assert a0 <= frozenset(subsets(power_u))
    assert a0 <= union(tagged_b)
    capture_witnesses = 0
    for tagged_c in subsets(tagged_b):
        if not a0 <= union(tagged_c):
            continue
        capture_witnesses += 1
        bound = iterate_union(tagged_c, 3)
        for x in a:
            assert any(u == x and frozenset((a_tag(u), b_tag(y))) in tagged_c
                       for u, y in relation)
            assert any(u == x and y in bound for u, y in relation)
    assert capture_witnesses == 1
    print(json.dumps({
        "untagged_capture_hypotheses": True,
        "untagged_claimed_input_coverage": False,
        "untagged_double_union_bounds_witnesses": False,
        "missing_input": 2,
        "missing_witness": 3,
        "tagged_capture_witnesses_exhaustively_checked": capture_witnesses,
        "tagged_triple_union_bounds_witnesses": True,
        "status": "all checks passed"
    }, indent=2))


if __name__ == "__main__":
    main()
