#!/usr/bin/env python3
"""Finite diagnostics for the exact-hull theorem, not finite EPSC models.

Exhaustively checks each pair (raw membership relation, image relation) on
one, two and three objects.  The theorem is conditional on two specific
represented Separation predicates.  The census never treats these finite
objects as models of the FULL EPSC or EFPC schema.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path


def profiles(n: int, relation: int) -> tuple[int, ...]:
    """Column a is the exact incoming membership extension of object a."""
    return tuple(sum(((relation >> (x * n + a)) & 1) << x
                     for x in range(n)) for a in range(n))


def rows(n: int, relation: int) -> tuple[int, ...]:
    mask = (1 << n) - 1
    return tuple((relation >> (x * n)) & mask for x in range(n))


def subset(a: int, b: int) -> bool:
    return a & ~b == 0


def image(r: tuple[int, ...], inputs: int) -> int:
    result = 0
    for x, outputs in enumerate(r):
        if inputs & (1 << x):
            result |= outputs
    return result


def analyze(e: tuple[int, ...], r: tuple[int, ...]) -> dict:
    n = len(e)
    empties = sum((1 << x) for x in range(n) if e[x] == 0)
    f = tuple(image(r, empties | e[c]) for c in range(n))
    global_range = image(r, (1 << n) - 1)
    bounded = True
    for outputs in r:
        member_union = 0
        for y in range(n):
            if outputs & (1 << y):
                member_union |= e[y]
        if not any(subset(member_union, b) for b in e):
            bounded = False
            break
    pre = tuple(subset(f[c], e[c]) for c in range(n))
    epsc = [c for c in range(n) if pre[c] and subset(e[c], global_range)]
    efpc = [c for c in range(n) if f[c] == e[c]]
    assert all(c in epsc for c in efpc), "exact closure must imply support"
    resources = []
    for c in range(n):
        if not pre[c]:
            continue
        candidates = [b for b in range(n) if subset(e[b], e[c]) and pre[b]]
        assert c in candidates
        meet = e[c]
        for b in candidates:
            meet &= e[b]
        representatives = [l for l in range(n) if e[l] == meet]
        for l in representatives:
            j_extension = e[c] & f[l]
            js = [j for j in range(n) if e[j] == j_extension]
            if not js:
                continue
            # This is the exact theorem's hypothesis and conclusion.
            assert pre[l]
            assert f[l] == e[l]
            assert all(subset(e[l], e[b]) for b in candidates)
            resources.append((c, l, js[0]))
    return dict(empty_objects=empties, operator_images=f, local_bound=bounded,
                epsc_witnesses=epsc, efpc_witnesses=efpc,
                resource_triples=resources)


def display(bits: int, n: int) -> list[int]:
    return [x for x in range(n) if bits & (1 << x)]


def pointwise_counterexample() -> dict:
    e = (0, 0b011, 0b101)
    r = (0b001, 0, 0b010)
    result = analyze(e, r)
    assert result['local_bound']
    assert result['epsc_witnesses'] == [1]
    assert result['efpc_witnesses'] == []
    assert result['operator_images'] == (1, 1, 3)
    assert 1 not in e  # The separated singleton extension {0} is absent.
    return dict(domain=[0, 1, 2],
                membership_profiles=[display(a, 3) for a in e],
                relation_rows=[display(a, 3) for a in r],
                operator_images=[display(a, 3) for a in result['operator_images']],
                local_subset_bounded=True, epsc_witness=1,
                efpc_witnesses=[], missing_separated_extension=[0])


def census(max_n: int = 3) -> dict:
    counts = []
    for n in range(1, max_n + 1):
        extent = 1 << (n * n)
        count = dict(objects=n, relation_pairs=0, bounded_pairs=0,
                     epsc_true_bounded=0, efpc_true_bounded=0,
                     pointwise_gaps=0, triples_with_two_resources=0,
                     pointwise_gaps_with_empty=0,
                     nonextensional_resource_pairs=0)
        for e_code in range(extent):
            e = profiles(n, e_code)
            duplicates = len(set(e)) < n
            for r_code in range(extent):
                a = analyze(e, rows(n, r_code))
                count['relation_pairs'] += 1
                count['triples_with_two_resources'] += len(a['resource_triples'])
                if duplicates and a['resource_triples']:
                    count['nonextensional_resource_pairs'] += 1
                if a['local_bound']:
                    count['bounded_pairs'] += 1
                    count['epsc_true_bounded'] += bool(a['epsc_witnesses'])
                    count['efpc_true_bounded'] += bool(a['efpc_witnesses'])
                    count['pointwise_gaps'] += bool(a['epsc_witnesses']) and not a['efpc_witnesses']
                    count['pointwise_gaps_with_empty'] += bool(a['empty_objects']) and bool(a['epsc_witnesses']) and not a['efpc_witnesses']
        counts.append(count)
    if max_n >= 2:
        assert counts[1]['pointwise_gaps_with_empty'] == 0
    return dict(scope='Finite instances and conditional resources only; not full-schema models.',
                census=counts, pointwise_counterexample=pointwise_counterexample())


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--max-n', type=int, choices=[1, 2, 3], default=3)
    p.add_argument('--output', type=Path)
    args = p.parse_args()
    result = census(args.max_n)
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
