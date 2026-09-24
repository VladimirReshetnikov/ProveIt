#!/usr/bin/env python3
"""Finite-model regression checks for omnific normalization.

These checks concern finite sign sequences and finite rational normal forms.
They do not verify transfinite proofs or the Ehrlich--Kaplan theorem.
Run: python3 verify.py --output verification_report.json
"""
from __future__ import annotations
from fractions import Fraction
from functools import cmp_to_key, lru_cache
from itertools import product
import argparse
import json
import random
from typing import Dict, FrozenSet

Word = str
Series = Dict[Word, Fraction]
COUNTS: dict[str, int] = {}


def check(condition: bool, label: str) -> None:
    if not condition:
        raise AssertionError(label)
    COUNTS[label] = COUNTS.get(label, 0) + 1


def compare(x: Word, y: Word) -> int:
    """First difference with minus < undefined < plus."""
    rank = {'-': -1, '+': 1}
    for i in range(max(len(x), len(y))):
        a = rank[x[i]] if i < len(x) else 0
        b = rank[y[i]] if i < len(y) else 0
        if a != b:
            return (a > b) - (a < b)
    return 0


def ancestors(x: Word) -> set[Word]:
    return {x[:i] for i in range(len(x))}


def right_ancestors(x: Word) -> set[Word]:
    return {x[:i] for i, sign in enumerate(x) if sign == '-'}


def initial(tree: set[Word] | FrozenSet[Word]) -> bool:
    return all(ancestors(x) <= tree for x in tree)


def theta(x: Word, alpha: int) -> Word:
    p = '-' * alpha
    if compare(x, p) < 0:
        raise ValueError('Exponent lies below the cone minimum.')
    if x == p:
        return ''
    if x.startswith(p + '+'):
        return '+' + p + x[len(p) + 1:]
    return '+' + x


def psi(y: Word, alpha: int) -> Word:
    if compare(y, '') < 0:
        raise ValueError('Inverse requires a nonnegative exponent.')
    p = '-' * alpha
    if not y:
        return p
    v = y[1:]
    if v.startswith(p):
        return p + '+' + v[len(p):]
    return v


def words(depth: int) -> list[Word]:
    return [''.join(t) for n in range(depth + 1)
            for t in product('-+', repeat=n)]


@lru_cache(None)
def all_initial_trees(depth: int) -> tuple[FrozenSet[Word], ...]:
    """Every prefix-closed subset of words of length at most depth."""
    if depth < 0:
        return (frozenset(),)
    smaller = all_initial_trees(depth - 1)
    result = [frozenset()]
    for left in smaller:
        for right in smaller:
            result.append(frozenset({''} | {'-' + w for w in left}
                                    | {'+' + w for w in right}))
    return tuple(result)


def clean(s: Series) -> Series:
    return {e: c for e, c in s.items() if c}


def add(s: Series, t: Series) -> Series:
    out = s.copy()
    for e, c in t.items():
        out[e] = out.get(e, Fraction(0)) + c
    return clean(out)


def scale(s: Series, a: Fraction) -> Series:
    return clean({e: a*c for e, c in s.items()})


def normalize(s: Series, alpha: int, n: int) -> Series:
    p = '-' * alpha
    return {theta(e, alpha): c * (2**n if e == p else 1)
            for e, c in clean(s).items()}


def unnormalize(s: Series, alpha: int, n: int) -> Series:
    return {psi(e, alpha): c * (Fraction(1, 2**n) if not e else 1)
            for e, c in clean(s).items()}


def sign(s: Series) -> int:
    s = clean(s)
    if not s:
        return 0
    c = s[max(s, key=cmp_to_key(compare))]
    return (c > 0) - (c < 0)


def main() -> dict:
    finite_words = words(7)
    for alpha in range(8):
        p = '-' * alpha
        cone = [w for w in finite_words if compare(w, p) >= 0]
        image = {theta(w, alpha) for w in cone}
        check(len(image) == len(cone), 'cone_injective')
        for x in cone:
            tx = theta(x, alpha)
            check(psi(tx, alpha) == x, 'left_inverse')
            check(compare(tx, '') >= 0, 'image_nonnegative')
            check(len(tx) <= 1 + len(x), 'finite_length_bound')
            if x != p:
                check(ancestors(tx) ==
                      {theta(z, alpha) for z in ancestors(x) | {p}},
                      'exact_predecessor_identity')
                check(right_ancestors(tx) ==
                      {theta(z, alpha) for z in right_ancestors(x)},
                      'right_ancestors_off_minimum')
            else:
                check(right_ancestors(tx) == set(), 'minimum_loses_right_ancestors')
        for x in cone:
            for y in cone:
                check(compare(x, y) == compare(theta(x, alpha), theta(y, alpha)),
                      'order_preservation')
        for y in finite_words:
            if compare(y, '') >= 0:
                check(theta(psi(y, alpha), alpha) == y, 'right_inverse')

    trees = all_initial_trees(3)
    check(len(trees) == 677, 'enumerated_all_677_trees')
    for tree in trees:
        if not tree:
            continue
        p = min(tree, key=cmp_to_key(compare))
        alpha = len(p)
        check(set(p) <= {'-'}, 'initial_minimum_is_negative_ordinal')
        target = {theta(x, alpha) for x in tree}
        check(initial(target), 'initial_image')
        check(min(target, key=cmp_to_key(compare)) == '', 'image_minimum_zero')
        # "D" flags record exactly those coefficient groups forced to
        # contain all dyadic rationals by the right-ancestor condition.
        forced = set().union(*(right_ancestors(x) for x in tree))
        target_forced = set().union(*(right_ancestors(y) for y in target))
        check(target_forced <= {theta(x, alpha) for x in forced},
              'no_new_dyadic_obligation')
        spine = {'+' + '-'*beta for beta in range(alpha)}
        check(spine <= {theta(x, alpha) for x in forced}, 'forced_spine')

    # All 677 initial trees grafted above the positive child, together with
    # the root 0; these are all nonnegative initial trees of depth <= 4.
    for subtree in trees:
        delta = {''} | {'+' + x for x in subtree}
        check(initial(delta), 'nonnegative_target_initial')
        for alpha in range(6):
            inverse = {psi(y, alpha) for y in delta}
            spine = {'+' + '-'*beta for beta in range(alpha)}
            check(initial(inverse) == (spine <= delta), 'inverse_spine_criterion')
            if spine <= delta:
                forced_target = set().union(*(right_ancestors(y) for y in delta))
                # The missing obligations are exactly the spine; permitting
                # D there must satisfy all source right-ancestor obligations.
                dyadic_target = forced_target | spine
                dyadic_source = {psi(y, alpha) for y in dyadic_target}
                forced_source = set().union(*(right_ancestors(x) for x in inverse))
                check(forced_source <= dyadic_source, 'inverse_coefficient_criterion')

    rng = random.Random(20260923)
    for _ in range(1500):
        alpha, n = rng.randrange(6), rng.randrange(5)
        p = '-'*alpha
        cone = [x for x in finite_words if compare(x, p) >= 0]
        def sample() -> Series:
            out = {x: Fraction(rng.randrange(-8, 9), 2**rng.randrange(4))
                   for x in rng.sample(cone, rng.randrange(0, 9))}
            out[p] = Fraction(rng.randrange(-8, 9), 2**n)
            return clean(out)
        a, b = sample(), sample()
        na, nb = normalize(a, alpha, n), normalize(b, alpha, n)
        check(unnormalize(na, alpha, n) == a, 'series_inverse')
        check(normalize(add(a, b), alpha, n) == add(na, nb), 'series_additive')
        check(sign(add(a, scale(b, Fraction(-1)))) ==
              sign(add(na, scale(nb, Fraction(-1)))), 'series_order')
        exponents = sorted(a, key=cmp_to_key(compare), reverse=True)
        image_exponents = sorted(na, key=cmp_to_key(compare), reverse=True)
        for k in range(len(exponents) + 1):
            trunc = {x: a[x] for x in exponents[:k]}
            ntrunc = {x: na[x] for x in image_exponents[:k]}
            check(normalize(trunc, alpha, n) == ntrunc, 'series_truncation')
        check(na.get('', Fraction(0)).denominator == 1, 'integer_constant')

    # Regression tests which specifically reject tempting stronger claims.
    check({theta(x, 1) for x in right_ancestors('-')} !=
          right_ancestors(theta('-', 1)), 'reject_global_right_ancestor_equality')
    check(theta('', 1) != '', 'normalization_need_not_fix_one_exponent')
    check(not initial({psi('', 1)}), 'reject_unconstrained_inverse')

    return {
        'status': 'PASS',
        'scope': 'Finite sign words, all depth-3 initial trees, and finite rational series only.',
        'not_a_verification_of': [
            'transfinite ordinal concatenation',
            'arbitrary set-supported Hahn sums',
            'the Ehrlich--Kaplan characterization',
            'a Lean formalization or independent mathematical review'],
        'max_source_word_length': 7,
        'number_of_initial_trees': len(trees),
        'random_series_pairs': 1500,
        'random_seed': 20260923,
        'total_assertions': sum(COUNTS.values()),
        'assertions_by_label': COUNTS,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', default='verification_report.json')
    args = parser.parse_args()
    report = main()
    with open(args.output, 'w', encoding='utf-8') as out:
        json.dump(report, out, indent=2)
        out.write('\n')
    print(json.dumps(report, indent=2))
