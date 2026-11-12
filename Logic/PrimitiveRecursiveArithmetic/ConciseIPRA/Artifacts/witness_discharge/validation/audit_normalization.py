"""Independent tests of the arity normalizer (no kernel substitution reuse).

This is an untrusted audit program, not part of the proof checker.
It compares against a named-variable normalizer and a natural-number
environment evaluator. Finite tests complement, rather than prove,
strong normalization and syntactic soundness.
"""
import argparse
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import random


class Limit(Exception):
    pass


def tick(budget):
    budget[0] -= 1
    if budget[0] < 0:
        raise Limit


def evaluate(term, free, bound=(), budget=None):
    """Standard interpretation with an independent environment, no substitution."""
    if budget is None:
        budget = [100000]
    tick(budget)
    if type(term) is int:
        if term == 0:
            return 0
        return free[-term - 1] if term < 0 else bound[term - 1]
    if len(term) == 2:
        assert term[0] == 0
        return 1 + evaluate(term[1], free, bound, budget)
    assert len(term) == 3
    count = evaluate(term[0], free, bound, budget)
    if count > 500:
        raise Limit
    state = evaluate(term[1], free, bound, budget)
    for _ in range(count):
        state = evaluate(term[2], free, (state,) + tuple(bound), budget)
        if state > 100000:
            raise Limit
    return state


def named(term, names, bound=()):
    if type(term) is int:
        if term == 0:
            return ('z',)
        return ('v', ('free', term) if term < 0 else bound[term - 1])
    if len(term) == 2:
        assert term[0] == 0
        return ('s', named(term[1], names, bound))
    assert len(term) == 3
    name = ('bound', next(names))
    return ('i', named(term[0], names, bound), named(term[1], names, bound),
            name, named(term[2], names, (name,) + tuple(bound)))


def named_formula(formula, names, bound=()):
    if len(formula) == 2:
        return ('e', named(formula[0], names, bound), named(formula[1], names, bound))
    assert len(formula) == 1
    y = ('bound', next(names))
    x = ('bound', next(names))
    return ('d', y, x, named_formula(formula[0], names, (y, x) + tuple(bound)))


def replace(term, source, value):
    if term[0] == 'v':
        return value if term[1] == source else term
    if term[0] == 'z':
        return term
    if term[0] == 's':
        return ('s', replace(term[1], source, value))
    if term[0] == 'e':
        return ('e', replace(term[1], source, value), replace(term[2], source, value))
    if term[0] == 'd':
        return term if source in term[1:3] else ('d', *term[1:3], replace(term[3], source, value))
    _, c, a, name, body = term
    return ('i', replace(c, source, value), replace(a, source, value), name,
            body if name == source else replace(body, source, value))


def normalize_named(term, budget=None):
    if budget is None:
        budget = [100000]
    tick(budget)
    tag = term[0]
    if tag in ('z', 'v'):
        return term
    if tag == 's':
        return ('s', normalize_named(term[1], budget))
    if tag == 'e':
        return ('e', normalize_named(term[1], budget), normalize_named(term[2], budget))
    if tag == 'd':
        return ('d', *term[1:3], normalize_named(term[3], budget))
    _, c, a, name, h = term
    c = normalize_named(c, budget)
    a = normalize_named(a, budget)
    h = normalize_named(h, budget)
    if c[0] == 'z':
        return a
    if c[0] == 's':
        old = normalize_named(('i', c[1], a, name, h), budget)
        return normalize_named(replace(h, name, old), budget)
    return ('i', c, a, name, h)


def arity(term, bound=()):
    tag = term[0]
    if tag == 'z':
        return 0
    if tag == 'v':
        return term[1][1] if term[1][0] == 'free' else bound.index(term[1]) + 1
    if tag == 's':
        return [0, arity(term[1], bound)]
    if tag == 'e':
        return [arity(term[1], bound), arity(term[2], bound)]
    if tag == 'd':
        return [arity(term[3], tuple(term[1:3]) + tuple(bound))]
    _, c, a, name, h = term
    return [arity(c, bound), arity(a, bound), arity(h, (name,) + tuple(bound))]


def random_term(rng, depth, bound=0, free=2):
    atoms = [0] + list(range(1, bound + 1)) + list(range(-free, 0))
    if depth == 0 or rng.random() < .36:
        return rng.choice(atoms)
    if rng.random() < .42:
        return [0, random_term(rng, depth - 1, bound, free)]
    return [random_term(rng, depth - 1, bound, free),
            random_term(rng, depth - 1, bound, free),
            random_term(rng, depth - 1, bound + 1, free)]


def random_formula(rng, depth, bound=0, free=3):
    if depth and rng.random() < .65:
        return [random_formula(rng, depth - 1, bound + 2, free)]
    return [random_term(rng, 3, bound, free), random_term(rng, 3, bound, free)]


def load(path):
    spec = importlib.util.spec_from_file_location('candidate', path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('checker', type=Path)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    kernel = load(args.checker)
    rng = random.Random(20261112)
    one = [0, 0]
    terms = [
        [one, one, [one, 1, [2, 0, 2]]],
        [one, -1, [one, 1, [2, 0, 2]]],
        [one, [0, -2], [one, 1, [2, 0, 2]]],
        [-1, 0, [1, 0, [0, 2]]],
        [-1, -2, [one, 1, [2, 0, 2]]],
    ] + [random_term(rng, 4) for _ in range(2500)]
    summary = {'checker_sha256': hashlib.sha256(args.checker.read_bytes()).hexdigest(),
               'terms': len(terms), 'named_comparisons': 0,
               'numeric_comparisons': 0, 'budget_skips': 0,
               'substitution_comparisons': 0, 'free_name_comparisons': 0,
               'formula_name_comparisons': 0,
               'malformed_rejections': 0}
    valuations = [(0, 0), (0, 1), (1, 0), (1, 2), (2, 1), (2, 2)]
    for term in terms:
        try:
            expect = arity(normalize_named(named(term, itertools.count())))
            actual = kernel.walk(term, lambda i, d: i, form=False)
            assert actual == expect, (term, actual, expect)
            kernel.syntax(actual, 2)
            assert kernel.walk(actual, lambda i, d: i, form=False) == actual
            summary['named_comparisons'] += 1
        except (Limit, RecursionError):
            summary['budget_skips'] += 1
            continue
        for values in valuations:
            try:
                left = evaluate(term, values)
                right = evaluate(actual, values)
                assert left == right, (term, values, left, actual, right)
                summary['numeric_comparisons'] += 1
            except Limit:
                summary['budget_skips'] += 1
    # Independently test bound substitution with open outer binder slots.
    # The replacement may contain those slots, so capture would be observable.
    for depth in (0, 1):
        for _ in range(500):
            outer = (('bound', -10), ('bound', -11))
            protected = (('bound', -12),) if depth else ()
            source = ('bound', -13)
            old_bound = protected + (source,) + outer
            new_bound = protected + outer
            term = random_term(rng, 3, bound=len(old_bound))
            value = random_term(rng, 3, bound=len(outer))
            names = itertools.count()
            try:
                left = named(term, names, old_bound)
                right = named(value, names, outer)
                expect = arity(normalize_named(replace(left, source, right)), new_bound)
                actual = kernel.sub(term, value, depth)
                assert actual == expect, ('substitution', depth, term, value, actual, expect)
                summary['substitution_comparisons'] += 1
            except (Limit, RecursionError):
                summary['budget_skips'] += 1
    # Name elimination replaces a negative parameter in one pass. Its target
    # can contain that same parameter; inserted syntax must not be rescanned.
    for _ in range(500):
        term = random_term(rng, 3, free=3)
        value = random_term(rng, 3, free=3)
        names = itertools.count()
        try:
            # Both arguments of Name are derived formula/term fragments and
            # hence are already normal. The callback intentionally does not
            # rescan inserted syntax, so test precisely that public invariant.
            left = normalize_named(named(term, names))
            right = normalize_named(named(value, names))
            term = arity(left)
            value = arity(right)
            expect = arity(normalize_named(replace(left, ('free', -3), right)))
            actual = kernel.walk(term, lambda i, d: value if i == -3 else i)
            assert actual == expect, ('free name', term, value, actual, expect)
            summary['free_name_comparisons'] += 1
        except (Limit, RecursionError):
            summary['budget_skips'] += 1
    for _ in range(400):
        names = itertools.count()
        formula = random_formula(rng, 3)
        value = random_term(rng, 3, free=3)
        try:
            old = normalize_named(named_formula(formula, names))
            new = normalize_named(named(value, names))
            normal_formula, normal_value = arity(old), arity(new)
            kernel.syntax(normal_formula, 3, True)
            expect = arity(normalize_named(replace(old, ('free', -3), new)))
            actual = kernel.walk(normal_formula, lambda i, d: normal_value if i == -3 else i)
            assert actual == expect, ('formula name', formula, value, actual, expect)
            kernel.syntax(actual, 3, True)
            summary['formula_name_comparisons'] += 1
        except (Limit, RecursionError):
            summary['budget_skips'] += 1
    malformed = [True, False, 0.0, None, {}, [], [0], [1, 0], [False, 0],
                 [0, True], [0, 0, 0, 0], ['z'], [0, 0, 2], [0, 0, -3],
                 [0, [0, 1], 0], [0, 0, [0]], [[0], 0, 0]]
    for value in malformed:
        try:
            kernel.syntax(value, 2)
        except Exception:
            summary['malformed_rejections'] += 1
        else:
            raise AssertionError(('malformed accepted', value))
    capture = [one, one, [one, 1, [2, 0, 2]]]
    assert kernel.walk(capture, lambda i, d: i, form=False) == one
    summary['capture_regression'] = {'raw': capture, 'normal': one}
    summary['status'] = 'PASS'
    text = json.dumps(summary, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text)


if __name__ == '__main__':
    main()
