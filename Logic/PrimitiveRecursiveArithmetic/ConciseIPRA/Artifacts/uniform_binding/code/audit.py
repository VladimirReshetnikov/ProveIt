"""Independent finite audit of the delivered counter-recursion checker.

Usage: python3 audit_counter_portable.py --checker code/checker.py
       --output evidence/independent_audit.json
This script is untrusted test code and is never imported by the checker.
"""
import argparse
import hashlib
import importlib.util
import json
import random
from pathlib import Path


def load(path):
    spec = importlib.util.spec_from_file_location('delivered_checker', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def well_term(a, scope, bound=0):
    if isinstance(a, bool):
        return False
    if isinstance(a, int):
        return a == 0 or 1 <= a <= bound or -scope <= a < 0
    if not isinstance(a, list) or len(a) != 3:
        return False
    n, seed, body = a
    if n == 0 and (type(body) is not int or body != 0):
        return False
    return well_term(n, scope, bound) and well_term(seed, scope, bound) and well_term(body, scope, bound + 2)


def well_formula(a, scope, bound=0):
    if not isinstance(a, list):
        return False
    if len(a) == 1:
        return well_formula(a[0], scope, bound + 2)
    return len(a) == 2 and all(well_term(t, scope, bound) for t in a)


def accepts_syntax(checker, a, scope, form):
    try:
        checker.syntax(a, scope, form)
        return True
    except Exception:
        return False


def rec(n, a, h):
    return [n, a, 0 if type(n) is int and n == 0 else h]


def numeral(n):
    a = 0
    for _ in range(n):
        a = [0, a, 0]
    return a


RNG = random.Random(741934)


def term(scope, bound, size):
    if size == 0 or RNG.randrange(3) == 0:
        return RNG.choice(list(range(-scope, bound + 1)))
    return rec(term(scope, bound, size - 1), term(scope, bound, size - 1), term(scope, bound + 2, size - 1))


def raw(size):
    if size == 0 or RNG.randrange(2) == 0:
        return RNG.choice([-5, -2, -1, 0, 1, 2, 3, 5, False, True, None, '', 0.0])
    return [raw(size - 1) for _ in range(RNG.randrange(5))]


def evaluate(a, free, bound=(), budget=None):
    if budget is None:
        budget = [30000]
    budget[0] -= 1
    if budget[0] < 0:
        raise OverflowError('finite audit budget')
    if type(a) is int:
        return 0 if a == 0 else bound[a - 1] if a > 0 else free[-a - 1]
    n = evaluate(a[0], free, bound, budget)
    value = evaluate(a[1], free, bound, budget) + 1
    if n > 1000:
        raise OverflowError('finite audit counter')
    for counter in range(n):
        value = evaluate(a[2], free, (value, counter) + bound, budget)
    return value


def template_apply(a, value, depth=0):
    """Replace the reserved free placeholder -3; lift a bound-counter value."""
    if type(a) is int:
        return (value + depth if type(value) is int and value > 0 else value) if a == -3 else a
    return rec(*(template_apply(v, value, depth + (2 if j == 2 else 0)) for j, v in enumerate(a)))


def use(index):
    return ['u', index, 0, None]


def join(s, t, r, p, q):
    return ['v', s, t, 0, 2, p, ['v', s, r, 0, 2, q, None]]


def congruence(s, t, body, p):
    return ['v', s, t, 0, body, p, ['v', s, s, 0, body, None, None]]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checker', type=Path, default=Path(__file__).with_name('checker.py'))
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    checker = load(args.checker)
    syntax_count = 0
    malformed = [[], [[]], [0], [0, 0, False], [0, 0, 1], [0, 0, []], [1, 0, 3], [1, 0, [0, 0, 4]]]
    corpus = malformed + [raw(3) for _ in range(1800)]
    for scope in range(4):
        corpus += [term(scope, 0, 3) for _ in range(100)]
        for a in corpus:
            for form in (False, True):
                expected = (well_formula if form else well_term)(a, scope)
                actual = accepts_syntax(checker, a, scope, form)
                if expected != actual:
                    raise AssertionError((scope, form, a, expected, actual))
                syntax_count += 1
    erased_body_rejections = 0
    for bad_body in (False, True, None, '', 0.0, [], [0, 0], [0, 0, 0], 3, -2, 1, 2):
        bad_term = [0, 0, bad_body]
        if accepts_syntax(checker, bad_term, 1, False):
            raise AssertionError(('erased malformed or noncanonical body', bad_term))
        erased_body_rejections += 1
    opening_count = 0
    skipped = 0
    for _ in range(900):
        scope, depth = RNG.randrange(4), RNG.randrange(1, 5)
        a, value = term(scope, depth, 2), term(scope, 0, 1)
        free = tuple(RNG.randrange(3) for _ in range(scope))
        bound = tuple(RNG.randrange(3) for _ in range(depth))
        cut = RNG.randrange(depth)
        try:
            substituted_value = evaluate(value, free)
            before = evaluate(a, free, bound[:cut] + (substituted_value,) + bound[cut+1:])
            opened = checker.opening(a, value, cut)
            if not well_term(opened, scope, depth - 1):
                raise AssertionError(('scope after opening', a, value, cut, opened))
            after = evaluate(opened, free, bound[:cut] + bound[cut+1:])
            if before != after:
                raise AssertionError(('opening value', a, value, cut, before, after))
            opening_count += 1
        except OverflowError:
            skipped += 1
    ce_count = 0
    for h in [1, 2, rec(2, 1, 1), rec(1, 2, 2)] + [term(2, 2, 1) for _ in range(300)]:
        free = (RNG.randrange(3), RNG.randrange(3))
        target, seed = -1, -2
        source = rec(numeral(1), 0, target)
        left = rec(rec(0, source, 0), seed, h)
        try:
            expected = evaluate(left, free)
            rhs = checker.opening(checker.opening(h, rec(target, seed, h)), target)
            if evaluate(rhs, free) != expected:
                raise AssertionError(('counter/state order', h, free, expected, rhs))
            ce_count += 1
        except OverflowError:
            skipped += 1
    macro_count = 0
    for _ in range(160):
        s, t, r = term(2, 0, 2), term(2, 0, 2), term(2, 0, 2)
        f = term(3, 0, 3)
        fs, ft = template_apply(f, s), template_apply(f, t)
        body = template_apply(f, 2)
        context = [([0, 0], [s, t]), ([0, 0], [fs, r])]
        con = congruence(s, t, body, use(0))
        proof = join(fs, ft, r, con, use(1))
        checker.prove([r, ft], proof, context)
        macro_count += 1
    result = {'syntax_agreements': syntax_count, 'semantic_opening_agreements': opening_count,
              'malformed_or_noncanonical_erased_bodies_rejected': erased_body_rejections,
              'counter_evaluation_semantic_agreements': ce_count,
              'arbitrary_template_transport_proofs': macro_count,
              'resource_limited_random_cases_skipped': skipped,
              'checker_sha256': hashlib.sha256(args.checker.read_bytes()).hexdigest(),
              'seed': 741934}
    print(json.dumps(result, indent=2))
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
