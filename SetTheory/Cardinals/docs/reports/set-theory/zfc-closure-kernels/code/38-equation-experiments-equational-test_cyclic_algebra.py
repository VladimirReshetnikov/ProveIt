#!/usr/bin/env python3
"""Finite semantic and adversarial witness checks for cyclic_algebra.py.

These tests are sanity checks, not replacements for the general algebraic proof.
The finite model checks cover all seven identities on a 64-element algebra whose
closure and rotation do not commute. Random checks use three distinct commuting
closures on a 256-element Boolean algebra. A separate counterexample guards
against the tempting but false extension to arbitrary equational premises.
"""

from itertools import product
import json
from random import Random

from cyclic_algebra import (BASIS, Move, basis_manifest, check, check_code,
                            context_apply, df_translate, evaluate, freeze, list_decode,
                            list_encode, move_decode, move_encode, n, q, r,
                            search, term_decode, term_encode, term_equal)


def variables(t):
    if isinstance(t, str):
        return {t}
    return set().union(*(variables(a) for a in t[1:]))


def semantic_checks():
    # A=P({0,1}) with f0=id, f1=indiscrete saturation, f2=id.
    universe_a = range(4)
    closures = (lambda a: a, lambda a: 3 if a else 0, lambda a: a)
    universe_b = list(product(universe_a, repeat=3))
    nand_a = lambda a, b: 3 ^ (a & b)
    nand_b = lambda a, b: tuple(nand_a(a[i], b[i]) for i in range(3))
    q_b = lambda a: tuple(closures[i](a[i]) for i in range(3))
    r_b = lambda a: (a[1], a[2], a[0])
    ops_b = {'n': nand_b, 'q': q_b, 'r': r_b}
    identities_checked = 0
    per_axiom = {}
    for name, left, right in BASIS:
        vs = sorted(variables(left) | variables(right))
        checked = 0
        for values in product(universe_b, repeat=len(vs)):
            binding = dict(zip(vs, values))
            assert evaluate(left, binding, ops_b) == evaluate(right, binding, ops_b), name
            checked += 1
        per_axiom[name] = checked
        identities_checked += checked
    # q and r themselves are NOT required to commute.
    witness = (0, 1, 0)
    assert q_b(r_b(witness)) != r_b(q_b(witness))
    # Explicit failure of preservation for arbitrary universal premises:
    # A |= f0(x)=x, but A !|= f1(x)=x. In the translated theory q=id
    # would imply r q r^2=id. Thus this Horn implication cannot be transported.
    assert all(closures[0](a) == a for a in universe_a)
    assert closures[1](1) != 1
    assert q_b(witness) != witness
    return {'finite_algebra_size': 64,
            'universal_identity_evaluations': identities_checked,
            'per_axiom': per_axiom,
            'noncommuting_q_r_witness': list(witness),
            'arbitrary_premise_counterexample_verified': True}


def translation_checks():
    # Three different existential cylinder maps on subsets of the 8 vertices
    # of a cube; Boolean elements are masks 0..255.
    def closure(index, mask):
        out = mask
        for atom in range(8):
            if mask & (1 << atom):
                out |= 1 << (atom ^ (1 << index))
        return out

    nand_a = lambda a, b: 255 ^ (a & b)
    closures = tuple(lambda a, i=i: closure(i, a) for i in range(3))
    for a in range(256):
        for i in range(3):
            for j in range(3):
                assert closures[i](closures[j](a)) == closures[j](closures[i](a))
    ops_b = {
        'n': lambda a, b: tuple(nand_a(a[i], b[i]) for i in range(3)),
        'q': lambda a: tuple(closures[i](a[i]) for i in range(3)),
        'r': lambda a: (a[1], a[2], a[0]),
    }
    rng = Random(20261016)

    def make_term(depth):
        if depth == 0 or rng.randrange(5) == 0:
            return 'c'
        tag = rng.randrange(4)
        if tag == 3:
            return n(make_term(depth - 1), make_term(depth - 1))
        return ('f' + str(tag), make_term(depth - 1))

    cases = 1200
    for _ in range(cases):
        t = make_term(5)
        a = rng.randrange(256)
        got = evaluate(df_translate(t), {'c': (a, a, a)}, ops_b)
        expected = []
        for shift in range(3):
            ops_a = {'n': nand_a}
            for i in range(3):
                ops_a['f' + str(i)] = closures[(i + shift) % 3]
            expected.append(evaluate(t, {'c': a}, ops_a))
        assert got == tuple(expected)
    return {'translation_cases_three_distinct_closures': cases,
            'base_boolean_algebra_size': 256,
            'all_three_product_coordinates_checked': True}


def certificate_checks():
    c = 'c'
    source = r(q(n(q(c), q(c))))
    target = n(r(q(c)), r(q(c)))
    good = [Move(5, False, 2, (0, 0, 0)), Move(1, False, 0, (1, 1, 0))]
    assert check(source, target, good)
    code = list_encode([move_encode(m) for m in good])
    assert check_code(source, target, code)
    negatives = [
        (source, q(target), good),
        (source, target, [Move(5, True, 2, (0, 0, 0)), good[1]]),
        (source, target, [Move(5, False, 1, (0, 0, 0)), good[1]]),
        (source, target, [Move(5, False, 2, (1, 0, 0)), good[1]]),
        (source, target, [Move(6, False, 2, (0, 0, 0)), good[1]]),
        (source, target, [Move(7, False, 2, (0, 0, 0)), good[1]]),
        (source, target, [Move(5, False, -1, (0, 0, 0)), good[1]]),
        (source, target, [Move(5, False, 2, (-1, 0, 0)), good[1]]),
        (source, target, good[:1]),
        (source, target, []),
    ]
    for s, t, cert in negatives:
        assert not check(s, t, cert)
    rejected_syntax = 0
    for bad in ('x', ('n', c), ('q', c, c), ('r', 'x'), ('unknown', c), 0, None):
        try:
            freeze(bad)
        except ValueError:
            rejected_syntax += 1
        else:
            raise AssertionError('accepted malformed ground term')
    assert search(r(r(r(c))), c, limit=12) == 11
    assert search(r(r(r(c))), q(c), limit=12) is None
    for k in range(5000):
        assert term_encode(term_decode(k)) == k
        assert list_encode(list(list_decode(k))) == k
        assert move_encode(move_decode(k)) == k
    return {'positive_chain_length': len(good),
            'negative_certificates_rejected': len(negatives),
            'malformed_ground_terms_rejected': rejected_syntax,
            'coding_roundtrips_each': 5000,
            'first_search_witness': 11}


def deep_term_checks():
    # Do not increase sys.setrecursionlimit: the candidate-checking path must
    # handle deeply nested finite syntax without a Python recursion cutoff.
    depth = 2000
    deep = deep_list = 'c'
    context = 0
    for _ in range(depth):
        deep = q(deep)
        deep_list = ['q', deep_list]
        context = 4 * context + 1
    encoded = term_encode(deep)
    assert term_equal(freeze(deep_list), deep)
    assert term_equal(term_decode(encoded), deep)
    assert term_equal(context_apply(context, 'c'), deep)
    assert check(r(r(r(deep))), deep, [Move(2, False, 0, (encoded, 0, 0))])
    source = context_apply(context, r(r(r('c'))))
    move = Move(2, False, context, (0, 0, 0))
    witness = list_encode([move_encode(move)])
    assert check_code(source, deep, witness)
    assert not check_code(source, context_apply(context, r('c')), witness)
    cyclic = ['q', None]
    cyclic[1] = cyclic
    try:
        freeze(cyclic)
    except ValueError:
        pass
    else:
        raise AssertionError('accepted a cyclic container as a finite term')
    return {'unary_depth': depth, 'recursive_call_limit_unchanged': True,
            'term_codec_context_and_certificates_passed': True,
            'cyclic_python_container_rejected': True}


def main():
    assert basis_manifest()['symbols_total'] == 88
    result = {'status': 'passed', 'basis': {'equations': 7, 'symbols': 88},
              'finite_models': semantic_checks(),
              'translation': translation_checks(),
              'certificates': certificate_checks(),
              'deep_terms': deep_term_checks(),
              'limitation': 'Finite checks are not a proof of the general theorem. '
                            'No Con(ZFC) payload or Turing-machine compilation included.'}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
