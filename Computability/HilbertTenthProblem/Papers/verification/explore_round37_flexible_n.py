#!/usr/bin/env python3
"""Exact arithmetic audit of a rejected 89-operation source.

This is deliberately not a universal-representation certificate.  The full
common-shift counterexample transfer is in
EXPLORATION_PELL_AFTER_BINARY_PRODUCT.md.  Only the proposed source and its
89 primitive statements are verified here; no huge Pell witness is built.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round37_1980_binary_product_certificate as previous
from round13_1980_certificate import verify_primitives


def verify():
    schedule = []
    removed = []
    for row in previous.SCHEDULE:
        if row[0] in {'q8', 'bound_sum', 'L1'}:
            removed.append(row)
            continue
        schedule.append(row)
        if row[0] == 'S':
            schedule.extend([
                ('flexible_size', '+', 'S', 'al'),
                ('flexible_n', '*', 'q4', 'flexible_size'),
            ])
    assert removed == [
        ('q8', '*', 'q4', 'q4'),
        ('bound_sum', '+', 'l', 'sigma'),
        ('L1', '+', 'bound_sum', 'al'),
    ]
    equality_pairs = [pair for index, pair in enumerate(previous.EQUALITIES)
                      if index != 0]
    assert equality_pairs[4] == ('n', 'q8')
    equality_pairs[4] = ('n', 'flexible_n')
    s = previous.SYM
    C = s['x'] + s['g']
    source_S = s['g'] + s['q']**2 * (
        s['l'] + s['e']*s['q'] + s['q']**2*(s['e']-s['l'])*C**2)
    old_source = previous.source_residuals()
    source = old_source[1:]
    source[4] = s['n'] - s['q']**4*(source_S+s['al'])
    env = dict(s)
    raw_counts = previous.baseline.run_schedule(schedule, env)
    u = 2*s['r']+1+s['j']*s['c']
    A, B = s['a']+2, s['H']+s['b']+2
    corrections = {
        1: -s['la']*source[2],
        15: source[14]*(u*u-s['y_aux']**2),
        16: source[2]*(s['ka']+s['rho']*(source[2]-2*(A-B))),
    }
    records = []
    assert len(source) == len(equality_pairs) == 21
    for index, ((left, right), residual) in enumerate(zip(equality_pairs, source)):
        actual = sp.expand(env[left]-env[right])
        correction = sp.expand(corrections.get(index, 0))
        if sp.expand(actual-residual-correction) == 0:
            sign = 1
        elif correction == 0 and sp.expand(actual+residual) == 0:
            sign = -1
        else:
            raise AssertionError(('source residual mismatch', index))
        records.append(dict(index=index, equality=[left, right], source_sign=sign,
            source_residual=sp.sstr(sp.expand(residual)),
            actual_residual=sp.sstr(actual), correction=sp.sstr(correction)))
    primitives, counts = verify_primitives(schedule, env)
    assert len(primitives) == 89 and counts == {'+': 41, '*': 48}
    assert len(s) - len(previous.PARAMETERS) == 34
    return dict(status='ARITHMETIC_PASS_BUT_REPRESENTATION_REFUTED',
        operations=89, additions=41, multiplications=48, unknowns=34,
        equality_tests=21, raw_operation_counts=raw_counts,
        parameters=previous.PARAMETERS, positive_inputs=previous.NAMES,
        primitive_instructions=primitives, equalities=equality_pairs,
        residual_polynomials=records,
        source_change='Delete ell+sigma+alpha=q; replace n=q^8 by n=q^4*(S+alpha).',
        obstruction='../1980/EXPLORATION_PELL_AFTER_BINARY_PRODUCT.md',
        scope='Exact arithmetic/source equivalence only. The common-shift alias '
              'extends to every positive Pell witness, so this is not a '
              'universal encoding of the intended represented set.')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(result, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(result['status'], result['operations'], result['raw_operation_counts'])
    print(result['unknowns'], 'positive unknowns;', result['equality_tests'], 'equalities')
