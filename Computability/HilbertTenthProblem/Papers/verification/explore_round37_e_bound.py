#!/usr/bin/env python3
"""Exact 89-operation arithmetic audit of a refuted representation."""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round37_1980_binary_product_certificate as previous
from round13_1980_certificate import verify_primitives


def verify():
    schedule = []
    for row in previous.SCHEDULE:
        if row[0] == 'bound_sum':
            assert row == ('bound_sum', '+', 'l', 'sigma')
            continue
        if row[0] == 'L1':
            assert row == ('L1', '+', 'bound_sum', 'al')
            row = ('L1', '+', 'e', 'al')
        schedule.append(row)
    s = previous.SYM
    source = previous.source_residuals()
    source[0] = s['e']+s['al']-s['q']
    env = dict(s)
    raw_counts = previous.baseline.run_schedule(schedule, env)
    u = 2*s['r']+1+s['j']*s['c']
    A, B = s['a']+2, s['H']+s['b']+2
    corrections = {
        2: -s['la']*source[3],
        16: source[15]*(u*u-s['y_aux']**2),
        17: source[3]*(s['ka']+s['rho']*(source[3]-2*(A-B))),
    }
    records = []
    for index, ((left, right), residual) in enumerate(zip(previous.EQUALITIES, source)):
        actual = sp.expand(env[left]-env[right])
        correction = sp.expand(corrections.get(index, 0))
        if sp.expand(actual-residual-correction) == 0:
            sign = 1
        elif correction == 0 and sp.expand(actual+residual) == 0:
            sign = -1
        else:
            raise AssertionError(('source residual mismatch', index))
        records.append(dict(index=index, equality=[left,right], source_sign=sign,
            source_residual=sp.sstr(sp.expand(residual)),
            actual_residual=sp.sstr(actual), correction=sp.sstr(correction)))
    primitives, counts = verify_primitives(schedule, env)
    assert len(primitives) == 89 and counts == {'+':41,'*':48}
    assert len(source) == len(previous.EQUALITIES) == 22
    assert len(s)-len(previous.PARAMETERS) == 34
    U,Y,X = sp.symbols('U Y X')
    aa, pp = Y*(U+1)+2, 2*U*Y*Y+1
    assert sp.expand((2*aa-1)**2-2*pp-(
        4*Y*Y*(U*U+U+1)+12*Y*(U+1)+7)) == 0
    assert sp.expand((2*pp-1)-4*aa-(4*Y*(U*(Y-1)-1)-7)) == 0
    psi6 = 32*X**5-32*X**3+6*X
    assert sp.expand(psi6-X*(X*X-1)**2-(31*X**5-30*X**3+5*X)) == 0
    return dict(status='ARITHMETIC_PASS_BUT_REPRESENTATION_REFUTED',
        operations=89, additions=41, multiplications=48,
        raw_operation_counts=raw_counts, unknowns=34, equality_tests=22,
        parameters=previous.PARAMETERS, positive_inputs=previous.NAMES,
        primitive_instructions=primitives, equalities=previous.EQUALITIES,
        residual_polynomials=records,
        source_change='Replace ell+sigma+alpha=q by e+alpha=q; other sources unchanged.',
        proof='../1980/EXPLORATION_BINARY_E_BOUND.md',
        counterexample='../1980/EXPLORATION_BINARY_E_BOUND_COUNTEREXAMPLE.md',
        failed_case='The first Pell index is r+1+v*U*Y with v>=1 and r>U*Y; '
                    'quadratic equidistribution supplies full positive false witnesses.',
        scope='Exact arithmetic and source equivalence; canonical necessity and partial '
              'Pell bootstrap are proved in the note. The companion counterexample '
              'refutes the representation by a general density argument; no giant '
              'Pell witness is materialized and no 89-operation universality is claimed.')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(result, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(result['status'], result['operations'], result['raw_operation_counts'])
    print(result['unknowns'], 'positive unknowns;', result['equality_tests'], 'equalities')
