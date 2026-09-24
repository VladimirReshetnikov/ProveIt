#!/usr/bin/env python3
"""Exact 82-operation finite history relation with an implicit packing bound."""
from pathlib import Path
import json
import sympy as sp

import round41_1980_causal_boolean_history as previous
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives

PARAMETERS = previous.PARAMETERS
OUTER_NAMES = [name for name in previous.OUTER_NAMES if name != 'alpha']
CORE_NAMES = previous.CORE_NAMES
NAMES = PARAMETERS + OUTER_NAMES + CORE_NAMES
SYM = {name: previous.SYM[name] for name in NAMES}
OUTER = [(name, op, 'Q4' if name == 'pack0' else left, right)
         for name, op, left, right in previous.OUTER
         if name not in ('ABC', 'bound')]
CORE = previous.CORE
SCHEDULE = OUTER + CORE
EQUALITIES = [(left,right) for left,right in previous.EQUALITIES if left != 'bound']


def source_residuals():
    source = previous.source_residuals()
    del source[6]
    z = SYM
    Q = z['q']**2
    P = z['Dw']+Q*z['Xw']+Q**2*z['Ew']+Q**3*z['Zw']+Q**7*(z['Bw']+z['hrow'])
    source[9] = z['r']-(Q**8-P)*3*z['lam']-2*z['lam']
    return source


def verify_certificate():
    need = baseline.need
    need(len(OUTER) == 39 and len(CORE) == 43, '39 outer and 43 Pell instructions')
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE,env)
    source = source_residuals()
    z = SYM
    aux_u = 2*z['r']+1+z['j']*z['c']
    correction = source[17]*(aux_u**2-z['y_aux']**2)
    records = []
    for index, ((left,right),residual) in enumerate(zip(EQUALITIES,source)):
        actual = sp.expand(env[left]-env[right])
        adjustment = correction if index == 18 else sp.Integer(0)
        if sp.expand(actual-residual-adjustment) == 0:
            sign = 1
        elif adjustment == 0 and sp.expand(actual+residual) == 0:
            sign = -1
        else:
            raise AssertionError('fresh residual mismatch at '+str(index))
        records.append(dict(index=index,equality=[left,right],source_sign=sign,
                            source=sp.sstr(sp.expand(residual)),actual=sp.sstr(actual),
                            correction=sp.sstr(sp.expand(adjustment))))
    need(len(records) == len(source) == len(EQUALITIES) == 20, '20 source equations')
    need(records[17]['correction'] == '0', 'exact auxiliary norm prerequisite')
    primitives, counts = verify_primitives(SCHEDULE,env)
    need(len(primitives) == 82 and counts == {'+':37,'*':45}, 'exact 82 operations')
    need(len(OUTER_NAMES+CORE_NAMES) == 30, '30 positive unknowns')
    need(set(NAMES) <= {operand for row in SCHEDULE for operand in row[2:]} |
         {operand for pair in EQUALITIES for operand in pair}, 'all supplied inputs used')
    need(all(residual.free_symbols <= set(SYM.values()) for residual in source),
         'deleted alpha does not survive in the source')
    need(sp.expand(env['n2']-z['q']**24) == 0, 'only squared Pell scale is materialized')
    Q = z['q']**2
    P = z['Dw']+Q*z['Xw']+Q**2*z['Ew']+Q**3*z['Zw']+Q**7*(z['Bw']+z['hrow'])
    need(sp.expand(env['packed']-P) == 0, 'sparse five-field packing uses existing Q4')
    need(('Ibound','v') in EQUALITIES, 'initial square-root guard retained')
    return dict(status='ARITHMETIC_PASS_FOR_IMPLICIT_BOUND_HISTORY',
                arithmetic_status='PASS',universality_status='NOT_ESTABLISHED',
                operations=82,histogram=histogram,primitive_histogram=counts,
                parameters=PARAMETERS,positive_unknowns=OUTER_NAMES+CORE_NAMES,
                unknown_count=30,equations=20,outer_operations=39,
                retained_pell_operations=43,
                packing='D+Q*X+Q^2*E+Q^3*Z+Q^7*(B+hrow)',
                range_source='Positive r in the special packing; no explicit tableau bound equation',
                initial_bound='I+alphaI=v',primitive_instructions=primitives,
                equalities=EQUALITIES,residuals=records,
                proof_note='../1980/EXPLORATION_IMPLICIT_BOUND_MOVING_FRAME.md',
                scope='Exact finite Rule110 moving histories with implicit bounds and causal Boolean decoding. The final physical row can extend one position beyond the packed source width. No universal input or halt interface is established.')


if __name__ == '__main__':
    result = verify_certificate()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['arithmetic_status'],result['operations'],result['primitive_histogram'])
    print('Finite-history improvement only; the proved universal bound remains 90.')
