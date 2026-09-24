#!/usr/bin/env python3
"""Exact 84-operation causal Boolean history relation; not universality."""
from pathlib import Path
import json
import sympy as sp

import round40_1980_moving_frame_components as previous
from round13_1980_certificate import verify_primitives

PARAMETERS = previous.PARAMETERS
OUTER_NAMES = previous.OUTER_NAMES
CORE_NAMES = previous.CORE_NAMES
NAMES, SYM = previous.NAMES, previous.SYM
OUTER = [('packed' if name == 'pack7' else name, op, left, right)
         for name, op, left, right in previous.OUTER
         if name not in ('pack8', 'packed')]
CORE = previous.CORE
SCHEDULE = OUTER + CORE
EQUALITIES = [(left, 'v' if left == 'Ibound' else right)
              for left, right in previous.EQUALITIES]


def source_residuals():
    source = previous.source_residuals()
    z = SYM
    Q = z['q']**2
    P = z['Dw']+Q*(z['Xw']+Q*(z['Ew']+Q*(z['Zw']+Q*(z['Bw']+z['hrow']))))
    source[7] = z['I']+z['alphaI']-z['v']
    source[10] = z['r']-(Q**8-P)*3*z['lam']-2*z['lam']
    return source


def verify_certificate():
    need = previous.previous.baseline.need
    need(len(OUTER) == 41 and len(CORE) == 43, '41 outer and 43 Pell instructions')
    env = dict(SYM)
    histogram = previous.previous.baseline.run_schedule(SCHEDULE, env)
    source = source_residuals()
    z = SYM
    aux_u = 2*z['r']+1+z['j']*z['c']
    correction = source[18]*(aux_u**2-z['y_aux']**2)
    records = []
    for index, ((left, right), residual) in enumerate(zip(EQUALITIES, source)):
        actual = sp.expand(env[left]-env[right])
        adjustment = correction if index == 19 else sp.Integer(0)
        if sp.expand(actual-residual-adjustment) == 0:
            sign = 1
        elif adjustment == 0 and sp.expand(actual+residual) == 0:
            sign = -1
        else:
            raise AssertionError('fresh residual mismatch at '+str(index))
        records.append(dict(index=index, equality=[left,right], source_sign=sign,
                            source=sp.sstr(sp.expand(residual)),
                            actual=sp.sstr(actual),
                            correction=sp.sstr(sp.expand(adjustment))))
    need(len(records) == len(source) == len(EQUALITIES) == 21, '21 source equations')
    need(records[18]['correction'] == '0', 'exact auxiliary prerequisite')
    primitives, counts = verify_primitives(SCHEDULE, env)
    need(len(primitives) == 84 and counts == {'+':39, '*':45}, 'exact 84 operations')
    need(len(OUTER_NAMES+CORE_NAMES) == 31, '31 positive unknowns')
    need(set(NAMES) <= {operand for row in SCHEDULE for operand in row[2:]} |
         {operand for pair in EQUALITIES for operand in pair}, 'all supplied inputs used')
    need(sp.expand(env['n2']-z['q']**24) == 0, 'squared scale is fully computed')
    packed = z['Dw']+z['q']**2*(z['Xw']+z['q']**2*(z['Ew']+z['q']**2*(
        z['Zw']+z['q']**2*(z['Bw']+z['hrow']))))
    need(sp.expand(env['packed']-packed) == 0, 'five fields with D least significant')
    need(('Ibound','v') in EQUALITIES, 'strengthened bound uses existing square root')
    return dict(status='ARITHMETIC_PASS_FOR_CAUSAL_BOOLEAN_HISTORY',
                arithmetic_status='PASS', universality_status='NOT_ESTABLISHED',
                operations=84, histogram=histogram, primitive_histogram=counts,
                parameters=PARAMETERS, positive_unknowns=OUTER_NAMES+CORE_NAMES,
                unknown_count=31, equations=21, outer_operations=41,
                retained_pell_operations=43,
                packed_fields=['Dw','Xw','Ew','Zw','Bw+hrow'],
                initial_bound='I+alphaI=v',
                primitive_instructions=primitives, equalities=EQUALITIES,
                residuals=records,
                proof_note='../1980/EXPLORATION_FIVE_PLANE_MOVING_FRAME.md',
                scope='Finite Rule110 moving-frame histories. Causal recovery of B Booleanity replaces its explicit mask plane. All-positive equivalence has a separate proof; no universal input or halt interface is claimed.')


if __name__ == '__main__':
    result = verify_certificate()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['arithmetic_status'],result['operations'],result['primitive_histogram'])
    print('Finite-history improvement only; the proved universal bound remains 90.')
