#!/usr/bin/env python3
"""Exact 86-operation moving-frame history components; no universality claim."""
from pathlib import Path
import json
import sympy as sp

import round39_1980_boolean_history_components as previous
from round13_1980_certificate import verify_primitives

PARAMETERS = previous.PARAMETERS
OUTER_NAMES = previous.OUTER_NAMES
CORE_NAMES = previous.CORE_NAMES
NAMES, SYM = previous.NAMES, previous.SYM
OUTER = [(name, op, 'Cw' if name == 'time_rhs' else left, right)
         for name, op, left, right in previous.OUTER]
CORE = previous.CORE
SCHEDULE = OUTER + CORE
EQUALITIES = previous.EQUALITIES


def source_residuals():
    residuals = previous.source_residuals()
    z = SYM
    residuals[8] = z['I'] + z['v']**2*z['Yw'] - z['Cw'] - z['q']**2*z['F']
    return residuals


def verify_certificate():
    need = previous.baseline.need
    need(len(OUTER) == len(CORE) == 43, '43 outer and 43 Pell instructions')
    differences = [(old, new) for old, new in zip(previous.SCHEDULE, SCHEDULE)
                   if old != new]
    need(differences == [(('time_rhs','+','Bw','QF'),
                          ('time_rhs','+','Cw','QF'))],
         'only the temporal right hand operand changes')
    env = dict(SYM)
    histogram = previous.baseline.run_schedule(SCHEDULE, env)
    source = source_residuals()
    z = SYM
    aux_u = 2*z['r'] + 1 + z['j']*z['c']
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
    need(records[18]['correction'] == '0', 'exact norm prerequisite')
    primitives, counts = verify_primitives(SCHEDULE, env)
    need(len(primitives) == 86 and counts == {'+':40, '*':46}, 'exact 86 operations')
    need(len(OUTER_NAMES+CORE_NAMES) == 31, '31 positive unknowns')
    need(all('n' not in row and 'ka' not in row for row in CORE), 'squared scale only')
    need(sp.expand(env['n2']-z['q']**24) == 0, 'correct squared Pell scale')
    return dict(status='ARITHMETIC_PASS_FOR_MOVING_FRAME_COMPONENTS',
                arithmetic_status='PASS', universality_status='OPEN_NOT_ENCODED',
                operations=86, histogram=histogram, primitive_histogram=counts,
                parameters=PARAMETERS, positive_unknowns=OUTER_NAMES+CORE_NAMES,
                unknown_count=31, equations=21, outer_operations=43,
                retained_pell_operations=43, changed_instructions=differences,
                primitive_instructions=primitives, equalities=EQUALITIES,
                residuals=records,
                proof_note='../1980/EXPLORATION_MOVING_FRAME_BOOLEAN_HISTORY.md',
                scope='Exact arithmetic for finite zero-exterior Rule110 histories in a one-cell moving frame. A universal raw-input and halting interface has not been proved.')


if __name__ == '__main__':
    result = verify_certificate()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(result['arithmetic_status'], result['operations'], result['primitive_histogram'])
    print('Universality OPEN: no finite-input Rule110 universality theorem is asserted.')
