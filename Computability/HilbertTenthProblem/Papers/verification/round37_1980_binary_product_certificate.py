#!/usr/bin/env python3
"""90 operations: binary product-bound encoding and a matching Pell shift.

The new fixed-index compiler and both positive-domain directions are in
BINARY_PRODUCT_90_PROOF.md. The source equations below are stated afresh;
the checker compares their full expanded residuals with every equality.
Fixed numerals and equality tests are free.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round36_1980_product_bound_certificate as previous
from round13_1980_certificate import verify_primitives

OUT = Path(__file__).with_suffix('.json')
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES)
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUALITIES = list(previous.EQUALITIES)
EQUATION_LABELS = list(previous.EQUATION_LABELS)


def make_schedule():
    replacements = {
        'R2': ('R2', '+', 'Tcoef', 'la'),
        'a4': ('a4', '*', 4, 'a'),
        'a4m5': ('a4m5', '+', 'a4', 3),
    }
    expected = {
        'R2': ('R2', '+', 'Tcoef', 'three_lambda'),
        'a4': ('a4', '*', 8, 'a'),
        'a4m5': ('a4m5', '+', 'a4', 15),
        'three_lambda': ('three_lambda', '*', 3, 'la'),
    }
    result = []
    for row in previous.SCHEDULE:
        name = row[0]
        if name in expected:
            baseline.need(row == expected[name], 'exact predecessor instruction: '+name)
        if name != 'three_lambda':
            result.append(replacements.get(name, row))
    return result


SCHEDULE = make_schedule()


def source_residuals():
    s = SYM
    x, a, b, c, d, e, f, g, h, i, j, k, ell, n, o, q, r, ss, t, w = (
        s[name] for name in ('x','a','b','c','d','e','f','g','h','i','j',
                            'k','l','n','o','q','r','s','t','w'))
    B, A, C = s['H']+b+2, a+2, x+g
    D, U, Y = A*A-1, w*n*n, ss*n*n
    la, th = s['la'], s['th']
    product = (e-ell)*C*C
    S = g+q*q*(ell+e*q+q*q*product)
    Tplus = q*q*(1+th*la)+ell*(th*q**4-b)
    K, aux_u = D*(f*f-1), 2*r+1+j*c
    aux_y2 = s['y_aux']**2
    return [
        ell+s['sigma']+s['al']-q,
        b-x-s['beta'],
        q*q-1-la*(B-1),
        th+2-B,
        ell+e*q-s['V']-t*th,
        n-q**8,
        r-S*(n*n-n)-Tplus*(n*n-1),
        U*Y*Y*(U*Y*Y+1)*k*k-s['tau']*(s['tau']+1),
        c-Y*k-s['eta'],
        k-s['eta']-s['zeta'],
        k-r-1-h*U*Y,
        a-Y*(U+1),
        c-s['ka']-s['phi'],
        d-U-a*c-s['ga']*(4*a+3),
        d*d-D*c*c-1,
        (i*c*c)**2-D*(f*f-1),
        K*(aux_u*aux_u-aux_y2)-(1-aux_y2),
        s['mu']-q-s['ka']*(A-B)-s['rho']*(D-(A-B)**2),
        D*s['ka']**2+1-s['mu']**2,
        s['ka']-s['Tindex']-s['Delta']*a,
        product-s['sigma'],
        aux_u-c-o*f,
    ]


def verify_certificate():
    env, old_env = dict(SYM), dict(previous.SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    baseline.run_schedule(previous.SCHEDULE, old_env)
    changed_registers = sorted(name for name in env.keys() & old_env.keys()
                               if sp.expand(env[name]-old_env[name]) != 0)
    baseline.need(changed_registers == sorted([
        'R2','a4','a4m5','gam','R14','A','Ac2','R15','R16','Mod','rM','R18','Aka2','R19']),
        'only geometry and the changed Pell discriminant/modulus dependents change')
    baseline.need('three_lambda' not in env,
                  'the deleted numeral-times-lambda register is absent')
    source, s = source_residuals(), SYM
    A, B = s['a']+2, s['H']+s['b']+2
    u = 2*s['r']+1+s['j']*s['c']
    corrections = {
        2: -s['la']*source[3],
        16: source[15]*(u*u-s['y_aux']**2),
        17: source[3]*(s['ka']+s['rho']*(source[3]-2*(A-B))),
    }
    baseline.need(len(source) == len(EQUALITIES) == 22,
                  '22 fresh complete source equations and equality tests')
    records = []
    for index, ((left, right), residual) in enumerate(zip(EQUALITIES, source)):
        actual = sp.expand(env[left]-env[right])
        correction = corrections.get(index, sp.Integer(0))
        if sp.expand(actual-residual-correction) == 0:
            sign = 1
        elif correction == 0 and sp.expand(actual+residual) == 0:
            sign = -1
        else:
            raise AssertionError('residual mismatch at '+EQUATION_LABELS[index])
        records.append(dict(equation=EQUATION_LABELS[index], equality=[left, right],
            source_residual_polynomial=sp.sstr(sp.expand(residual)),
            certificate_residual_polynomial=sp.sstr(actual),
            source_residual_sign=sign,
            triangular_correction_polynomial=sp.sstr(sp.expand(correction))))
    for index in (3, 15):
        baseline.need(records[index]['triangular_correction_polynomial'] == '0',
                      'acyclic corrections have independently exact prerequisites')

    old_source = previous.source_residuals()
    discriminant_difference = 4*s['a']+12
    deltas = {
        2: 2*s['la'],
        13: s['ga']*discriminant_difference,
        14: s['c']**2*discriminant_difference,
        15: (s['f']**2-1)*discriminant_difference,
        16: -(s['f']**2-1)*(u*u-s['y_aux']**2)*discriminant_difference,
        17: s['rho']*discriminant_difference,
        18: -s['ka']**2*discriminant_difference,
    }
    for index, (old, new) in enumerate(zip(old_source, source)):
        baseline.need(sp.expand(new-old-deltas.get(index, 0)) == 0,
                      'fresh source exactly matches the declared change: '+str(index))
    primitives, counts = verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 90 and counts == {'+':42, '*':48},
                  '90-operation histogram with fixed numerals free')
    used = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
            if isinstance(operand, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, 'all positive inputs participate')
    baseline.need(len(NAMES) == 38 and len(PARAMETERS) == 4,
                  '34 positive unknowns and four supplied inputs')
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  'all fresh source symbols are declared')
    numerals = sorted({operand for row in primitives for operand in (row['left'], row['right'])
                       if isinstance(operand, int)})
    baseline.need(numerals == [1,3,4], 'the binary-shift literals are free')
    return dict(status='PASS', operations=90, straight_line_histogram=histogram,
        additions_and_multiplications_only=dict(additions=42, multiplications=48),
        unknowns=34, equations=22, equality_tests=22,
        parameters=PARAMETERS, positive_input_names=NAMES,
        positive_unknown_names=[name for name in NAMES if name not in PARAMETERS],
        primitive_instructions=primitives, equalities=EQUALITIES,
        residual_polynomials=records, changed_registers=changed_registers,
        changed_source_indices_zero_based=sorted(deltas),
        source_change_polynomials={str(i):sp.sstr(sp.expand(value)) for i,value in deltas.items()},
        literal_numerals=numerals,
        implicit_positive_factor='sigma=(e-l)*(x+g)^2>0 and x+g>0 imply e-l>0; no supplied Omega is needed',
        fixed_index='Binary two-helper compiler: H=H0-1, V=ell0(2)+2^L*e0(2), Tindex=psi_2(L), e0=ell0+D',
        parity_for_half_parameter_pell='Canonical g and ell have zero radix-unit digit; even B and q imply S,Tplus,r even',
        proofs=['../1980/BINARY_PRODUCT_90_PROOF.md','../1980/BASE_TWO_PELL_90_PROOF.md'],
        supplementary_regression='round37_1980_binary_product_encoding.json',
        scope='complete 90-operation arithmetic certificate; universality and positive-domain equivalence are proved separately; fixed numerals and equality tests free')


if __name__ == '__main__':
    receipt = verify_certificate()
    OUT.write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(receipt['status'], receipt['operations'], receipt['straight_line_histogram'])
    print(receipt['unknowns'], 'positive unknowns;', receipt['equations'], 'equalities')
