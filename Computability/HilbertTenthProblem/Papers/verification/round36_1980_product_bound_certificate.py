#!/usr/bin/env python3
"""91 operations: product-bound helper encoding and half-parameter Pell.

The new fixed-index compiler and both positive-domain directions are in
PRODUCT_BOUND_91_PROOF.md. The source equations below are stated afresh;
the checker compares their full expanded residuals with every equality.
Fixed numerals and equality tests are free.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round35_1980_half_parameter_pell_certificate as previous
from round13_1980_certificate import verify_primitives

OUT = Path(__file__).with_suffix('.json')
PARAMETERS = list(previous.PARAMETERS)
NAMES = [name for name in previous.NAMES if name != 'Omega']
SYM = {name: sp.Symbol(name) for name in NAMES}
REMOVED_SOURCE_INDEX = 21
EQUALITIES = [pair for index, pair in enumerate(previous.EQUALITIES)
              if index != REMOVED_SOURCE_INDEX]
EQUATION_LABELS = [label for index, label in enumerate(previous.EQUATION_LABELS)
                   if index != REMOVED_SOURCE_INDEX]
EQUATION_LABELS[0] = 'positive_product_bound'
EQUATION_LABELS[20] = 'positive_product'


def make_schedule():
    replacements = {
        't2': ('t2', '-', 'e', 'l'),
        'bound_sum': ('bound_sum', '+', 'l', 'sigma'),
        'S3': ('S3', '*', 't2', 'C2'),
    }
    expected = {
        't2': ('t2', '-', 'la', 'e'),
        'bound_sum': ('bound_sum', '+', 'l', 'e'),
        'S3': ('S3', '*', 't2', 'code_gap'),
        'code_gap': ('code_gap', '-', 'q', 'C2'),
    }
    result = []
    for row in previous.SCHEDULE:
        name = row[0]
        if name in expected:
            baseline.need(row == expected[name], 'exact predecessor instruction: '+name)
        if name != 'code_gap':
            result.append(replacements.get(name, row))
    baseline.need(previous.EQUALITIES[REMOVED_SOURCE_INDEX] == ('t2', 'Omega'),
                  'delete exactly the now-implied positive-coefficient equality')
    return result


SCHEDULE = make_schedule()


def source_residuals():
    s = SYM
    x, a, b, c, d, e, f, g, h, i, j, k, ell, n, o, q, r, ss, t, w = (
        s[name] for name in ('x','a','b','c','d','e','f','g','h','i','j',
                            'k','l','n','o','q','r','s','t','w'))
    B, A, C = s['H']+b+4, a+4, x+g
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
        th+4-B,
        ell+e*q-s['V']-t*th,
        n-q**8,
        r-S*(n*n-n)-Tplus*(n*n-1),
        U*Y*Y*(U*Y*Y+1)*k*k-s['tau']*(s['tau']+1),
        c-Y*k-s['eta'],
        k-s['eta']-s['zeta'],
        k-r-1-h*U*Y,
        a-Y*(U+1),
        c-s['ka']-s['phi'],
        d-U-a*c-s['ga']*(8*a+15),
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
        't2', 'bound_sum', 'L1', 'S3', 'S3q4', 'Sin', 'Sq4', 'S', 'SA', 'R7']),
        'only the product, bound, and dependent packed-source registers change')
    baseline.need('Omega' not in env and 'code_gap' not in env,
                  'the unused positive input and deleted subtraction are absent')
    source, s = source_residuals(), SYM
    A, B = s['a']+4, s['H']+s['b']+4
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
    aligned = old_source[:REMOVED_SOURCE_INDEX]+old_source[REMOVED_SOURCE_INDEX+1:]
    C = s['x']+s['g']
    old_product = (s['la']-s['e'])*(s['q']-C*C)
    new_product = (s['e']-s['l'])*C*C
    deltas = {
        0: s['sigma']-s['e'],
        6: -(new_product-old_product)*s['q']**4*(s['n']**2-s['n']),
        20: new_product-old_product,
    }
    for index, (old, new) in enumerate(zip(aligned, source)):
        baseline.need(sp.expand(new-old-deltas.get(index, 0)) == 0,
                      'fresh source exactly matches the declared change: '+str(index))
    baseline.need(sp.expand(old_source[REMOVED_SOURCE_INDEX]-
                           (s['la']-s['e']-previous.SYM['Omega'])) == 0,
                  'the omitted old source is precisely the old positive-factor condition')
    primitives, counts = verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 91 and counts == {'+':42, '*':49},
                  '91-operation histogram with fixed numerals free')
    used = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
            if isinstance(operand, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, 'all positive inputs participate')
    baseline.need(len(NAMES) == 38 and len(PARAMETERS) == 4,
                  '34 positive unknowns and four supplied inputs')
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  'all fresh source symbols are declared')
    numerals = sorted({operand for row in primitives for operand in (row['left'], row['right'])
                       if isinstance(operand, int)})
    baseline.need(numerals == [1,3,8,15], 'literal numerals are unchanged and free')
    return dict(status='PASS', operations=91, straight_line_histogram=histogram,
        additions_and_multiplications_only=dict(additions=42, multiplications=49),
        unknowns=34, equations=22, equality_tests=22,
        parameters=PARAMETERS, positive_input_names=NAMES,
        positive_unknown_names=[name for name in NAMES if name not in PARAMETERS],
        primitive_instructions=primitives, equalities=EQUALITIES,
        residual_polynomials=records, changed_registers=changed_registers,
        changed_aligned_source_indices_zero_based=[0,6,20],
        removed_predecessor_source_index_zero_based=REMOVED_SOURCE_INDEX,
        source_change_polynomials={str(i):sp.sstr(sp.expand(value)) for i,value in deltas.items()},
        literal_numerals=numerals,
        implicit_positive_factor='sigma=(e-l)*(x+g)^2>0 and x+g>0 imply e-l>0; no supplied Omega is needed',
        fixed_index='New two-helper compiler: H=H0-3, V=ell0(4)+4^L*e0(4), Tindex=psi_4(L), e0=ell0+D',
        parity_for_half_parameter_pell='Canonical g and ell have zero radix-unit digit; even B and q imply S,Tplus,r even',
        proofs=['../1980/PRODUCT_BOUND_91_PROOF.md','../1980/HALF_PARAMETER_PELL_92_PROOF.md'],
        supplementary_regression='round36_1980_product_bound_encoding.json',
        scope='complete 91-operation arithmetic certificate; universality and positive-domain equivalence are proved separately; fixed numerals and equality tests free')


if __name__ == '__main__':
    receipt = verify_certificate()
    OUT.write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(receipt['status'], receipt['operations'], receipt['straight_line_histogram'])
    print(receipt['unknowns'], 'positive unknowns;', receipt['equations'], 'equalities')
