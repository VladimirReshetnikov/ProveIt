#!/usr/bin/env python3
"""89 operations: narrow binary packing with a borrowed product mask.

The 22 source polynomials are stated afresh. All 34 supplied unknowns
remain positive; x is unchanged and H,V,Tindex are the same fixed index.
Numerals and equality tests are free. See the two companion proofs.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round37_1980_binary_product_certificate as previous
from round13_1980_certificate import verify_primitives

OUT = Path(__file__).with_suffix('.json')
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES)
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUALITIES = [('n', 'q4') if pair == ('n', 'q8') else pair
              for pair in previous.EQUALITIES]
EQUATION_LABELS = list(previous.EQUATION_LABELS)


def make_schedule():
    replacements = {
        'S3q4': ('S3q4', '*', 'S2', 'q'),
        'Sin': ('Sin', '+', 'S3', 'S3q4'),
        'Sq4': ('Sq4', '*', 'Sin', 'q'),
        'Tq4': ('Tq4', '*', 'theta_lambda', 'q2'),
        'theta_q4': ('theta_q4', '*', 'th', 'q'),
    }
    expected = {
        'q8': ('q8', '*', 'q4', 'q4'),
        'S3q4': ('S3q4', '*', 'S3', 'q2'),
        'Sin': ('Sin', '+', 'S2', 'S3q4'),
        'Sq4': ('Sq4', '*', 'Sin', 'q2'),
        'Tq4': ('Tq4', '*', 'Tcoef', 'q2'),
        'theta_q4': ('theta_q4', '*', 'th', 'q4'),
    }
    result = []
    for row in previous.SCHEDULE:
        name = row[0]
        if name in expected:
            baseline.need(row == expected[name], 'exact predecessor instruction: '+name)
        if name != 'q8':
            result.append(replacements.get(name, row))
    baseline.need(previous.EQUALITIES[5] == ('n', 'q8'), 'only the packing scale changes')
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
    S = g+q*(product+q*(ell+e*q))
    Tplus = q*q*th*la+ell*(th*q-b)
    K, aux_u = D*(f*f-1), 2*r+1+j*c
    aux_y2 = s['y_aux']**2
    return [
        ell+s['sigma']+s['al']-q,
        b-x-s['beta'],
        q*q-1-la*(B-1),
        th+2-B,
        ell+e*q-s['V']-t*th,
        n-q**4,
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
        'S3q4','Sin','Sq4','S','SA','Tq4','theta_q4','mask_gap','indicator_mask','T','TB','R7']),
        'only the two packed words and their arithmetic dependents change')
    baseline.need('q8' not in env, 'the q8 multiplication is deleted')
    source, s = source_residuals(), SYM
    A, B = s['a']+2, s['H']+s['b']+2
    u = 2*s['r']+1+s['j']*s['c']
    corrections = {
        2: -s['la']*source[3],
        16: source[15]*(u*u-s['y_aux']**2),
        17: source[3]*(s['ka']+s['rho']*(source[3]-2*(A-B))),
    }
    baseline.need(len(source) == len(EQUALITIES) == 22, '22 complete source equations')
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
            certificate_residual_polynomial=sp.sstr(actual), source_residual_sign=sign,
            triangular_correction_polynomial=sp.sstr(sp.expand(correction))))
    for index in (3, 15):
        baseline.need(records[index]['triangular_correction_polynomial'] == '0',
                      'acyclic corrections have independently exact prerequisites')

    q, n, ell, e, g = (s[key] for key in ('q','n','l','e','g'))
    product = (e-ell)*(s['x']+g)**2
    old_S = g+q**2*(ell+e*q+q**2*product)
    new_S = g+q*(product+q*(ell+e*q))
    old_T = q**2*(1+s['th']*s['la'])+ell*(s['th']*q**4-s['b'])
    new_T = q**2*s['th']*s['la']+ell*(s['th']*q-s['b'])
    deltas = {5:q**8-q**4,
              6:-(new_S-old_S)*(n*n-n)-(new_T-old_T)*(n*n-1)}
    for index, (old, new) in enumerate(zip(previous.source_residuals(), source)):
        baseline.need(sp.expand(new-old-deltas.get(index, 0)) == 0,
                      'only scale and packed index source change: '+str(index))
    primitives, counts = verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 89 and counts == {'+':42, '*':47},
                  '89 operations with free fixed numerals')
    used = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
            if isinstance(operand, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, 'all positive inputs participate')
    baseline.need(len(NAMES) == 38 and len(PARAMETERS) == 4,
                  '34 positive unknowns and four supplied inputs')
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  'all source symbols are declared')
    numerals = sorted({operand for row in primitives for operand in (row['left'], row['right'])
                       if isinstance(operand, int)})
    baseline.need(numerals == [1,3,4], 'the same free literal numerals suffice')
    return dict(status='PASS', operations=89, straight_line_histogram=histogram,
        additions_and_multiplications_only=dict(additions=42, multiplications=47),
        unknowns=34, equations=22, equality_tests=22, parameters=PARAMETERS,
        positive_input_names=NAMES,
        positive_unknown_names=[name for name in NAMES if name not in PARAMETERS],
        primitive_instructions=primitives, equalities=EQUALITIES,
        residual_polynomials=records, changed_registers=changed_registers,
        changed_source_indices_zero_based=sorted(deltas),
        source_change_polynomials={str(i):sp.sstr(sp.expand(value)) for i,value in deltas.items()},
        literal_numerals=numerals,
        fixed_index='Unchanged: H=H0-1, V=ell0(2)+2^L*e0(2), Tindex=psi_2(L); raw x unchanged',
        before_exponents='0<S<n=q^4, 0<Tplus<2n, n<=r<3n^3, n>=64, 3L<=B<=n',
        after_exponents='Tplus<n; middle spill self-excludes before canonical code recovery',
        parity_for_half_parameter_pell='Canonical B divides g and ell; S,Tplus,r are even',
        proofs=['../1980/BINARY_PRODUCT_89_PROOF.md','../1980/BASE_TWO_PELL_89_PROOF.md'],
        supplementary_regression='round38_1980_binary_product_encoding.json',
        scope='Complete 89-operation arithmetic certificate; general universality and positive-domain equivalence are proved separately; fixed numerals and equality tests are free')


if __name__ == '__main__':
    receipt = verify_certificate()
    OUT.write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(receipt['status'], receipt['operations'], receipt['straight_line_histogram'])
    print(receipt['unknowns'], 'positive unknowns;', receipt['equations'], 'equalities')
