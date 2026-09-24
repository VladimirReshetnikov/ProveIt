#!/usr/bin/env python3
"""A bounded code alias when the product system only bounds sigma.

Finite sparse compiler check of the false-row repair. The general note
establishes the symbolic large-block identities and positive extension.
This script does not construct the huge full universal Pell witnesses.
"""
from collections import defaultdict
import json
from pathlib import Path

from round36_1980_product_bound_encoding import (
    assignment, make_layout, raw_low, symbolic_checks,
)
from round30_1980_linear_radix_encoding import need, next_power_two, sparse_digits


def verify():
    layout = make_layout()
    symbolic_checks(layout)
    names = [name for name, _ in layout['rows']]
    negative = layout['targets'][names.index('zero-')]
    positive = layout['targets'][names.index('zero+')]
    K = layout['K']
    L = next_power_two(3*K+3)
    records = []
    for H0, x in ((64, 1), (64, 7), (64, 64), (256, 257)):
        logical = dict(x=x, delta=1, V0=x, V1=x, X=x, Y=x, Z=x,
                       dc=1, u=x*x-1, v=x*x, a=x+1, z=x*x+x+1, zero=1)
        values = assignment(layout, logical, H0)
        coefficient_bound = len(layout['D'])*sum(values.values())**2
        B = next_power_two(max(64*coefficient_bound+1, 4*H0, H0+x+2))
        b, theta = B-H0-1, B-4
        raw = raw_low(layout, values)
        need(raw[negative] == -2 and raw[positive] == 2,
             'exactly the zero-row pair is deliberately false')
        for target, (name, _) in zip(layout['targets'], layout['rows']):
            expected = -2 if name == 'zero-' else 2 if name == 'zero+' else (
                1 if name.startswith('unit_') else 0)
            need(raw.get(target, 0) == expected, 'all other main targets are true')

        positions = set(layout['indicator']) | {
            start+offset for start in layout['starts'] for offset in range(-6, 3)}
        original, _, _ = sparse_digits(raw, positions, B)
        need(any(original[negative+i]['digit'] >= 4 for i in range(3)),
             'the original signed test rejects the false negative row')
        repaired = defaultdict(int, raw)
        repaired[negative] += 2
        repaired[negative+1] += 1
        digits, events, _ = sparse_digits(repaired, positions, B)
        need(all(digits[p]['digit'] < 4 for p in layout['indicator']),
             'the shifted effective third block passes every indicator')
        need([digits[negative+i]['digit'] for i in range(3)] == [0, 1, 0],
             'the false negative row is repaired to an allowed window')

        # m0=(B+2) B^negative. These are its two exact digits after
        # multiplication by b; all untouched middle-mask digits are B-4.
        product = (B+2)*b
        product_digits = [product % B, product//B]
        need(product_digits == [B-2*H0-2, B-H0], 'exact two-digit mask perturbation')
        altered_mask = [B-4-d for d in product_digits]
        need(altered_mask == [2*H0-2, H0-4], 'no borrow outside the two positions')
        need(all(0 <= digit < B and (digit & 1) == 0 for digit in altered_mask),
             'both perturbed middle digits pass the indicator digit one')
        need(negative in layout['indicator'] and negative+1 in layout['indicator'],
             'both perturbed positions have canonical ell digit one')

        # Enforce the fixed-index congruence by an untested high term.
        modulus = B//4-1
        low_residue = ((B+2)*pow(B, negative, modulus)) % modulus
        high_power = pow(B, K+1, modulus)
        coefficient = (-low_residue*pow(high_power, -1, modulus)) % modulus
        need((low_residue+coefficient*high_power) % modulus == 0,
             'm is divisible by the odd part of theta')
        m_mod_theta = ((B+2)*pow(B, negative, theta)
                       + coefficient*pow(B, K+1, theta)) % theta
        need(m_mod_theta*pow(B, 2*L, theta)*(pow(B, L, theta)+1) % theta == 0,
             'theta divides the exact packed-congruence increment')
        need(negative+2 < K and K+4 < L and 3*K < L,
             'high adjustment and aliased masks stay outside all low tests')
        need(coefficient < B and (B+2)*b < B*B,
             'm<B^(K+3), mb<q, and all stated block bounds are available')
        records.append(dict(x=x, H0=H0, B=B, false_raw_pair=[2, -2],
                            repaired_negative_digits=[0, 1, 0],
                            altered_middle_mask_digits=altered_mask,
                            congruence_adjustment_coefficient=coefficient,
                            sparse_events=events))
    return dict(status='PASS', scope='finite exact sparse alias and mask checks; full positive-witness argument is in the separate note',
                cases=records, tested_starts=len(layout['starts']),
                indicator_digits=len(layout['indicator']))


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(result['status'], len(result['cases']), 'false-row repairs;', result['indicator_digits'], 'indicator positions each')
