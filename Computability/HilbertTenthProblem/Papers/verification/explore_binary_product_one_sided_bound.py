#!/usr/bin/env python3
"""Sparse corroboration of the binary one-sided-product-bound alias.

This is a finite code/mask check, not an instantiated universal Pell
witness. The general positive extension is proved in the companion note.
The sample's false assignment does not assert nonmembership of its input;
the separate inconsistent circuit in the note establishes nonmembership.
"""
from collections import defaultdict
import json
from pathlib import Path

from round37_1980_binary_product_encoding import (
    assignment, make_layout, raw_low, symbolic_checks,
)
from round30_1980_linear_radix_encoding import need, next_power_two, sparse_digits


def radix_digits(value, radix, count):
    out = []
    for _ in range(count):
        out.append(value % radix)
        value //= radix
    need(value == 0, 'radix expansion fits the claimed width')
    return out


def verify():
    layout = make_layout()
    structure = symbolic_checks(layout)
    names = [name for name, _ in layout['rows']]
    positive = layout['targets'][names.index('zero+')]
    negative = layout['targets'][names.index('zero-')]
    K = layout['K']
    L = next_power_two(3*K+3)
    records = []
    for H0, x in ((64, 1), (64, 7), (64, 64), (256, 257)):
        logical = dict(x=x, delta=1, V0=x, V1=x, X=x, Y=x, Z=x,
                       dc=1, u=x*x-1, v=x*x, a=x+1, z=x*x+x+1, zero=1)
        values = assignment(layout, logical, H0)
        bound = len(layout['D'])*sum(values.values())**2
        B = next_power_two(max(64*bound+1, 4*H0, H0+x+2))
        b, theta = B-H0-1, B-2
        raw = raw_low(layout, values)
        for target, (name, _) in zip(layout['targets'], layout['rows']):
            expected = 2 if name == 'zero+' else -2 if name == 'zero-' else (
                1 if name.startswith('unit_') else 0)
            need(raw.get(target, 0) == expected, 'only one ordinary pair is false')
        positions = set(layout['indicator']) | {
            start+offset for start in layout['starts'] for offset in range(-6, 3)}
        original, _, _ = sparse_digits(raw, positions, B)
        need(original[positive]['digit'] == 2, 'the binary mask rejects the positive row')
        need(any(original[negative+i]['digit'] >= 2 for i in range(3)),
             'the binary mask rejects the negative row')

        # m0=(B^2-2)B^positive + (B+2)B^negative. Its signed sparse
        # expression cancels both false coefficients exactly.
        repaired = defaultdict(int, raw)
        repaired[positive] -= 2
        repaired[positive+2] += 1
        repaired[negative] += 2
        repaired[negative+1] += 1
        digits, events, _ = sparse_digits(repaired, positions, B)
        need(all(digits[p]['digit'] <= 1 for p in layout['indicator']),
             'all canonical indicator windows pass after the common-code shift')
        positive_window = [digits[positive+i]['digit'] for i in range(3)]
        negative_window = [digits[negative+i]['digit'] for i in range(3)]
        need(positive_window == [0, 0, 1] and negative_window == [0, 1, 0],
             'both false rows have the exact claimed binary repairs')

        product_plus = radix_digits((B*B-2)*b, B, 3)
        product_minus = radix_digits((B+2)*b, B, 2)
        need(product_plus == [2*H0+2, B-2, B-H0-2], 'positive-row product digits')
        need(product_minus == [B-2*H0-2, B-H0], 'negative-row product digits')
        mask_plus = [theta-d for d in product_plus]
        mask_minus = [theta-d for d in product_minus]
        need(mask_plus == [B-2*H0-4, 0, H0], 'positive-row mask digits')
        need(mask_minus == [2*H0, H0-2], 'negative-row mask digits')
        need(all(0 <= d < B and d & 1 == 0 for d in mask_plus+mask_minus),
             'every changed middle-mask digit passes canonical ell digit one')
        for start, count in ((positive, 3), (negative, 2)):
            need(all(start+i in layout['indicator'] for i in range(count)),
                 'all low changes lie in the specified indicator windows')
        need(positive+3 < negative and negative+3 < K,
             'corrections are disjoint and below the code bound')

        # theta=2*(B/2-1); q^2 supplies its power-of-two factor.
        modulus = B//2-1
        low_residue = ((B*B-2)*pow(B, positive, modulus)
                       +(B+2)*pow(B, negative, modulus)) % modulus
        high_power = pow(B, K+1, modulus)
        adjustment = (-low_residue*pow(high_power, -1, modulus)) % modulus
        need((low_residue+adjustment*high_power) % modulus == 0,
             'the alias coefficient is divisible by the odd part of theta')
        m_mod_theta = ((B*B-2)*pow(B, positive, theta)
                       +(B+2)*pow(B, negative, theta)
                       +adjustment*pow(B, K+1, theta)) % theta
        need(m_mod_theta*pow(B, 2*L, theta)*(pow(B, L, theta)+1) % theta == 0,
             'the exact fixed-congruence increment is divisible by theta')

        high_product = radix_digits(adjustment*b, B, 2)
        borrow = 0
        high_mask = []
        for value in high_product:
            difference = theta-value+borrow
            high_mask.append(difference % B)
            borrow = difference // B
        need(borrow == 0 and high_product[1] < B//2,
             'the untested high adjustment borrow clears within two positions')
        need(K+4 < L and 3*K < L and adjustment < B//2,
             'all mask corrections remain below the e block and outside low tests')
        records.append(dict(x=x, H0=H0, B=B, false_raw_pair=[2,-2],
                            repaired_positive_digits=positive_window,
                            repaired_negative_digits=negative_window,
                            changed_middle_plus=mask_plus,
                            changed_middle_minus=mask_minus,
                            congruence_adjustment=adjustment,
                            untested_high_mask_digits=high_mask,
                            sparse_events=events))
    return dict(status='PASS',
                scope='Finite sparse binary-code, common-shift, mask, and congruence checks only; the separate note proves the inconsistent-circuit and full positive extension arguments. Toy fixed thresholds here do not instantiate the full admissible index or huge Pell witnesses.',
                structure=structure, cases=records,
                tested_starts=len(layout['starts']), indicator_digits=len(layout['indicator']))


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(result['status'], len(result['cases']), 'binary false-pair repairs;',
          result['indicator_digits'], 'indicator positions each')
