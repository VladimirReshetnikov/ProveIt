#!/usr/bin/env python3
"""Finite symbolic/carry regression for the 90-operation binary product.

This supplements BINARY_PRODUCT_90_PROOF.md and its separate arithmetic
certificate. It tests a sample circuit with two input helpers,
positive compensating coefficients at every negative-D test, and sparse
three-digit carries. No giant radix power is constructed.
"""
from collections import defaultdict
import json
from pathlib import Path

from round30_1980_linear_radix_encoding import (
    need, mono, polynomial, scaled, square_terms, target_polynomial,
    sparse_digits, next_power_two,
)
from round32_1980_affine_radix_encoding import expand_logical, split_bit_clear

OUT = Path(__file__).with_suffix('.json')


def make_layout():
    names = ['x', 'delta', 'V0', 'V1', 'X', 'Y', 'Z', 'dc', 'u',
             'v', 'a', 'z', 'zero']
    groups = {name: (name,) if name in ('x', 'delta') else
              tuple(name+'_'+str(i) for i in range(3)) for name in names}
    physical = [item for name in names for item in groups[name]]
    weights = {'x': 0}
    weights.update({name: 8*7**i for i, name in enumerate(physical[1:])})
    rows = []
    for i in (0, 1):
        own, other = 'V'+str(i), 'V'+str(1-i)
        rows.append((own+'_seed', polynomial((-1, 'x', 'x')), own,
                     polynomial((1, own, own), (-1, 'x', 'x'))))
        reverse = polynomial((2, 'x', 'delta'), (-2, own, 'delta'))
        rows.append((own+'_reverse', reverse, other, reverse))
    logical_rows = [
        ('copy_X', polynomial((1, 'X', 'X'), (-1, 'V0', 'V0'))),
        ('copy_Y', polynomial((1, 'Y', 'Y'), (-1, 'V0', 'V0'))),
        ('copy_Z', polynomial((1, 'Z', 'Z'), (-1, 'V0', 'V0'))),
        ('copy_delta', polynomial((1, 'dc', 'dc'), (-1, 'delta', 'delta'))),
        ('guard', polynomial((2, 'V0', 'X'), (-2, 'delta', 'dc'), (-2, 'u', 'delta'))),
        ('multiply', polynomial((2, 'V0', 'X'), (-2, 'v', 'delta'))),
        ('add_one', polynomial((2, 'V0', 'delta'), (2, 'delta', 'dc'), (-2, 'a', 'delta'))),
        ('add', polynomial((2, 'v', 'delta'), (2, 'a', 'delta'), (-2, 'z', 'delta'))),
        ('zero', polynomial((2, 'zero', 'delta'))),
    ]
    for name, poly in logical_rows:
        for sign in (1, -1):
            signed = scaled(poly, sign)
            rows.append((name+('+' if sign == 1 else '-'), signed, 'V1', signed))
    rows.extend((name, polynomial((1, 'delta', 'delta')), None,
                 polynomial((1, 'delta', 'delta')))
                for name in ('unit_plain', 'unit_double'))
    M = max(weights.values())
    spacing = 12*M+8
    targets = [(len(rows)+2)*spacing+8*M+i*spacing for i in range(len(rows))]
    D = defaultdict(int)
    starts = {}
    physical_rows = []
    for t, (name, poly, helper, expected) in zip(targets, rows):
        physical_poly = expand_logical(poly, groups)
        physical_expected = expand_logical(expected, groups)
        physical_rows.append((name, physical_expected))
        starts[t] = physical_expected
        for (left, right), coefficient in physical_poly.items():
            mult = 1 if left == right else 2
            need(coefficient % mult == 0 and coefficient//mult in (-1, 1),
                 'all base divided coefficients are +/-1')
            r = t-weights[left]-weights[right]
            D[r] += coefficient//mult
            if coefficient < 0:
                need(helper is not None, 'every negative term has a helper')
                if (left, right) != ('x', 'x'):
                    need(left not in groups[helper] and right not in groups[helper],
                         'augmenting helper group is disjoint from negative factors')
                for j, hleft in enumerate(groups[helper]):
                    for hright in groups[helper][j:]:
                        D[r-weights[hleft]-weights[hright]] += 1
                extra = expand_logical(polynomial((1, helper, helper), (-1, 'x', 'x')), groups)
                need(r not in starts or starts[r] == extra, 'coincident starts demand same polynomial')
                starts[r] = extra
    for start in starts:
        D[start-4] += 1
    for part in groups['X']:
        D[targets[-1]-1-weights[part]] += 1
    D = {key: val for key, val in D.items() if val}
    need(set(D.values()) <= {-1, 1}, 'all complementary coefficients remain +/-1')
    indicator = set(weights.values())-{0}
    for start in starts:
        indicator.update(range(start, start+3))
    need(all(exponent in indicator for exponent, val in D.items() if val < 0),
         'every negative coefficient is an indicator position')
    ecoeff = {p: D.get(p, 0)+int(p in indicator) for p in set(D)|indicator}
    need(all(exponent not in indicator for exponent, val in D.items() if val > 0),
         'every positive complementary coefficient lies off the indicator')
    need(set(ecoeff.values()) <= {0, 1}, 'canonical e has binary digits')
    return dict(weights=weights, groups=groups, physical=physical, D=D, starts=starts,
                rows=physical_rows, targets=targets, indicator=indicator, M=M,
                spacing=spacing, K=targets[-1]+3, e_coeff=ecoeff)


def symbolic_checks(layout):
    terms = square_terms(layout['weights'])
    D, starts, last = layout['D'], layout['starts'], layout['K']-1
    need(min(D) > layout['M'], 'all true-coordinate tests are below D')
    need(min(D)+min(starts) > last, 'dummy coordinates affect no low test or reset')
    need(min(D) > 0 and max(D) < layout['K'], 'short positive-degree complementary support')
    need(D[max(D)] > 0, 'leading +1 and coefficient digits +/-1 imply D(B)>0 for every B>=2')
    expected_pads = {}
    expected_pads[layout['targets'][-1]] = expand_logical(
        polynomial((2, 'x', 'X')), layout['groups'])
    extra_reset_terms = 0
    for start, expected in starts.items():
        need(target_polynomial(layout, start, terms) == expected, 'exact main/negative-position target')
        for offset in (-6, -5, -3, -2, 1, 2):
            need(target_polynomial(layout, start+offset, terms) == {}, 'empty carry-clearing position')
        reset = target_polynomial(layout, start-4, terms)
        need(reset.get(('x', 'x'), 0) >= 1 and all(v > 0 for v in reset.values()),
             'each reset is a positive polynomial containing x squared')
        extra_reset_terms += len(reset)-1
        need(target_polynomial(layout, start-1, terms) == expected_pads.get(start, {}),
             'only the final unit row has the exact twice-input-square padding')
    for position in layout['weights'].values():
        need(target_polynomial(layout, position, terms) == {}, 'true-coordinate coefficient is zero')
    return dict(true_coordinates=len(layout['weights']), rows=len(layout['rows']),
                tested_starts=len(starts), indicator_digits=len(layout['indicator']),
                D_terms=len(D), D1=sum(map(abs, D.values())),
                extra_positive_reset_terms=extra_reset_terms,
                canonical_e_digit_set=sorted(set(layout['e_coeff'].values())),
                exact_target_and_padding_checks=True, dummy_exclusion=True)


def raw_low(layout, values):
    result = defaultdict(int)
    Dsorted = sorted(layout['D'].items())
    for degree, (left, right), multiplicity in square_terms(layout['weights']):
        value = multiplicity*values[left]*values[right]
        if not value:
            continue
        for dexp, coef in Dsorted:
            exponent = degree+dexp
            if exponent >= layout['K']:
                break
            result[exponent] += coef*value
    return {key: val for key, val in result.items() if val}


def assignment(layout, logical, H0):
    result = {}
    for name, group in layout['groups'].items():
        parts = (logical.get(name, 0),) if len(group) == 1 else split_bit_clear(logical.get(name, 0), H0)
        result.update(zip(group, parts))
    return result


def finite_checks(layout):
    positions = set(layout['indicator']) | {start+offset for start in layout['starts'] for offset in range(-6, 3)}
    records = []
    for H0, x in ((64, 1), (64, 7), (64, 63), (64, 64), (64, 129), (256, 257)):
        logical = dict(x=x, delta=1, V0=x, V1=x, X=x, Y=x, Z=x, dc=1,
                       u=x*x-1, v=x*x, a=x+1, z=x*x+x+1, zero=0)
        values = assignment(layout, logical, H0)
        bound = sum(map(abs, layout['D'].values()))*sum(values.values())**2
        B = next_power_two(max(64*bound+1, H0+x+2))
        raw = raw_low(layout, values)
        need(max(map(abs, raw.values())) <= bound < B//64, 'necessary coefficients are tiny')
        digits, events, _ = sparse_digits(raw, positions, B)
        need(all(digits[p]['digit'] < 2 for p in layout['indicator']), 'all necessary binary mask digits pass')
        need(all(digits[p]['incoming'] == 0 for p in layout['starts']), 'necessary target carries are zero')
        records.append(dict(H0=H0, x=x, B=B, events=events))
    wide = []
    for seed in range(4):
        H0, B = 64, 1 << 34
        values = {name: ((B//3+(i+1)*(7919+seed*101)) % B) & ~H0
                  for i, name in enumerate(layout['weights'])}
        values['x'] = B-H0-2-seed
        bound = sum(map(abs, layout['D'].values()))*sum(values.values())**2
        need(bound < B**3//64, 'wide code has the required uniform cubic bound')
        raw = raw_low(layout, values)
        digits, events, _ = sparse_digits(raw, positions, B)
        for start in layout['starts']:
            if start != layout['targets'][-1]:
                need(digits[start]['incoming'] == 0, 'wide signed carries clear at every ordinary test')
                val = raw.get(start, 0)
                if val < 0:
                    need(any(digits[start+i]['digit'] >= 2 for i in range(3)),
                         'every negative raw target fails its binary three-digit test')
        wide.append(dict(seed=seed, B=B, largest_raw=max(map(abs, raw.values())), events=events))
    unit_pairs = 0
    for B in (64,128,256,512):
        for delta in range(1,B):
            square = delta*delta
            if square % B > 1 or square//B > 1:
                continue
            for x in range(delta,B):
                value = square+(2*x*x)//B
                accepted = value % B <= 1 and (value//B) % B <= 1 and value//(B*B) <= 1
                need(not accepted or delta == 1, 'binary plain/double-pad tests admit only the unit')
                unit_pairs += 1
    return dict(necessary_cases=records, arbitrary_wide_cases=wide,
                exhaustive_local_unit_pairs=unit_pairs)


def verify():
    layout = make_layout()
    return dict(status='PASS', scope='finite compiler and full sparse low-carry regression only; the general universality proof is separate and this is not exhaustive',
                symbolic=symbolic_checks(layout), finite=finite_checks(layout))


if __name__ == '__main__':
    result = verify()
    OUT.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(result['status'], result['symbolic'])
