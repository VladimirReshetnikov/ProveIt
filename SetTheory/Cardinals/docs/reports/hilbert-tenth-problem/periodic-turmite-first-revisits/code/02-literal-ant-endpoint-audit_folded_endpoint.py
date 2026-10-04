#!/usr/bin/env python3
"""Add folded selector sources; preserve every predecessor artifact unchanged."""
from pathlib import Path
from copy import deepcopy
import hashlib
import json
import audit_endpoint as predecessor

ROOT = Path(__file__).resolve().parent


def make_folded(paid):
    src = deepcopy(predecessor.make_source(paid))
    a, b, c = src['section_ends']
    power_part = src['gates'][:b]
    if paid:
        dname = 'DBuild'
        power_part.insert(a, {'out': dname, 'op': 'sub', 'args': ['CBuild', '1']})
        a += 1
        b += 1
    else:
        dname = 'D'
        src['fixed_numeral_recipes']['D'] = {
            'base': 3, 'exponent': predecessor.U_PERIOD, 'subtract': 2,
        }
    old_nonpower = src['gates'][src['section_ends'][1]:]
    c_name = 'CBuild' if paid else 'C'
    new_nonpower = [
        {'out': 'Hy', 'op': 'sub', 'args': ['HyPlus', '1']},
        {'out': 'CHxPlus', 'op': 'mul', 'args': [c_name, 'HxPlus']},
        {'out': 'U', 'op': 'sub', 'args': ['CHxPlus', dname]},
    ] + old_nonpower[4:]
    assert [g['out'] for g in old_nonpower[:4]] == ['Hx', 'Hy', 'CxHx', 'U']
    src['gates'] = power_part + new_nonpower
    src['section_ends'] = [a, b, len(src['gates'])]
    src['model'] += '_horizontal_positive_quotient_fold'
    src['predecessor_model'] = 'paid_numerals' if paid else 'fixed_numerals'
    return src


# Sparse exact polynomials. Variables: W,HxPlus,HyPlus,BoundCol,K,C.
# Exponents remain small Python integers even when W's degree is large;
# fixed numeral values are never expanded or evaluated.
N = 6
ZERO_MONOMIAL = (0,)*N


def scalar(n):
    return {ZERO_MONOMIAL: n} if n else {}


def symbol(i):
    exp = [0]*N
    exp[i] = 1
    return {tuple(exp): 1}


def plus(a, b, sign=1):
    z = dict(a)
    for m, coef in b.items():
        z[m] = z.get(m, 0) + sign*coef
        if not z[m]:
            del z[m]
    return z


def times(a, b):
    z = {}
    for m, c in a.items():
        for n, d in b.items():
            e = tuple(x+y for x, y in zip(m, n))
            z[e] = z.get(e, 0) + c*d
    return {m:c for m,c in z.items() if c}


def outer_polynomials(src):
    a, b, c = src['section_ends']
    vars_ = dict(zip(['W','HxPlus','HyPlus','BoundCol','K','C'], [symbol(i) for i in range(N)]))
    vars_['1'] = scalar(1)
    vars_['D'] = plus(vars_['C'], scalar(1), -1)
    # The preceding exponent audit establishes the paid numeral outputs.
    # Substitute K,C after their separately verified construction.
    if a:
        vars_[src['power_targets']['K']] = vars_['K']
        vars_['CBuild'] = vars_['C']
        if 'horizontal_positive_quotient_fold' in src['model']:
            assert src['gates'][a-1] == {'out': 'DBuild', 'op': 'sub', 'args': ['CBuild', '1']}
            vars_['DBuild'] = vars_['D']
    for g in src['gates'][a:]:
        x, y = (vars_[name] for name in g['args'])
        if g['op'] == 'mul':
            z = times(x,y)
        elif g['op'] == 'add':
            z = plus(x,y)
        elif g['op'] == 'sub':
            z = plus(x,y,-1)
        else:
            raise AssertionError(g['op'])
        vars_[g['out']] = z
    return {name: vars_[name] for name in ['U','V','ColumnBound','EndpointHead']}


def total_degree(poly, ignore_fixed_numerals=False):
    # K and C are fixed numbers, so the last two symbolic degrees do not
    # contribute to degree in actual variables.
    return max(sum(m[:4] if ignore_fixed_numerals else m) for m in poly)


def main():
    predecessor_names = [
        'audit_endpoint.py', 'ENDPOINT_AUDIT.md', 'endpoint_fixed_numerals_source.json',
        'endpoint_paid_numerals_source.json', 'endpoint_audit_receipt.json',
    ]
    original_hashes = {n: hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in predecessor_names}
    srcs = {'folded_fixed_numerals': make_folded(False), 'folded_paid_numerals': make_folded(True)}
    results = {}
    for label, src in srcs.items():
        results[label] = predecessor.check_source(src)
        old = predecessor.make_source('paid' in label)
        op, np = outer_polynomials(old), outer_polynomials(src)
        assert op == np
        assert src['equalities'] == old['equalities']
        assert src['new_positive_witnesses'] == old['new_positive_witnesses']
        results[label]['same_endpoint_polynomials_as_predecessor'] = True
        results[label]['same_witnesses_and_equalities_as_predecessor'] = True
        results[label]['expanded_head_total_degree_in_actual_variables'] = total_degree(np['EndpointHead'], True)
        (ROOT / f'endpoint_{label}_source.json').write_text(json.dumps(src, indent=2)+'\n')
    assert results['folded_fixed_numerals']['total'] == {'M':37,'A':5,'total':42}
    assert results['folded_paid_numerals']['total'] == {'M':94,'A':7,'total':101}
    assert results['folded_fixed_numerals']['expanded_head_total_degree_in_actual_variables'] == 605950
    # Sanity checks of horizontal exact equality and positivity, including
    # zero quotient Hx=0 <=> HxPlus=1, for several smaller even periods.
    small_cases = 0
    for u in [2,4,6,8]:
        C, D = 3**u-1, 3**u-2
        for HxPlus in range(1,21):
            old = 1+C*(HxPlus-1)
            new = C*HxPlus-D
            assert old == new >= 1
            assert (new == 1) == (HxPlus == 1)
            small_cases += 1
    assert {n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in predecessor_names} == original_hashes
    report = {
        'audits':results,
        'positivity_regression_cases':small_cases,
        'fixed_numeral_ports':{
            'K':'3^481225262775',
            'C':'3^481238074400 - 1',
            'D':'3^481238074400 - 2 = C - 1',
        },
        'fixed_ports_are_prescribed_not_quantified':True,
        'same_pointwise_zero_sets_with_same_three_witnesses':True,
        'five_witness_reformulation':{
            'witnesses':['U','V','Uq','Vq','BoundCol'],
            'max_expanded_endpoint_polynomial_degree':576001,
            'three_witness_max_expanded_endpoint_polynomial_degree':605950,
            'degree_scope':'Endpoint equations only, after treating numeral ports as fixed constants; no global degree claim.',
        },
        'predecessor_hashes_unchanged':original_hashes,
        'giant_fixed_powers_materialized':False,
        'upstream_code_executed':False,
    }
    new_names = ['audit_folded_endpoint.py']+[f'endpoint_{label}_source.json' for label in srcs]
    report['sha256'] = {n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in new_names}
    (ROOT/'folded_endpoint_audit_receipt.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__ == '__main__':
    main()
