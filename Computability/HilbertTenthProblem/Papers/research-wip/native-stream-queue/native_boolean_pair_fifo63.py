"""Exact split-input paired Boolean ternary FIFO63; general carry72.

These are complete projections of component sources, not universal bounds.
"""
import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path

import sympy as sp
import input_bridge_boolean_ternary60 as prior

PAIR = [('pb_initial_sum', '+', 'init0', 'init1'),
        ('pb_lane_tail', '*', 'W', 'F0'),
        ('pb_lane_transport', '+', 'init0', 'pb_lane_tail')]
CONTROL = [(f'pb_term{i}', '*', f'weight{i}', f'F{i}') for i in range(4)] + [
    ('pb_sum1', '+', 'pb_term0', 'pb_term1'),
    ('pb_sum2', '+', 'pb_sum1', 'pb_term2'),
    ('pb_sum3', '+', 'pb_sum2', 'pb_term3'),
    ('pb_time_term', '*', 'time_weight', 'q'),
    ('pb_carry_lhs', '+', 'pb_sum3', 'pb_time_term')]
FIXED = [f'weight{i}' for i in range(4)] + ['time_weight', 'endpoint']


def independent_sources(z, controller=False):
    result = prior.independent_sources(z, True) + [
        z['init0']+z['init1']-2*z['x'],
        z['F2']-z['init0']-z['W']*z['F0']]
    if controller:
        result += [sum(z[f'weight{i}']*z[f'F{i}'] for i in range(4))
                   +z['time_weight']*z['q']-z['endpoint']]
    return result


def source_check(controller=False):
    base = prior.source_check(True)
    parameters = base['positive_parameters']
    auxiliaries = base['positive_auxiliaries']+['init0', 'init1']
    z = {name: sp.Symbol(name) for name in parameters+auxiliaries+(FIXED if controller else [])}
    schedule = base['instructions']+PAIR+(CONTROL if controller else [])
    env = prior.prior.execute(schedule, dict(z, n2=z['q']))
    equations = [entry['equality'] for entry in base['sources']] + [
        ['pb_initial_sum', 'bt_initial'], ['F2', 'pb_lane_transport']]
    if controller:
        equations += [['pb_carry_lhs', 'endpoint']]
    polynomials = independent_sources(z, controller)
    u = 2*z['r']+1+z['j']*z['c']
    correction = polynomials[8]*(u*u-z['y_aux']**2)
    records = []
    for ix, ((left, right), polynomial) in enumerate(zip(equations, polynomials)):
        adjust = correction if ix == 9 else 0
        assert sp.expand(env[left]-env[right]-polynomial-adjust) == 0, ix
        records.append(dict(equality=[left, right], source=str(sp.expand(polynomial)),
                            correction=str(sp.expand(adjust))))
    second_lane = z['F3']-z['init1']-z['W']*z['F1']
    assert sp.expand(polynomials[13]-polynomials[17]-polynomials[16]-second_lane) == 0
    counts = Counter(row[1] for row in schedule)
    assert len(schedule) == 63+9*controller
    assert counts['*'] == 32+5*controller
    assert counts['+']+counts['-'] == 31+4*controller
    assert len(equations) == len(polynomials) == 18+controller
    assert len(parameters)+len(auxiliaries)-1 == 29
    assert set().union(*(p.free_symbols for p in polynomials)) == set(z.values())
    if controller:
        c = sp.symbols('c0:4'); h, cs, cf = sp.symbols('offset cs cf')
        replace = {z[f'weight{i}']: 2*c[i] for i in range(4)}
        replace.update({z['time_weight']: h-2*cf, z['endpoint']: h-2*cs})
        global_carry = 2*sum(c[i]*z[f'F{i}'] for i in range(4))+h*(z['q']-1)+2*cs-2*z['q']*cf
        assert sp.expand(polynomials[-1].subs(replace)-global_carry) == 0
    return dict(operations=len(schedule), multiplications=counts['*'],
                additions_subtractions=counts['+']+counts['-'], equations=len(equations),
                positive_parameters=parameters, positive_auxiliaries=auxiliaries,
                positive_existentials_excluding_x=29, aliases={'n2': 'q'},
                instructions=[list(row) for row in schedule], sources=records,
                fixed_constants=('weight_i=2*c_i; time_weight=h-2*cf; endpoint=h-2*cs'
                                 if controller else None),
                scope='Exact paired Boolean ternary FIFO with positive split init0+init1=2x'
                      +(' and the entire fixed affine carry graph' if controller else ''))


def digits(value, t):
    return [value//3**j % 3 for j in range(t)]


def direct_pair(initials, fields, m, t):
    W = 3**m
    contents = list(initials)
    for j in range(t):
        reads = [fields[2+i]//3**j % 3 for i in (0, 1)]
        appends = [fields[i]//3**j % 3 for i in (0, 1)]
        if any(contents[i] % 3 != reads[i] for i in (0, 1)):
            return False
        contents = [contents[i]//3+(W//3)*appends[i] for i in (0, 1)]
        assert all(0 <= N < W for N in contents)
    return contents == [0, 0]


def semantic_checks():
    rows = []
    for t in range(2, 5):
        q = 3**t
        boolean = [sum(bit*3**j for j, bit in enumerate(bits))
                   for bits in product((0, 1), repeat=t) if any(bits)]
        candidates = admitted = 0
        for fields in product(boolean, repeat=4):
            if sum(fields) >= q:
                continue
            for m in range(1, t+1):
                W = 3**m
                initials = [fields[2+i]-W*fields[i] for i in (0, 1)]
                arithmetic = min(initials) > 0 and sum(initials) < W and sum(initials) % 2 == 0
                if min(initials) > 0 and sum(initials) < W:
                    semantic = direct_pair(initials, fields, m, t) and sum(initials) % 2 == 0
                else:
                    semantic = False
                assert arithmetic == semantic
                if arithmetic:
                    assert all(prior.native_boolean(I, m) for I in initials)
                    assert t >= m+1 and sum(fields) % 2 == 0
                    assert prior.prior.valuation(prior.pack(fields, q)) == 0
                    admitted += 1
                candidates += 1
        rows.append(dict(t=t, q=q, positive_boolean_stream_and_width_tuples=candidates,
                         admitted=admitted))
    return dict(domains=rows, total_candidates=sum(row['positive_boolean_stream_and_width_tuples'] for row in rows),
                total_admitted=sum(row['admitted'] for row in rows),
                scope='All positive native Boolean fields through t=4; initial values are the unique transport residuals')


def positive_split(value):
    assert value > 0 and value % 2 == 0
    first, second = prior.split(value)
    if second == 0:
        place = 1
        while first//place % 3 == 0:
            place *= 3
        first -= place
        second = place
    assert first > 0 and second > 0 and first+second == value
    return first, second


def positive_maps():
    examples = []
    for x in range(1, 201):
        initials = positive_split(2*x)
        W = 3; m = 1
        while W <= 2*x+2:
            W *= 3; m += 1
        q = 3*W; t = m+1
        fields = [1, 1, initials[0]+W, initials[1]+W]
        slacks = dict(alpha=q-sum(fields), width_beta=W-2*x, L=3)
        assert all(prior.native_boolean(I, m) for I in initials)
        assert all(prior.native_boolean(F, t) for F in fields)
        assert sum(fields) % 2 == 0 and min(slacks.values()) > 0
        assert direct_pair(initials, fields, m, t)
        assert prior.prior.valuation(prior.pack(fields, q)) == 0
        if x in (1, 2, 10, 200):
            examples.append(dict(x=x, W=W, q=q, initials=list(initials), fields=fields,
                                 r=str(prior.pack(fields, q)), **slacks))
    return dict(ordinary_positive_inputs=200, examples=examples,
                complete_kernel_extension='Inherited positive Boolean55 converse, proved parametrically; auxiliary Pell coordinates not materialized')


def local_global_carry():
    checked = integral = 0
    q = 9
    words = [0, 1, 3, 4]
    for coefficients in product((-1, 0, 1), repeat=4):
        for h, cs in product((-1, 0, 1), repeat=2):
            for fields in product(words, repeat=4):
                numerator = cs; denominator = 1
                for j in range(2):
                    increment = h+sum(coefficients[i]*(fields[i]//3**j % 3) for i in range(4))
                    numerator += denominator*increment
                    denominator *= 3
                if numerator % q == 0:
                    cf = numerator//q
                    carry = cs
                    for j in range(2):
                        step = carry+h+sum(coefficients[i]*(fields[i]//3**j % 3) for i in range(4))
                        assert step % 3 == 0
                        carry = step//3
                    assert carry == cf
                    assert 2*sum(coefficients[i]*fields[i] for i in range(4))+(h-2*cf)*q == h-2*cs
                    integral += 1
                checked += 1
    return dict(arbitrary_two_step_boolean_word_and_controller_tuples=checked,
                integral_endpoint_paths=integral,
                scope='Independent local/global identity and integrality check, not a controller universality test')


def boundaries():
    fields = [1, 3, 28, 10]; x = 1; W = 9; q = 81
    assert all(prior.native_boolean(F, 4) for F in fields)
    assert sum(fields) < q and sum(fields) % 2 == 0
    assert sum(fields[2:]) == 2*x+W*sum(fields[:2])
    assert prior.run(2*x, sum(fields[:2]), 2, 4) == (sum(fields[2:]), 0)
    initials = [fields[2+i]-W*fields[i] for i in (0, 1)]
    assert initials == [19, -17]
    phase_fields = [1, 1, 4, 4]
    assert sum(phase_fields) == (81-1)//8
    assert any(F//3 % 3 for F in phase_fields)
    short_width_fields = [1, 9, 4, 28]
    assert sum(short_width_fields[:2]) == (81-1)//8
    assert sum(short_width_fields) < 81 and sum(short_width_fields) % 2 == 0
    assert all(prior.native_boolean(F, 4) for F in short_width_fields)
    assert direct_pair((1, 1), short_width_fields, 1, 4)
    return dict(scalar_fifo_not_paired=dict(x=x, W=W, q=q, fields=fields,
                                          forced_initials=initials),
                aggregate_even_phase_sum_does_not_type_support=dict(q=81, fields=phase_fields,
                                                                   sum_fields=sum(phase_fields)),
                permanent_even_phase_append_width_one_exception=dict(x=1, W=3, q=81,
                                                                     initials=[1, 1], fields=short_width_fields))


def verify():
    return dict(status='PASS_EXACT_PAIRED_BOOLEAN_TERNARY_FIFO63',
                source63=source_check(False), source72=source_check(True),
                semantics=semantic_checks(), positive_maps=positive_maps(),
                carry=local_global_carry(), boundaries=boundaries(),
                scope='Exact component and full carry relation only; split normalization, universal compiler and acceptance remain unproved',
                established_complete_universal_bound=76)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--write', action='store_true'); args = parser.parse_args()
    result = verify(); path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(json.dumps({key: value for key, value in result.items() if key not in ('source63', 'source72')}, indent=2))
