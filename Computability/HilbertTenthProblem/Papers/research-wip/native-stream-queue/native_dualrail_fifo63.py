"""Exact joint-bounded native FIFO63; general carry72 is not universal."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

import sympy as sp
import native_dualrail_fifo67 as prior

selector = prior.selector


def source_check():
    parameters = ['x', 'W', 'q', 'F0', 'F1', 'F2', 'F3']
    auxiliaries = selector.CORE_NAMES + ['alpha', 'beta', 'L']
    z = {name: sp.Symbol(name) for name in parameters + auxiliaries}
    packing = [row for row in prior.base.prior.OUTER
               if not row[0].startswith('bound') and row[0] != 'even_r']
    fifo = [(name, op, 6 if name == 'initial' else left, right)
            for name, op, left, right in prior.EXTRA66]
    joint = [('joint_sum', '+', 'append_sum', 'read_sum'),
             ('joint_bound', '+', 'joint_sum', 'alpha')]
    schedule = packing + [('twice_H', '-', 'q', 1)] + selector.CORE + fifo + joint
    env = selector.execute(schedule, z)
    equalities = [('r', 'packed')] + selector.kernel.EQUALITIES[1:] + [
        ('read_sum', 'transport'), ('width_bound', 'W'),
        ('q', 'length_product'), ('joint_bound', 'q')]
    q = z['q']
    fields = [z[f'F{i}'] for i in range(4)]
    supplied = dict(z, nu=sp.Symbol('unused_nu'),
                    **{f'alpha{i}': sp.Symbol(f'unused_alpha{i}') for i in range(4)})
    old = prior.base.prior.independent_sources(supplied, False)
    sources = old[4:5] + old[6:]
    norm_index = len(sources) - 3
    append = fields[0] + fields[1] - q + 1
    read = fields[2] + fields[3] - q + 1
    sources += [read - 6*z['x'] - z['W']*append,
                6*z['x'] + z['beta'] - z['W'], q-z['W']*z['L'],
                append + read + z['alpha'] - q]
    u = 2*z['r'] + 1 + z['j']*z['c']
    correction = sources[norm_index] * (u*u-z['y_aux']**2)
    records = []
    for ix, ((left, right), source) in enumerate(zip(equalities, sources)):
        adjustment = correction if ix == norm_index+1 else 0
        assert sp.expand(env[left]-env[right]-source-adjustment) == 0, ix
        records.append(dict(equality=[left, right], source=str(sp.expand(source)),
                            correction=str(sp.expand(adjustment))))
    counts = Counter(row[1] for row in schedule)
    assert len(schedule) == 63 and counts['*'] == 33
    assert counts['+'] + counts['-'] == 30
    assert len(equalities) == len(sources) == 15 and len(auxiliaries) == 20
    assert set().union(*(p.free_symbols for p in sources)) == set(z.values())
    return dict(operations=63, multiplications=33, additions_subtractions=30,
                equations=15, positive_parameters=parameters, positive_auxiliaries=auxiliaries,
                instructions=[list(row) for row in schedule], sources=records)


def carry_count(r):
    carry = count = 0
    while r or carry:
        digit = r % 3
        r //= 3
        carry = (2*digit+carry)//3
        count += carry
    return count


def fields_with_joint_bound(q):
    # Joint bound is sum(Fi) <= 3q-3; every supplied field is positive.
    limit = 3*q-3
    for f0 in range(1, limit-2):
        for f1 in range(1, limit-f0-1):
            for f2 in range(1, limit-f0-f1):
                for f3 in range(1, limit-f0-f1-f2+1):
                    yield (f0, f1, f2, f3)


def prepower():
    cases = 0
    for q in range(3, 11):
        scale = q**4
        for fields in fields_with_joint_bound(q):
            r = prior.base.prior.packed(fields, q)
            assert q**3+q*q+q+1 <= r < 3*scale
            assert scale < r*r and scale*scale > r+1
            assert scale*(scale+1) > 12*r
            cases += 1
    return dict(positive_joint_bounded_field_tuples=cases, q_range=[3, 10],
                scope='No power, field, parity, or nonnegative decoded-stream assumption')


def exhaustive():
    rows = []
    for t in range(1, 4):
        q = 3**t
        H = (q-1)//2
        checked = valued = arithmetic_count = 0
        for fields in fields_with_joint_bound(q):
            r = prior.base.prior.packed(fields, q)
            valuation = carry_count(r)
            native = all(0 < f < q and prior.base.prior.native(f, t) for f in fields)
            native = native and fields[0] % 3 == 2
            append = fields[0]+fields[1]-q+1
            read = fields[2]+fields[3]-q+1
            checked += 1
            valued += valuation >= 4*t
            for m in range(1, t+1):
                W = 3**m
                initial = read-W*append
                if not 0 < initial < W or initial % 6:
                    continue
                arithmetic = valuation >= 4*t and r % 2 == 0
                semantic = native
                assert arithmetic == semantic, (t, fields, W, initial, valuation)
                if arithmetic:
                    assert t >= m >= 2 and 0 < append < q and 0 < read < q
                    assert append+read < q and valuation == 4*t
                    planes = [[(f-H)//3**j % 3 for j in range(t)] for f in fields]
                    reads = [planes[2][j]+planes[3][j] for j in range(t)]
                    appends = [planes[0][j]+planes[1][j] for j in range(t)]
                    assert prior.direct_fifo(initial, W, reads, appends)
                    arithmetic_count += 1
        rows.append(dict(t=t, positive_field_tuples=checked,
                         valuation_admitted=valued, accepted=arithmetic_count))
    return rows


def long_overflow_structure():
    # Independent carry-pattern enumeration at q=9,27,81. Minimum digit
    # vectors cover every carry pattern: increasing a digit increases S.
    cases = 0
    for t in range(1, 8):
        q = 3**t
        for missed in range(-1, 4*t+1):
            incoming = 0
            digits = []
            possible = True
            for j in range(4*t+1):
                outgoing = int(j != missed)
                available = [d for d in range(3) if (2*d+incoming)//3 == outgoing
                             and (j < 4*t or d > 0)]
                if not available:
                    possible = False
                    break
                digits.append(min(available))
                incoming = outgoing
            if not possible:
                continue
            r = sum(d*3**j for j, d in enumerate(digits))
            normalized = [r//q**i % q for i in range(3)] + [r//q**3]
            total = sum(normalized)
            if total <= 3*q-3:
                assert missed in (t-1, 2*t-1, 3*t-1)
                assert total >= 3*q-q//3
                assert total+q-1 > 3*q-3
                assert normalized[3] < 2*q
            cases += 1
    return dict(minimal_carry_patterns=cases, maximum_t=7,
                conclusion='Only the first three block boundaries can meet the joint sum')


def all_inputs():
    cases = 0
    for x in range(1, 201):
        initial = 6*x
        W, m = 9, 2
        while W <= initial:
            W *= 3
            m += 1
        t, q = m+1, 3*W
        H = (q-1)//2
        reads = [initial//3**j % 3 for j in range(m)] + [1]
        appends = [1] + [0]*(t-1)
        for rail in (0, 1):
            d0 = [int(d == 2 or (d == 1 and rail == 0)) for d in reads]
            d1 = [d-a for d, a in zip(reads, d0)]
            fields = [H+1, H, H+prior.word(d0), H+prior.word(d1)]
            r = prior.base.prior.packed(fields, q)
            alpha = q-(initial+W)-1
            assert min(fields+[r, alpha, W-initial, q//W]) > 0
            assert r % 2 == 0 and carry_count(r) == 4*t
            assert prior.direct_fifo(initial, W, reads, appends)
            assert fields[0]+fields[1]-q+1 == 1
            assert fields[2]+fields[3]-q+1 == initial+W
            cases += 1
    return dict(ordinary_positive_inputs=200, positive_outer_maps=cases,
                full_Pell_coordinates='Parametric positive extension, not materialized')


def controller_schedules(source):
    controller = prior.conditional_carry_schedule(True, False, True)['instructions']
    result = {}
    for equal_endpoints in (False, True):
        extra = (controller[:7] + [['carry_negative_offset', '*', 'negative_lambda', 'twice_H']]
                 if equal_endpoints else controller[:-1])
        inputs = {name: sp.Symbol(name) for name in
                  source['positive_parameters']+source['positive_auxiliaries']+
                  ['weight0', 'weight1', 'weight2', 'weight3', 'lambda', 'endpoint_difference']}
        inputs['negative_lambda'] = -inputs['lambda']
        env = selector.execute(source['instructions']+extra, inputs)
        expected = sum(inputs[f'weight{i}']*inputs[f'F{i}'] for i in range(4))
        expected += inputs['lambda']*(inputs['q']-1)
        if equal_endpoints:
            equality = ['carry_s0123', 'carry_negative_offset']
        else:
            equality = ['carry_with_offset', 'endpoint_difference']
            expected -= inputs['endpoint_difference']
        assert sp.expand(env[equality[0]]-env[equality[1]]-expected) == 0
        count = Counter(row[1] for row in source['instructions']+extra)
        total = 72-int(equal_endpoints)
        assert len(source['instructions']+extra) == total
        result[str(total)] = dict(operations=total, multiplications=count['*'],
                                 additions_subtractions=count['+']+count['-'], equations=16,
                                 condition='cs=cf' if equal_endpoints else 'arbitrary endpoints',
                                 equality=equality,
                                 fixed_comparison_numeral='endpoint_difference=cf-cs',
                                 extra_instructions=extra,
                                 scope='Joint-bounded entire affine carry/FIFO graph; universality open')
    return result


def removed_input_factor_counterexample():
    q, W, fields = 27, 9, (14, 14, 5, 41)
    r = prior.base.prior.packed(fields, q)
    append = fields[0]+fields[1]-q+1
    read = fields[2]+fields[3]-q+1
    assert r == 811040 and carry_count(r) == 12 and r % 2 == 0
    assert read == 2+W*append and append+read < q and 2 < W
    assert fields[3] >= q
    return dict(q=q, W=W, fields=list(fields), r=r, valuation=12, initial=2,
                scope='Full outer/kernel projection at I=2x; excludes a free return to that input factor')


def verify():
    source = source_check()
    return dict(status='PASS_EXACT_JOINT_BOUNDED_FIFO_63', source=source,
                prepower=prepower(), exhaustive=exhaustive(),
                overflow_patterns=long_overflow_structure(), all_inputs=all_inputs(),
                controllers=controller_schedules(source),
                input_factor_counterexample=removed_input_factor_counterexample(),
                dependency_sha256=hashlib.sha256(Path(prior.__file__).read_bytes().replace(b'\r\n', b'\n')).hexdigest(),
                scope='Exact FIFO component with A+D<q and input6x; no universal compiler',
                established_complete_universal_bound=76)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    else:
        assert json.loads(receipt.read_text()) == result, 'receipt mismatch'
    print(json.dumps({key: value for key, value in result.items() if key != 'source'}, indent=2))
