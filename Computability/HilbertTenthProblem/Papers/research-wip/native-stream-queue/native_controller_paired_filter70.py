"""Bound sharing65/70/73 and direct paired transports64/69/72, exact components."""
import argparse
from collections import Counter
from itertools import product
import hashlib
import json
from pathlib import Path
import sympy as sp
import native_controller_paired_filter71 as prior

boolean = prior.boolean


def source_check(controller=True, aligned=False, direct_lanes=True):
    old = prior.source_check(controller, aligned)
    schedule = []
    for original in old['instructions']:
        row = tuple(original)
        name = row[0]
        if name == 'bt_joint':
            continue
        if name == 'bt_joint_bound':
            row = (name, '+', 'F3', 'alpha')
        if direct_lanes:
            if name in ('bt_read', 'bt_transport'):
                continue
            if name == 'bt_tail':
                schedule += [('pf70_lane1_tail', '*', 'W', 'F1'),
                             ('pf70_lane1_transport', '+', 'init1', 'pf70_lane1_tail')]
                continue
        schedule.append(row)
    names = old['positive_parameters'] + old['positive_auxiliaries']
    z = {name: sp.Symbol(name) for name in names}
    constants = {name: sp.Symbol(name) for name in ('g0', 'g1', 'g2', 'gap', 'block_modulus')}
    equalities = [tuple(record['equality']) for record in old['sources']]
    polynomials = prior.paired.independent_sources(z, False)
    polynomials[12] = z['F3']+z['alpha']-z['q']
    if direct_lanes:
        equalities[13] = ('F3', 'pf70_lane1_transport')
        polynomials[13] = z['F3']-z['init1']-z['W']*z['F1']
    polynomials += [2*(z['F0']+z['F1']+z['F2'])+1-z['q']]
    if controller:
        polynomials += [constants['g0']*z['F0']+constants['g1']*z['F1']+
                        constants['g2']*z['F3']-constants['gap']]
    if aligned:
        polynomials += [constants['block_modulus']*z['block_time']-
                        2*(z['F0']+z['F1']+z['F2']),
                        constants['block_modulus']*z['block_width']+1-z['W']]
    env = boolean.prior.execute(schedule, dict(z, **constants, n2=z['q']))
    u = 2*z['r']+1+z['j']*z['c']
    correction = polynomials[8]*(u*u-z['y_aux']**2)
    records = []
    for i, ((left, right), polynomial) in enumerate(zip(equalities, polynomials)):
        adjust = correction if i == 9 else 0
        assert sp.expand(env[left]-env[right]-polynomial-adjust) == 0, i
        records.append(dict(equality=[left, right], source=str(sp.expand(polynomial)),
                            correction=str(sp.expand(adjust))))
    counts = Counter(row[1] for row in schedule)
    total = 65-int(direct_lanes)+5*controller+3*aligned
    assert len(schedule) == total
    assert counts['*'] == 32+3*controller+2*aligned
    assert counts['+']+counts['-'] == 33-int(direct_lanes)+2*controller+aligned
    assert len(equalities) == len(polynomials) == 19+controller+2*aligned
    assert len(names)-1 == 29+2*aligned
    if direct_lanes:
        assert all(name not in env for name in ('bt_joint', 'bt_read', 'bt_tail', 'bt_transport'))
        scalar = z['F2']+z['F3']-2*z['x']-z['W']*(z['F0']+z['F1'])
        assert sp.expand(polynomials[13]+polynomials[16]+polynomials[17]-scalar) == 0
    used = set().union(*(p.free_symbols for p in polynomials))
    assert set(z.values()) <= used
    return dict(operations=total, multiplications=counts['*'],
                additions_subtractions=counts['+']+counts['-'], equations=len(equalities),
                positive_witnesses_excluding_x=len(names)-1,
                positive_parameters=old['positive_parameters'],
                positive_auxiliaries=old['positive_auxiliaries'],
                direct_lane_transports=direct_lanes,
                fixed_constants=old['fixed_constants'], block_alignment=old['block_alignment'],
                instructions=[list(row) for row in schedule], sources=records,
                changed_bound='F3+alpha=q; the paid one-hot filter bounds the other three fields',
                scope='Same exact finite-machine projection as frozen66/71/74, with changed slack and literal sharing savings')


def prepower_checks():
    cases = 0
    for q in range(7, 42, 2):
        H = (q-1)//2
        for f0 in range(1, H-1):
            for f1 in range(1, H-f0):
                f2 = H-f0-f1
                for f3 in range(1, q):
                    fields = [f0, f1, f2, f3]
                    assert 2*sum(fields[:3])+1 == q and all(0 < F < q for F in fields)
                    r = boolean.pack(fields, q)
                    assert q**3+q*q+q+1 <= r < q**4 and r >= 400
                    X = q*(r//q+1)
                    Y = 4
                    E = X*Y
                    a = Y*(X+1)
                    A = a+3
                    P = 2*X*Y*Y+1
                    assert X > r and E > r+1 and a > 2*r+1
                    assert P > A and r+2 >= 402 and 6*X*Y*Y > a
                    cases += 1
    return dict(arbitrary_positive_pre_power_tuples=cases, q_odd_range=[7,41],
                minimum_q=7, minimum_r=400, minimum_main_index=402,
                scope='No power assumption or Boolean field typing used in these preliminary bounds')


def typing_checks():
    rows = []
    for t in range(1, 5):
        q = 3**t
        H = (q-1)//2
        cases = admitted = 0
        for f0 in range(1, H-1):
            for f1 in range(1, H-f0):
                f2 = H-f0-f1
                for f3 in range(1, q):
                    fields = [f0, f1, f2, f3]
                    r = boolean.pack(fields, q)
                    arithmetic = r % 2 == 0 and boolean.prior.valuation(r) == 0
                    semantic = (all(boolean.native_boolean(F, t) for F in fields)
                                and sum(fields) % 2 == 0)
                    assert arithmetic == semantic
                    if arithmetic:
                        assert sum(fields) < q
                        old_alpha = q-sum(fields)
                        new_alpha = q-f3
                        assert 0 < old_alpha < new_alpha and new_alpha == old_alpha+H
                        assert all(sum(F//3**j % 3 for F in fields[:3]) == 1 for j in range(t))
                        admitted += 1
                    cases += 1
        rows.append(dict(t=t, q=q, arbitrary_positive_fields=cases, typed_even_fields=admitted))
    return dict(domains=rows, field_tuples=sum(row['arbitrary_positive_fields'] for row in rows),
                admitted=sum(row['typed_even_fields'] for row in rows),
                scope='Pre-typed bounded fields with the new bound and paid filter; tests recovery of the old joint bound after typing')


def positive_maps():
    examples = []
    aligned_examples = []
    for x in range(1, 201):
        I0, I1 = prior.paired.positive_split(2*x)
        for ell in (1, 2, 3, 5):
            m = ell
            while 3**m <= 6*x:
                m += ell
            W = 3**m
            Hm = (W-1)//2
            q = W**3
            t = 3*m
            fields = [W*Hm, Hm-I0, I0+W*W*Hm, I1+W*(Hm-I0)]
            assert prior.paired.direct_pair((I0,I1), fields, m, t)
            assert all(boolean.native_boolean(F,t) for F in fields)
            assert sum(fields[:3]) == (q-1)//2 and sum(fields) % 2 == 0
            alpha = q-fields[3]
            old_alpha = q-sum(fields)
            assert old_alpha > 0 and alpha == old_alpha+(q-1)//2
            assert fields[3]+alpha == q and W-2*x > 0
            if ell > 1:
                modulus = 3**ell-1
                assert (q-1) % modulus == 0 and (W-1) % modulus == 0
                assert (q-1)//modulus > 0 and (W-1)//modulus > 0
            if x in (1, 2, 10, 200):
                record = dict(x=x, ell=ell, m=m, t=t, W=W, q=q,
                              initial=[I0,I1], fields=fields, alpha=alpha,
                              width_beta=W-2*x, L=q//W, old_joint_alpha=old_alpha)
                (examples if ell == 1 else aligned_examples).append(record)
    fixture = prior.controlled_witness()
    fixture['old_joint_alpha'] = fixture['alpha']
    fixture['alpha'] = fixture['q']-fixture['fields'][3]
    assert fixture['alpha'] == 71 and fixture['fields'][3]+fixture['alpha'] == fixture['q']
    return dict(ordinary_inputs=200, maps_per_input=4,
                bare64_examples=examples, aligned_zero_controller_examples=aligned_examples,
                positive_controlled69_fixture=fixture,
                scope='Three-sweep map gives64 for all inputs; zero fixed carry data give aligned72 examples. Nonzero controller completeness remains its exact finite-run predicate.')


def verify():
    variants = {}
    for direct in (False, True):
        for controller, aligned in ((False, False), (True, False), (True, True)):
            result = source_check(controller, aligned, direct)
            variants[f'source{result["operations"]}'] = result
    assert sorted(int(key[6:]) for key in variants) == [64,65,69,70,72,73]
    return dict(status='PASS_FILTERED_PAIRED_BOUND_SHARING64_69_72',
                sources=variants, prepower=prepower_checks(), typing=typing_checks(),
                positive=positive_maps(),
                dependency_sha256=hashlib.sha256(Path(prior.__file__).read_bytes()).hexdigest(),
                scope='Exact optimized components; unchanged controller language, no universal ordinary-input simulation or acceptance theorem',
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
    print(json.dumps(dict(status=result['status'], source_operations=sorted(int(k[6:]) for k in result['sources']),
                         prepower=result['prepower'], typing=result['typing'],
                         ordinary_inputs=result['positive']['ordinary_inputs'],
                         maps_per_input=result['positive']['maps_per_input']), indent=2))
