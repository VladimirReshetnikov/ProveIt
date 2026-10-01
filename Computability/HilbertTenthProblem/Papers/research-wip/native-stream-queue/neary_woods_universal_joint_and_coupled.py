"""Coupled auxiliary linear units in the complete two-core U9 source."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_joint_and_arithmetic as parent

compiler = parent.compiler
PREFIXES = parent.PREFIXES
polynomial_source = parent.polynomial_source
degree_bound = parent.degree_bound


def rewrite(old, prefixes=PREFIXES):
    prefixes = tuple(prefixes)
    assert prefixes and len(set(prefixes)) == len(prefixes)
    assert all(p in old['merged_native_indices'] for p in prefixes)
    assert all(p in PREFIXES for p in prefixes) and old['joint_native_and']
    assert not old.get('coupled_native_linear')
    rows = {n: (op, a, b) for n, op, a, b in old['source']}
    assert old['comparisons'][-1] == (old['unit_register'], 1)
    assert old['unit_factors'].count('and__bs_q') == 1
    # The only conditional coordinate restoration changes F0 and its X slack.
    consumers = lambda name: {n for n, _, a, b in old['source'] if name in (a, b)}
    assert consumers('and__F0') == {'and__shared_sum02', 'and__bs_packed'}
    assert consumers('and__bound_beta') == {'and__bs_X_bound'}
    assert all(not {'and__F0','and__bound_beta'} & {a,b} for a,b in old['comparisons'])
    assert rows['and__bs_X_bound'] == ('+', 'and__bs_packed', 'and__bound_beta')
    removed = set()
    omitted = []
    audit = {}
    for p in prefixes:
        r = old['index_r_registers'][p]
        critical = {
            p+'r1': ('+', r, 1),
            p+'tr1': ('+', p+'r1', r),
            p+'H17': ('-', p+'jc', p+'tr1'),
            p+'H2': ('*', p+'H17', p+'H17'),
            p+'R11': ('-', p+'R10b', p+'hpm1'),
            p+'index_unit': ('-', p+'R11', r),
            p+'aux_u_rhs': ('-', p+'of', p+'R10a'),
            p+'of': ('*', p+'o', p+'f'),
            p+'jc': ('*', p+'j', p+'R10a'),
        }
        assert all(rows[n] == row for n, row in critical.items())
        expected = {p+'r1': {p+'tr1'}, p+'tr1': {p+'H17'}, p+'H17': {p+'H2'}}
        assert {n: consumers(n) for n in expected} == expected
        pair = (p+'H17', p+'aux_u_rhs')
        assert pair in old['comparisons']
        assert [v for v in old['comparisons'] if any(n in v for n in expected)] == [pair]
        assert not set(expected) & set(old.get('public_registers', {}).values())
        removed.update(expected)
        omitted.append(pair)
        audit.update({n: sorted(v) for n, v in expected.items()})
    changed_squares = {p+'H2': p for p in prefixes}
    source = [(n, '*', changed_squares[n]+'aux_u_rhs', changed_squares[n]+'aux_u_rhs')
              if n in changed_squares else row
              for row in old['source'] for n in [row[0]] if n not in removed]
    factors = list(old['unit_factors'])
    unit = old['unit_register']
    for p in prefixes:
        assert all(p+n not in rows for n in ('coupled_twice_K','coupled_difference','linear_unit','coupled_all_units'))
        source += [(p+'coupled_twice_K', '+', p+'R11', p+'R11'),
                   (p+'coupled_difference', '-', p+'aux_u_rhs', p+'jc'),
                   (p+'linear_unit', '+', p+'coupled_difference', p+'coupled_twice_K'),
                   (p+'coupled_all_units', '*', unit, p+'linear_unit')]
        factors.append(p+'linear_unit')
        unit = p+'coupled_all_units'
    pairs = [p for p in old['comparisons'][:-1] if p not in omitted]+[(unit, 1)]
    source = parent.parent.units.sort_source(source, old['parameters']+old['auxiliaries'])
    cc = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    packet = dict(old, source=source, comparisons=pairs, operations=len(source), equations=len(pairs),
                  multiplications=cc['M'], additions_subtractions=cc['A'], unit_register=unit,
                  unit_factors=factors, coupled_native_linear=prefixes, coupled_parent=old,
                  coupled_removed_comparisons=omitted, coupled_deleted_registers=sorted(removed),
                  coupled_deleted_consumers=audit)
    n = len(prefixes)
    assert cc['M'] == old['multiplications']+n and cc['A'] == old['additions_subtractions']
    assert len(source) == old['operations']+n and len(pairs) == old['equations']-n
    assert packet['auxiliaries'] == old['auxiliaries']
    compiler.check_source(packet)
    return packet


def build(form='normalized', *, merge_bound=True, prefixes=PREFIXES):
    return rewrite(parent.build(form, merge_bound=merge_bound), prefixes)


def ledger(packet):
    source, out = polynomial_source(packet)
    old = packet['coupled_parent']
    before, _ = polynomial_source(old)
    cc = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    bc = Counter('M' if op == '*' else 'A' for _, op, _, _ in before)
    n = len(packet['coupled_native_linear'])
    assert len(source) == len(before)-2*n
    assert cc['M'] == bc['M'] and cc['A'] == bc['A']-2*n
    d = degree_bound(packet)
    delta = sum(3 if p == 'geo__' else -167 for p in packet['coupled_native_linear'])
    assert d['degree_upper_bound'] == degree_bound(old)['degree_upper_bound']+delta
    return dict(form=packet['form'], prefixes=list(packet['coupled_native_linear']),
                bound_is_program_E=packet['bound_is_program_E'],
                certificate={k: packet[k] for k in ('operations','multiplications',
                    'additions_subtractions','equations','witnesses')},
                polynomial=dict(operations=len(source),multiplications=cc['M'],
                    additions_subtractions=cc['A'],output=out),
                parameters=packet['parameters'], **d)


def audit_identity(packet, values):
    old = packet['coupled_parent']
    execute, scalar = compiler.parent.execute, compiler.parent.scalar
    source, out = polynomial_source(packet)
    env = execute(source, values)
    before = execute(old['source'], values)
    changed = set(packet['coupled_deleted_registers']) | {p+'H2' for p in packet['coupled_native_linear']}
    for n, _, a, b in old['source']:
        if a in changed or b in changed:
            changed.add(n)
        if n not in changed:
            assert env[n] == before[n]
    factors = {n: before[n] for n in old['unit_factors']}
    for p in packet['coupled_native_linear']:
        U, V = before[p+'H17'], before[p+'aux_u_rhs']
        factors[p+'P17'] += before[p+'R16']*(V*V-U*U)
        factors[p+'linear_unit'] = 2*before[p+'index_unit']-1-(U-V)
    product = 1
    for n in packet['unit_factors']:
        assert env[n] == factors[n]
        product *= factors[n]
    assert env[packet['unit_register']] == product
    rr = [scalar(a,before)-scalar(b,before) for a,b in old['comparisons'][:-1]
          if (a,b) not in packet['coupled_removed_comparisons']]
    assert rr == [scalar(a,env)-scalar(b,env) for a,b in packet['comparisons'][:-1]]
    assert env[out] == product*(1+sum(r*r for r in rr))-1
    return True


def normalize_to_parent(packet, values, epsilon_joint):
    assert epsilon_joint in (-1,1)
    if 'and__' not in packet['coupled_native_linear']:
        assert epsilon_joint == 1
    result = dict(values)
    delta = 1-epsilon_joint
    result['and__F0'] -= delta
    result['and__bound_beta'] += delta
    return result


def restoration_checks():
    rng = random.Random(297153)
    cases = positive = signed = negative = 0
    for form in ('units','normalized'):
      for prefixes in (('geo__',), ('and__',), PREFIXES):
        packet = build(form,prefixes=prefixes)
        C = {n: 4 for n in compiler.NUMERALS}
        C.update(recoder_radix=4,repunit_divisor=7)
        p = parent.parent.constants_parent.materialize_packet(packet,C)
        old = p['coupled_parent']
        source,out = polynomial_source(p);old_source,old_out = polynomial_source(old)
        for eps in ((-1,1) if 'and__' in prefixes else (1,)):
          for case in range(24):
            v = {n:rng.randrange(1,4) for n in p['parameters']+p['auxiliaries']}
            v.update({f'hist__Shat{i}':2 for i in range(4)})
            e = compiler.parent.execute(p['source'],v)
            v['and__F1'] = e['and__padded_A']-e['and__F3']
            v['and__F2'] = e['and__padded_B']-e['and__F3']
            v['and__F0'] = e['and__q']-eps-v['and__F1']-v['and__F2']-e['and__F3']
            assert min(v['and__F0'],v['and__F1'],v['and__F2'])>0
            for prefix in PREFIXES:
                e = compiler.parent.execute(p['source'],v)
                r = e[p['index_r_registers'][prefix]]
                sign = eps if prefix == 'and__' else 1
                v[prefix+'zeta'] = r+e[prefix+'hpm1']+sign-v[prefix+'eta']
                e = compiler.parent.execute(p['source'],v)
                v[prefix+'f'] = 1
                v[prefix+'o'] = (v[prefix+'j']+1)*e[prefix+'R10a']-2*e[prefix+'R11']+1
                assert v[prefix+'o']>0 and v[prefix+'zeta']>0
            if case >= 18:
                for prefix in PREFIXES:
                    v[prefix+'i'] *= -1
                    v[prefix+'y_aux'] *= -1
            e = compiler.parent.execute(source,v)
            assert e['geo__index_unit']==1 and e['and__index_unit']==e['and__bs_q']==eps
            assert all(e[prefix+'linear_unit']==1 for prefix in prefixes)
            restored = normalize_to_parent(p,v,eps)
            before = compiler.parent.execute(old_source,restored)
            assert before['and__index_unit']==before['and__bs_q']==1
            assert all(before[a]==before[b] for a,b in p['coupled_removed_comparisons'])
            assert [e[a]-e[b] for a,b in p['comparisons'][:-1]] == [
                before[a]-before[b] for a,b in old['comparisons'][:-1]
                if (a,b) not in p['coupled_removed_comparisons']]
            assert e[out]==before[old_out]
            assert all(e[n]==before[n] for n,_,_,_ in old['source'] if not n.startswith(('geo__','and__','recoder_unit_')))
            if case<18:
                assert min(v.values())>0 and min(restored.values())>0
                positive+=1
            else:signed+=1
            cases+=1;negative+=eps==-1
    return dict(conditional_complete_output_restorations=cases,positive_cases=positive,
                signed_cases=signed,negative_joint_cases=negative,
                scope='Structured off-zero norm assignments, imposing the index/checksum/linear signs and both ports; no complete positive Pell zero is numerically claimed.')


def sign_checks():
    carry = checksum = bounds = 0
    for r in range(17,20000,16):
        v2 = ((r-1)&-(r-1)).bit_length()-1
        assert (r-2).bit_count() == r.bit_count()+v2-2
        assert (r-2).bit_count() >= r.bit_count()+2
        carry+=1
    rng = random.Random(29697)
    for t in range(4,14):
        q = 1<<t
        # C=-1: each field has its forced low nibble.
        high_total = (q>>4)-1
        for _ in range(32):
            rest=high_total;aa=[]
            for _ in range(3):
                k=rng.randrange(rest+1);aa.append(k);rest-=k
            aa.append(rest)
            F=[16*a+b for a,b in zip(aa,(3,4,2,8))]
            r=sum(f*q**i for i,f in enumerate(F))
            assert sum(F)==q+1 and all(0<f<q for f in F)
            assert r.bit_count()==sum(f.bit_count() for f in F)>=t+1
            checksum+=1
        for r in (q**3+q*q+q+1,q**4-1):
            assert r-2>q and 16*(r-1)>2*(2*r+3)
            bounds+=1
    for Q in range(4,40):
        B=4*Q;r=7*B
        assert r-2>B and r-2>Q and 12*(r-1)>2*(2*r+3)
        bounds+=1
    return dict(exact_low_nibble_carry_cases=carry,negative_checksum_population_cases=checksum,
                strengthened_target_bound_cases=bounds)


def verify():
    rng = random.Random(297144153)
    records=[];cases=signed=0
    for interface in (False,True):
      for form in ('units','normalized'):
       for prefixes in (('geo__',),('and__',),PREFIXES):
        packet=build(form,merge_bound=interface,prefixes=prefixes)
        records.append(ledger(packet))
        for case in range(64):
            positive=case<32
            C={n:rng.randrange(1,8) if positive else rng.randrange(-5,6) for n in compiler.NUMERALS}
            if positive:C.update(recoder_radix=4,repunit_divisor=7)
            literal=parent.parent.constants_parent.materialize_packet(packet,C)
            values={n:rng.randrange(1,5) if positive else rng.randrange(-3,4)
                    for n in packet['parameters']+packet['auxiliaries']}
            audit_identity(literal,values);cases+=1;signed+=not positive
    p=build();source,out=polynomial_source(p);encoded=compiler.encode_source(source)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_JOINT_AND_COUPLED',ledgers=records,
                complete_factor_and_output_corrections=cases,signed_cases=signed,
                conditional_restoration=restoration_checks(),sign_checks=sign_checks(),
                source_sha256=hashlib.sha256(json.dumps(encoded,sort_keys=True).encode()).hexdigest(),
                example=dict(source=encoded,output=out,comparisons=p['comparisons'],
                    parameters=p['parameters'],auxiliaries=p['auxiliaries'],
                    fixed_numeral_definitions=compiler.NUMERALS),
                scope='Same accepted ordinary-input relation as301. Geometry index sign is forced positive by joint population/low-nibble contradictions. A negative joint index/checksum branch restores F0-2 and bound_beta+2. No positive-tuple bijection or off-zero equality with301 is claimed. Default297=144M153A,51w12eq,degree at most2311.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['ledgers'][-1])
