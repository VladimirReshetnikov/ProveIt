"""Complete AND64/65 and conditional eight-field selection118/120.

The retained selector56 theorem supplies the positive Pell converse.
Finite checks do not materialize its astronomical canonical Pell tuple.
"""
import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path
import random

import sympy as sp
import native_controller_binary_selector56 as native

AUX = ['F0', 'F1', 'F2']+native.CORE_NAMES+['odd_half', 'bound_beta']
AND_PARAMETERS = ['P', 'Hhat', 'Mhat', 'Zhat']


def kernel():
    core = [(name, op, 'q' if left == 'n2' else left,
             'q' if right == 'n2' else right) for name, op, left, right in native.CORE]
    return native.OUTER+core+native.BOUND


def comparisons():
    return [('r', 'bs_packed'), ('bs_q', 'q'), ('s', 'bs_odd'),
            ('bs_X_bound', 'wn2')]+native.CORE_EQUALITIES+[
                ('input_A', 'padded_A'), ('input_B', 'padded_B')]


def suffix(scale, left, right, output, hatted):
    return [('q', '*', 16, scale),
            ('scaled_A', '*', 16, left),
            ('padded_A', '-' if hatted else '+', 'scaled_A', 4 if hatted else 12),
            ('scaled_B', '*', 16, right),
            ('padded_B', '-' if hatted else '+', 'scaled_B', 6 if hatted else 10),
            ('scaled_Z', '*', 16, output),
            ('F3', '-' if hatted else '+', 'scaled_Z', 8)]+kernel()+[
                ('input_A', '+', 'F1', 'F3'), ('input_B', '+', 'F2', 'F3')]


def and_source(unbounded=False):
    source=suffix('P', 'Hhat', 'Mhat', 'Zhat', True)
    return source[1:] if unbounded else source, comparisons()


def batch_source(exclusive=False, unbounded=False):
    prefix = [('P2', '*', 'P', 'P'), ('P4', '*', 'P2', 'P2'),
              ('P8', '*', 'P4', 'P4'), ('J2', '+', 'P', 1),
              ('P2plus1', '+', 'P2', 1), ('J4', '*', 'J2', 'P2plus1'),
              ('P4plus1', '+', 'P4', 1), ('J8', '*', 'J4', 'P4plus1'),
              ('ht0', '*', 'P2', 'history2'), ('ht1', '+', 'history3', 'ht0'),
              ('ht2', '*', 'P2', 'ht1'), ('ht3', '+', 'history0', 'ht2'),
              ('ht4', '*', 'P2', 'ht3'), ('ht5', '+', 'history1', 'ht4'),
              ('Hbatch', '*', 'J2', 'ht5')]
    for tag in ('S', 'Z'):
        last = f'{tag}hat7'
        for index in range(6, -1, -1):
            mult, total = f'{tag}pack_mult{index}', f'{tag}pack_sum{index}'
            prefix += [(mult, '*', 'P', last), (total, '+', f'{tag}hat{index}', mult)]
            last = total
        prefix.append((f'{tag}batch', '-', last, 'J8'))
    prefix += [('Bm1', '-', 'B', 1), ('Mbatch', '*', 'Bm1', 'Sbatch')]
    if exclusive:
        bounds = [('Zsum1', '+', 'Zhat0', 'Zhat1')]
        bounds += [(f'Zsum{i}', '+', f'Zsum{i-1}', f'Zhat{i}') for i in range(2,8)]
        bounds += [('Zglobal', '+', 'Zsum7', 'bound_global')]
        extra_equalities = [('Zglobal', 'J2')]
    else:
        bounds = [(f'Zbound{i}', '+', f'Zhat{i}', f'bound{i}') for i in range(8)]
        extra_equalities = [(f'Zbound{i}', 'J2') for i in range(8)]
    source = prefix+bounds+suffix('P8', 'Hbatch', 'Mbatch', 'Zbatch', False)
    if unbounded:
        source=[row for row in source if row[0] not in ('P8','q')]
    equalities = comparisons()+extra_equalities
    return source, equalities


BATCH_PARAMETERS = ['P', 'B']+[f'history{i}' for i in range(4)]+[f'Shat{i}' for i in range(8)]+[f'Zhat{i}' for i in range(8)]


def execute(source, inputs):
    env = dict(inputs)
    for name, op, left, right in source:
        assert name not in env, name
        a = env[left] if isinstance(left, str) else left
        b = env[right] if isinstance(right, str) else right
        env[name] = a*b if op == '*' else a+b if op == '+' else a-b
    return env


def source_audit(batch=False, exclusive=False, unbounded=False):
    source, equalities = batch_source(exclusive,unbounded) if batch else and_source(unbounded)
    parameters = BATCH_PARAMETERS if batch else AND_PARAMETERS[1:] if unbounded else AND_PARAMETERS
    auxiliaries = AUX+(['bound_global'] if exclusive else [f'bound{i}' for i in range(8)] if batch else [])+(['q'] if unbounded else [])
    z = {name: sp.Symbol(name) for name in parameters+auxiliaries}
    env = execute(source, z)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    expected = (
        (120, {'M':57,'A':63},17,23) if exclusive else
        (120, {'M':57,'A':63},24,30) if batch else (65,{'M':33,'A':32},16,22))
    if unbounded:
        saving=2 if batch else 1
        expected=(expected[0]-saving,{'M':expected[1]['M']-saving,'A':expected[1]['A']},expected[2],expected[3]+1)
    assert (len(source), counts, len(equalities), len(auxiliaries)) == expected
    raw = dict(z, q=env['q'], F3=env['F3'])
    independent = native.independent_sources(raw)
    u = z['j']*z['c']-(2*z['r']+1)
    correction = independent[11]*(u*u-z['y_aux']**2)
    for index, ((left, right), expected) in enumerate(zip(equalities[:14], independent)):
        adjust = correction if index == 12 else 0
        assert sp.expand(env[left]-env[right]-expected-adjust) == 0
    if batch:
        P, B = z['P'], z['B']
        slots = (1,1,0,0,3,3,2,2)
        H = sum(z[f'history{i}']*P**j for j,i in enumerate(slots))
        S = sum((z[f'Shat{i}']-1)*P**i for i in range(8))
        Z = sum((z[f'Zhat{i}']-1)*P**i for i in range(8))
        assert sp.expand(env['Hbatch']-H) == 0
        assert sp.expand(env['Mbatch']-(B-1)*S) == 0
        assert sp.expand(env['Zbatch']-Z) == 0
        if not unbounded:
            assert sp.expand(env['q']-16*P**8) == 0
        expected = [z['F1']+16*Z+8-(16*H+12),
                    z['F2']+16*Z+8-(16*(B-1)*S+10)]
        expected += ([sum(z[f'Zhat{i}'] for i in range(8))+z['bound_global']-P-1]
                     if exclusive else [z[f'Zhat{i}']+z[f'bound{i}']-P-1 for i in range(8)])
    else:
        expected = [z['F1']+16*z['Zhat']-8-(16*z['Hhat']-4),
                    z['F2']+16*z['Zhat']-8-(16*z['Mhat']-6)]
    for (left,right), value in zip(equalities[14:], expected):
        assert sp.expand(env[left]-env[right]-value) == 0
    return dict(operations=len(source), multiplications=counts['M'], additions_subtractions=counts['A'],
                equations=len(equalities), positive_parameters=parameters,
                positive_auxiliaries=auxiliaries, auxiliary_count=len(auxiliaries),
                source=source, comparisons=equalities,
                original_selector_residuals_with_auxiliary_correction=True)


def truth_fields(P, H, M):
    assert 0 <= H < P and 0 <= M < P and P & (P-1) == 0
    Q, A, B = 16*P, 16*H+12, 16*M+10
    mask = Q-1
    return ((~A & ~B) & mask, A & ~B & mask, ~A & B & mask, A & B)


def primitive_checks():
    cases = 0
    for ell in range(8):
        P = 1 << ell
        for H, M in product(range(P), repeat=2):
            Z, fields = H & M, truth_fields(P,H,M)
            assert all(value > 0 for value in fields)
            assert sum(fields) == 16*P-1 and fields[0] & 1
            assert fields[3] == 16*(Z+1)-8
            assert fields[1]+fields[3] == 16*(H+1)-4
            assert fields[2]+fields[3] == 16*(M+1)-6
            packed = sum(value*(16*P)**i for i,value in enumerate(fields))
            assert packed.bit_count() == ell+4 and packed & 1
            assert tuple((next(i for i,f in enumerate(fields) if (f>>j)&1)) for j in range(4)) == (0,2,1,3)
            cases += 1
    # All partitions with the required first bit: any padded-port match
    # decodes exactly the prescribed nonnegative AND values.
    projections = 0
    for ell in range(5):
        for tail in product(range(4), repeat=ell):
            labels = (0,2,1,3)+tail
            fields = tuple(sum(1<<j for j,label in enumerate(labels) if label==i) for i in range(4))
            A,B,Z = fields[1]+fields[3],fields[2]+fields[3],fields[3]
            assert (A%16,B%16,Z%16)==(12,10,8)
            assert Z//16 == (A//16)&(B//16)
            projections += 1
    return dict(all_inputs_through_binary_length7=cases, empty_words_and_all_zero_fields_included=True,
                truth_prefix=[0,2,1,3], reverse_partition_projections=projections)


def packed(digits,B):
    return sum(digit*B**i for i,digit in enumerate(digits))


def batch_checks():
    rng=random.Random(65120)
    cases=mutations=0
    for bits in range(1,7):
        B=1<<bits
        for t in range(1,9):
            P=B**t
            for _ in range(24):
                histories=[[rng.randrange(1,B) for j in range(t)] for i in range(4)]
                selectors=[[rng.randrange(2) for j in range(t)] for i in range(8)]
                slot=(1,1,0,0,3,3,2,2)
                H=[packed(row,B) for row in histories]
                S=[packed(row,B) for row in selectors]
                Z=[packed([selectors[i][j]*histories[slot[i]][j] for j in range(t)],B) for i in range(8)]
                Hb=sum(H[slot[i]]*P**i for i in range(8))
                Mb=(B-1)*sum(S[i]*P**i for i in range(8))
                Zb=sum(Z[i]*P**i for i in range(8))
                assert Zb==Hb&Mb
                assert max(Hb,Mb,Zb)<P**8
                fs=truth_fields(P**8,Hb,Mb)
                supplied=dict(P=P,B=B,**{f'history{i}':v for i,v in enumerate(H)},
                              **{f'Shat{i}':v+1 for i,v in enumerate(S)},
                              **{f'Zhat{i}':v+1 for i,v in enumerate(Z)},
                              **{f'bound{i}':P-v for i,v in enumerate(Z)})
                # Source evaluation uses arbitrary core witnesses; only the
                # outer interface is tested here. The theorem supplies its Pell extension.
                supplied.update({name:1 for name in AUX})
                supplied.update({f'F{i}':fs[i] for i in range(3)})
                env=execute(batch_source()[0],supplied)
                assert env['q']==16*P**8 and env['F3']==fs[3]
                assert env['Hbatch']==Hb and env['Mbatch']==Mb and env['Zbatch']==Zb
                assert all(env[a]==env[b] for a,b in batch_source()[1][14:])
                loose=execute(batch_source(unbounded=True)[0],dict(supplied,q=16*P**8))
                assert all(loose[a]==loose[b] for a,b in batch_source(unbounded=True)[1][14:])
                lane=rng.randrange(8);bad=list(Z);bad[lane]=(bad[lane]+1)%P
                assert sum(bad[i]*P**i for i in range(8)) != Hb&Mb
                mutations+=1;cases+=1
    # Bounds cannot simply be dropped: positive hatted lanes can carry.
    P=4
    good=[0,1,0,0,0,0,0,0]
    bad=[P,0,0,0,0,0,0,0]
    assert good != bad and sum(v*P**i for i,v in enumerate(good))==sum(v*P**i for i,v in enumerate(bad))
    assert all(v+1>0 for v in bad) and bad[0]+1>P
    assert (3*sum(P**i for i in range(8)) & P) == sum(v*P**i for i,v in enumerate(bad))
    # Binary cell expansion is not valid in arbitrary odd radix.
    assert packed([1,2],3) & ((3-1)*packed([1,0],3)) != packed([1,0],3)
    return dict(selected_field_fixtures=cases, altered_output_fields_rejected=mutations,
                independent_boolean_selectors='No one-hot hypothesis used by this local component',
                missing_lane_bound_counterexample=dict(radix=P, valid_outputs=good, aliased_outputs=bad),
                odd_radix_counterexample=dict(B=3,history=[1,2],selector=[1,0]),
                scope='History/selector digit types and P=B^t are hypotheses; their arithmetic compilation remains unpaid')


def exclusive_checks():
    rng=random.Random(1202317)
    cases=0
    for bits in range(4,9):
        B=1<<bits
        for t in range(1,9):
            P=B**t
            for _ in range(24):
                digits=[[rng.randrange(1,B//2) for j in range(t)] for i in range(4)]
                labels=[rng.randrange(9) for j in range(t)]
                slots=(1,1,0,0,3,3,2,2)
                H=[packed(row,B) for row in digits]
                S=[packed([int(label==i+1) for label in labels],B) for i in range(8)]
                Z=[packed([digits[slots[i]][j] if labels[j]==i+1 else 0 for j in range(t)],B) for i in range(8)]
                assert sum(Z)<P//2 and P-sum(Z)-7>0
                Hb=sum(H[slots[i]]*P**i for i in range(8));Mb=(B-1)*sum(S[i]*P**i for i in range(8))
                fs=truth_fields(P**8,Hb,Mb)
                supplied=dict(P=P,B=B,bound_global=P-sum(Z)-7,
                              **{f'history{i}':v for i,v in enumerate(H)},
                              **{f'Shat{i}':v+1 for i,v in enumerate(S)},
                              **{f'Zhat{i}':v+1 for i,v in enumerate(Z)})
                supplied.update({name:1 for name in AUX});supplied.update({f'F{i}':fs[i] for i in range(3)})
                env=execute(batch_source(True)[0],supplied)
                assert env['F3']==fs[3]
                assert all(env[a]==env[b] for a,b in batch_source(True)[1][14:])
                loose=execute(batch_source(True,True)[0],dict(supplied,q=16*P**8))
                assert all(loose[a]==loose[b] for a,b in batch_source(True,True)[1][14:])
                cases+=1
    return dict(positive_outer_fixtures=cases, B_range='2^bits, bits4..8', durations='1..8',
                completeness_margin='sum selected fields < P/2; bound_global=P-sum(Z_i)-7>0',
                scope='Requires mutually exclusive selectors and history digits strictly below B/2; unlike the general batch')


def verify():
    return dict(status='PASS_NATIVE_BINARY_MASKED_SELECTION65',
                complete_and65=source_audit(), conditional_batch120=source_audit(True),
                exclusive_batch120=source_audit(True,True),
                complete_unbounded_and64=source_audit(unbounded=True),
                conditional_unbounded_batch118=source_audit(True,unbounded=True),
                exclusive_unbounded_batch118=source_audit(True,True,True),
                primitive=primitive_checks(), batch=batch_checks(), exclusive=exclusive_checks(),
                limits='Complete AND65 has a parametric positive Pell converse inherited from selector56. '
                       'Batch120 certifies all eight digitwise selected-source fields only under the explicitly '
                       'stated dyadic cell geometry and history/Boolean-selector semantics. '
                       'Neither is a complete universal computation certificate.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
