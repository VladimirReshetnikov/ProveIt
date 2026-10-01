"""A fixed reflection and a shifted origin save one boundary operation.

The generic relation uses initial(1,u) and terminal e2. Reflect every fixed
macro letter to recover exactly the previous universal input relation.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp
import group_projective_computed_kernel_fields as parent

execute = parent.execute
residuals = parent.residuals
polynomial_source = parent.polynomial_source
physical = parent.parent.physical


def reflect_codes(codes):
    return tuple(tuple(physical.inverse_letter(label) for label in code) for code in codes)


def build(codes, alpha=24, beta=12, variant='six'):
    old = parent.build(codes, alpha, beta, variant)
    replacements = {
        'history__d0': ('+', 'history__c0', 'history__u'),
        'history__UP': ('*', 'history__c0', 'P'),
        'history__right_even': ('-', 'history__UP', 'D'),
        'history__VP': ('*', 'D', 'P'),
    }
    replacements.update({f'history__DdS{i}': ('*', 'history__c0', f'history__dS{i}')
                         for i in range(4)})
    source = [(name, *replacements[name]) if name in replacements else (name, op, left, right)
              for name, op, left, right in old['source'] if name != 'history__V']
    assert len(old['source'])-len(source) == 1
    available = {'x', *old['auxiliaries']}
    for name, op, left, right in source:
        assert name not in available
        assert all(isinstance(v, int) or v in available for v in (left, right))
        available.add(name)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    assert counts == {'M': old['multiplications'], 'A': old['additions_subtractions']-1}
    packet = dict(old)
    packet.update(source=source, operations=len(source), additions_subtractions=counts['A'],
                  boundary_source=[row for row in source if row[0] in ('history__input_product','history__u','D','history__c0','history__d0')],
                  removed_boundary_gate=['history__V','+','D',1],
                  changed_boundary_gates=replacements,
                  generic_relation='Paired action on(1,u), ending at(e2,e2), u=alpha*x+beta+1.')
    return packet


def expected_history(packet, values):
    v = parent.parent.data(packet, values)
    D, u, B, P = v['D'], v['u'], v['B'], values['P']
    shift = D-1
    initials, ends = (D, shift+u)*2, (shift, D)*2
    rr = []
    for i in range(4):
        delta = values[f'Zhat{2*i}']-values[f'Zhat{2*i+1}']-shift*(v['S'][2*i]-v['S'][2*i+1])
        rr.append(B*(values[f'H{i}']+delta)-values[f'H{i}']-ends[i]*P+initials[i])
    return rr


def source_checks():
    rng = random.Random(184514)
    records, cases = [], 0
    for codes in ((), ((1,), (2,)), ((1,2),(3,4)), ((1,2,3,4,5,6,7,8,1,2),)):
        for variant in parent.VARIANTS:
            old, new = parent.build(codes, variant=variant), build(codes, variant=variant)
            old_sos, old_out = polynomial_source(old)
            sos, out = polynomial_source(new)
            m, h, p = new['m'], new['h'], new['projection_additions']
            flow = new['flow']['operations']
            assert new['operations'] == 3*m+3*h+p+184+flow-3*min(h,3)
            assert len(sos) == new['operations']+3*new['equations']-1 == len(old_sos)-1
            for case in range(256):
                z = {name: rng.randrange(1,14) if case < 192 else rng.randrange(-6,7)
                     for name in new['parameters']+new['auxiliaries']}
                env, before = execute(sos, z), execute(old_sos, z)
                rr, oldrr = residuals(new, env), residuals(old, before)
                assert rr[:4] == expected_history(new, z)
                assert rr[4:] == oldrr[4:]
                assert env[out] == sum(value*value for value in rr)
                assert env[out]-before[old_out] == sum(a*a-b*b for a,b in zip(rr[:4],oldrr[:4]))
                for key in ('range_H','range_M','range_Z','range_total_scale','selection__q'):
                    assert env[key] == before[key]
                cases += 1
            t = sp.Symbol('t')
            names = new['parameters']+new['auxiliaries']
            z = {name: sp.Poly((1+i%3)*t+i+1,t) for i,name in enumerate(names)}
            env, before = execute(sos,z), execute(old_sos,z)
            degree = 12*m+232 if variant == 'four' else 24*m+444
            assert env[out].degree() == before[old_out].degree() == degree
            assert env[out].LC() == before[old_out].LC()
            counts = Counter('M' if op == '*' else 'A' for _,op,_,_ in sos)
            new['sum_of_squares'] = dict(operations=len(sos), multiplications=counts['M'],
                                         additions_subtractions=counts['A'], exact_degree=degree,
                                         weighted_leading_coefficient=str(env[out].LC()), output=out)
            records.append(new)
    return dict(packets=records,independent_complete_residual_cases=cases,
                signed_cases=cases//4,weighted_degree_slices=len(records))


def trace(word,u):
    state=[1,u,1,u];rows=[state[:]]
    for label in word:
        if label:
            i=(label-1)//2;state[i]+=(1 if label%2 else -1)*state[i^1]
        rows.append(state[:])
    return rows


def reflection_checks():
    rng=random.Random(1841);J=(-1,0,0,1)
    for _ in range(512):
        word=tuple(rng.randrange(9) for _ in range(rng.randrange(30)))
        reflected=reflect_codes((word,))[0]
        old=physical.word_matrices(word);new=physical.word_matrices(reflected)
        assert new==tuple(physical.mul(physical.mul(J,A),J) for A in old)
        u=rng.randrange(3,20)
        assert tuple(physical.action(A,(1,u)) for A in new)==tuple(physical.action(J,physical.action(A,(-1,u))) for A in old)
    return dict(arbitrary_word_reflections=512,letter_order_preserved=True)


def outer_checks():
    records=[]
    for r in (2,3,5):
        raw=physical.target_word(r)
        codes=reflect_codes((raw,physical.inverse_word(raw)))
        packet=build(codes,alpha=1,beta=1)
        for tokens in ((0,),(0,1,0)):
            indices=[]
            for token in tokens:
                start=1+sum(len(c) for c in codes[:token])
                indices.extend(range(start,start+len(codes[token])))
            indices += [0,0]
            word=[packet['edges'][i][2] for i in indices]
            u=r+1;states=trace(word,u)
            assert states[-1]==[0,1,0,1]
            limit=max(u,packet['m']//8,1+max(abs(v) for row in states for v in row))
            D=1<<limit.bit_length();shift=D-1;B=8*D;t=len(word);P=B**t;Jrep=(P-1)//(B-1)
            rows=[[shift+v for v in row] for row in states[:-1]]
            H=[sum(row[i]*B**j for j,row in enumerate(rows)) for i in range(4)]
            Z=[sum((label==i+1)*rows[j][(i//2)^1]*B**j for j,label in enumerate(word)) for i in range(8)]
            E=[sum((e==i)*B**j for j,e in enumerate(indices)) for i in range(packet['m'])]
            z={name:1 for name in packet['parameters']+packet['auxiliaries']}
            z.update(x=r-1,height_slack=D-u,P=P,J=Jrep,history_bound=P-sum(H))
            z.update({f'H{i}':v for i,v in enumerate(H)})
            z.update({f'Zhat{i}':v+1 for i,v in enumerate(Z)})
            z.update({f'controller__edge_hat{i}':v+1 for i,v in enumerate(E)})
            z['selection__bound_global']=P-sum(Z)-7;z['controller__radix_beta']=B-packet['m']
            data=parent.parent.data(packet,z)
            assert data['H']&data['M']==data['Z']
            fields=parent.parent.shared.parent.selection.parent.truth_fields(data['N'],data['H'],data['M'])
            z.update({f'selection__F{i}':fields[i] for i in range(3)})
            assert min(z.values())>0
            env=execute(packet['source'],z);rr=residuals(packet,env)
            assert rr[:5]==[0]*5
            old_index=packet['inherited_residual_indices']
            for i,parent_index in enumerate(old_index):
                if parent_index in (6,19,20,21,22,23,24,25):assert rr[i]==0
            assert trace(raw,u)[-1]!=[0,1,0,1], 'reflection is essential'
            records.append(dict(r=r,duration=t,D=D,m=packet['m'],positive_outer_checks=True))
    return dict(fixtures=records,scope='Native auxiliary placeholders are not claimed as full zeros; exact positive AND theorem supplies their extension.')


def verify():
    return dict(status='PASS_GROUP_PROJECTIVE_SHIFTED_BOUNDARY',source=source_checks(),
                reflection=reflection_checks(),positive_outer=outer_checks(),
                certificate_operations='3m+3h+p+184+f_flow-3min(h,3)',
                four_polynomial_operations='3m+3h+p+249+f_flow-3min(h,3)',
                six_polynomial_operations='3m+3h+p+243+f_flow-3min(h,3)',
                scope='Complete positive paired-action compiler. Universal input sets agree with parent after fixed macro reflection; no witness-tuple bijection is claimed.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
