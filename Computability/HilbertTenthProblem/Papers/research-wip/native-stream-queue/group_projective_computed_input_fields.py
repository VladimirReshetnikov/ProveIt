"""The joined zero-output radix region makes both input fields positive.

Compute the two native input fields at the existing port-gate cost and
erase their two comparisons and positive witnesses.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import sympy as sp
import group_projective_coupled_linear_unit as parent

execute=parent.execute
residuals=parent.residuals
polynomial_source=parent.polynomial_source


def rewrite(old):
    pairs=[('selection__input_A','selection__padded_A'),
           ('selection__input_B','selection__padded_B')]
    definitions=[('selection__input_A','+','selection__F1','selection__F3'),
                 ('selection__input_B','+','selection__F2','selection__F3')]
    assert all(row in old['source'] for row in definitions)
    assert all(pair in old['comparisons'] for pair in pairs)
    aliases={'selection__F1':'computed_input_F1','selection__F2':'computed_input_F2',
             'selection__input_A':'selection__padded_A','selection__input_B':'selection__padded_B'}
    def sub(x):return aliases.get(x,x)
    source=[]
    for name,op,a,b in old['source']:
        if name=='selection__input_A':source.append(('computed_input_F1','-','selection__padded_A','selection__F3'))
        elif name=='selection__input_B':source.append(('computed_input_F2','-','selection__padded_B','selection__F3'))
        else:source.append((name,op,sub(a),sub(b)))
    aux=[name for name in old['auxiliaries'] if name not in ('selection__F1','selection__F2')]
    assert len(aux)==len(old['auxiliaries'])-2
    comparisons=[(sub(a),sub(b)) for a,b in old['comparisons'] if (a,b) not in pairs]
    source=parent.index.parent.sort_source(source,{'x',*aux})
    assert Counter(row[1]=='*' for row in source)==Counter(row[1]=='*' for row in old['source'])
    packet=dict(old,source=source,comparisons=comparisons,auxiliaries=aux,
                positive_witnesses=len(aux),equations=len(comparisons),
                computed_input_fields=True,computed_input_aliases=aliases,
                removed_input_comparisons=[old['comparisons'].index(pair) for pair in pairs])
    assert len(source)==old['operations'] and len(comparisons)==old['equations']-2
    return packet


def build(codes,alpha=24,beta=12,variant='six',controller_mask=False,compute_length=False):
    return rewrite(parent.build(codes,alpha,beta,variant,controller_mask,compute_length))


def extend(z,env):
    return dict(z,selection__F1=env['computed_input_F1'],selection__F2=env['computed_input_F2'])


def degree_top(packet,weights):
    # Neither deleted supplied coordinate occurs in the parent's leading form.
    return parent.degree_top(packet,weights)


def source_checks():
    rng=random.Random(2883544);records=[];cases=negative_extensions=0;example=None
    for codes in ((),((1,2),(3,4)),((1,2,3,4,5,6,7,8,1,2),)):
      for variant in ('four','six'):
       for reuse in (False,True):
        if reuse and parent.build(codes)['m']<8:continue
        for comp in (False,True):
            old=parent.build(codes,variant=variant,controller_mask=reuse,compute_length=comp)
            packet=rewrite(old);sos,out=polynomial_source(packet);old_sos,old_out=polynomial_source(old)
            omit=packet['removed_input_comparisons']
            assert len(sos)==len(old_sos)-6
            for case in range(64):
                z={name:rng.randrange(1,9) if case<48 else rng.randrange(-4,5)
                   for name in packet['parameters']+packet['auxiliaries']}
                env=execute(sos,z);before=execute(old_sos,extend(z,env))
                rr=residuals(old,before)
                assert all(rr[i]==0 for i in omit)
                assert residuals(packet,env)==[v for i,v in enumerate(rr) if i not in omit]
                assert env[out]==before[old_out]==sum(v*v for v in residuals(packet,env))
                assert all(env[name]==before[name] for name,_,_,_ in packet['source'] if name in before)
                for field,register in packet['computed_input_aliases'].items():
                    assert before[field]==env[register]
                if case<48 and min(env['computed_input_F1'],env['computed_input_F2'])<=0:
                    negative_extensions+=1
                cases+=1
            weights={name:1+i%3 for i,name in enumerate(packet['parameters']+packet['auxiliaries'])}
            weights['selection__tau_gap']=1
            degree,top,uds,tops=degree_top(packet,weights)
            t=sp.Symbol('t');z={name:sp.Poly(weights[name]*t+i+1,t) for i,name in enumerate(weights)}
            env=execute(packet['source'],z)
            for name in uds:assert (env[name].degree(),env[name].LC())==(uds[name],tops[name]),name
            polys=[sp.Poly(v,t) for v in residuals(packet,env)];largest=max(v.degree() for v in polys)
            highest=int(sum(v.LC()**2 for v in polys if v.degree()==largest))
            assert 2*largest==degree and highest==top*top
            counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in sos)
            m,h,p=packet['m'],packet['h'],packet['projection_additions'];f=packet['flow']['operations']
            C=3*m+3*h+p+185+f-3*min(h,3)-reuse
            assert packet['operations']==C+4
            assert packet['equations']==(12 if variant=='four' else 10)-comp
            assert packet['positive_witnesses']==m+(31 if variant=='four' else 29)-comp
            assert len(sos)==C+(39 if variant=='four' else 33)-3*comp
            encoded=highest.to_bytes((highest.bit_length()+7)//8,'big')
            records.append(dict(m=m,variant=variant,controller_mask=reuse,compute_length=comp,
                certificate_operations=packet['operations'],certificate_M=packet['multiplications'],
                certificate_A=packet['additions_subtractions'],equations=packet['equations'],
                positive_witnesses=packet['positive_witnesses'],polynomial_operations=len(sos),
                polynomial_M=counts['M'],polynomial_A=counts['A'],exact_degree=degree,
                residual_degrees=[int(v.degree()) if not v.is_zero else None for v in polys],
                input_field_degrees=[int(env[name].degree()) for name in ('computed_input_F1','computed_input_F2')],
                weighted_highest_coefficient_sha256=hashlib.sha256(encoded).hexdigest()))
            if m==16 and variant=='six' and reuse and comp:example=packet
    assert example['operations']==262 and example['equations']==9 and example['positive_witnesses']==44
    assert len(polynomial_source(example)[0])==288
    return dict(records=records,source_example=example,full_graph_and_SOS_identities=cases,
                positive_supplied_assignments=3*cases//4,signed_supplied_assignments=cases//4,
                positive_off_zero_assignments_with_nonpositive_computed_fields=negative_extensions,
                exact_residual_and_unit_degree_audits=len(records))


def pretyping_checks():
    rng=random.Random(216288);cases=0;non_dyadic=0;by_J={}
    codes=((1,2),(3,4))
    for variant in ('four','six'):
      for reuse in (False,True):
       for comp in (False,True):
        packet=build(codes,variant=variant,controller_mask=reuse,compute_length=comp)
        for case in range(96):
            z={name:rng.randrange(1,5) for name in packet['parameters']+packet['auxiliaries']}
            z['x']=rng.randrange(1,5);z['height_slack']=rng.randrange(1,12)
            edges=[rng.randrange(0,4) for _ in range(packet['m'])]
            if case==0:edges=[1]+[0]*(packet['m']-1)
            if not any(edges):edges[0]=1
            J=sum(edges);D=packet['alpha']*z['x']+packet['beta']+1+z['height_slack']
            B=16*D;P=(B-1)*J+1
            if not comp:z['P']=P
            z.update({f'controller__edge_hat{i}':e+1 for i,e in enumerate(edges)})
            # Positive histories/output hats with a strictly positive joint slack.
            H=[rng.randrange(1,1+P//32) for _ in range(4)]
            Z=[rng.randrange(0,1+P//64) for _ in range(8)]
            z.update({f'H{i}':v for i,v in enumerate(H)})
            z.update({f'Zhat{i}':v+1 for i,v in enumerate(Z)})
            z['selection__bound_global']=P-sum(H)-sum(Z)-7
            assert z['selection__bound_global']>0
            env=execute(packet['source'],z)
            T2=P**(packet['scale_exponent']-2)
            assert env['range_Z']<T2
            assert env['range_H']>=T2*B and env['range_M']>=T2*(B-1)
            assert env['computed_input_F1']>0 and env['computed_input_F2']>0
            restored=extend(z,env);assert min(restored.values())>0
            assert env['computed_input_F1']%16==4 and env['computed_input_F2']%16==2
            if B&(B-1) or P&(P-1):non_dyadic+=1
            by_J[J]=by_J.get(J,0)+1;cases+=1
    return dict(positive_outer_bound_fixtures=cases,fixtures_with_nondyadic_B_or_P=non_dyadic,
                minimal_J_fixtures=by_J[1],
                scope='Only raw controller sum, repunit and joint scalar bound are imposed. No norm, bit partition, Boolean controller or transport equation is assumed.')


def verify():
    return dict(status='PASS_GROUP_PROJECTIVE_COMPUTED_INPUT_FIELDS',source=source_checks(),
                pretyping=pretyping_checks(),
                scope='Positive zero-set graph elimination of both native input fields. Positivity is restored from retained outer bounds before invoking any native sign or typing theorem.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
