"""Compute the remaining checksum field on the positive-checksum branch.

The zero-output radix region proves positivity before typing. The coupled
parent's negative checksum branch normalizes before the field is erased.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import sympy as sp
import group_projective_computed_input_fields as parent

execute=parent.execute
residuals=parent.residuals
polynomial_source=parent.polynomial_source


def rewrite(old):
    expected=[('selection__shared_sum02','+','selection__F0','computed_input_F2'),
              ('selection__bs_Q','+','selection__shared_sum02','selection__padded_A'),
              ('selection__bs_q','-','selection__q','selection__bs_Q'),
              ('unit_product','*','unit_pair','selection__bs_q')]
    assert all(row in old['source'] for row in expected)
    aliases={'selection__F0':'computed_checksum_F0','selection__bs_q':1,'unit_product':'unit_pair'}
    def sub(value):return aliases.get(value,value)
    source=[]
    for name,op,a,b in old['source']:
        if name=='unit_product':continue
        if name=='selection__bs_Q':source.append((name,'-','selection__q','selection__padded_A'))
        elif name=='selection__shared_sum02':source.append((name,'-','selection__bs_Q',1))
        elif name=='selection__bs_q':source.append(('computed_checksum_F0','-','selection__shared_sum02','computed_input_F2'))
        else:source.append((name,op,sub(a),sub(b)))
    aux=[name for name in old['auxiliaries'] if name!='selection__F0']
    assert len(aux)==len(old['auxiliaries'])-1
    pairs=[(sub(a),sub(b)) for a,b in old['comparisons']]
    source=parent.parent.index.parent.sort_source(source,{'x',*aux})
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert counts=={'M':old['multiplications']-1,'A':old['additions_subtractions']}
    packet=dict(old,source=source,comparisons=pairs,auxiliaries=aux,operations=len(source),
                multiplications=counts['M'],positive_witnesses=len(aux),computed_checksum_field=True,
                computed_checksum_aliases=aliases)
    assert len(source)==old['operations']-1 and pairs==old['comparisons']
    return packet


def build(codes,alpha=24,beta=12,variant='six',controller_mask=False,compute_length=False):
    return rewrite(parent.build(codes,alpha,beta,variant,controller_mask,compute_length))


def extend(z,env):return dict(z,selection__F0=env['computed_checksum_F0'])


def degree_top(packet,weights):
    _,_,degrees,tops=parent.degree_top(packet,weights)
    del degrees['selection__bs_q'];del tops['selection__bs_q']
    top=1
    for value in tops.values():top*=value
    return 2*sum(degrees.values()),top,degrees,tops


def source_checks():
    rng=random.Random(2873376);records=[];cases=0;example=None
    for codes in ((),((1,2),(3,4)),((1,2,3,4,5,6,7,8,1,2),)):
      for variant in ('four','six'):
       for reuse in (False,True):
        if reuse and parent.build(codes)['m']<8:continue
        for comp in (False,True):
            old=parent.build(codes,variant=variant,controller_mask=reuse,compute_length=comp)
            packet=rewrite(old);sos,out=polynomial_source(packet);old_sos,old_out=polynomial_source(old)
            assert len(sos)==len(old_sos)-1
            for case in range(64):
                z={name:rng.randrange(1,9) if case<48 else rng.randrange(-4,5)
                   for name in packet['parameters']+packet['auxiliaries']}
                env=execute(sos,z);before=execute(old_sos,extend(z,env))
                assert before['selection__bs_q']==1
                assert residuals(packet,env)==residuals(old,before)
                assert env[out]==before[old_out]==sum(v*v for v in residuals(packet,env))
                assert all(env[name]==before[name] for name,_,_,_ in packet['source']
                           if name in before and name!='selection__bs_Q')
                assert env['computed_checksum_F0']==16*(env['range_total_scale']-env['range_H']-env['range_M']+env['range_Z'])-15
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
            C=3*m+3*h+p+185+f-3*min(h,3)-reuse;nu=1+comp;L=packet['scale_exponent']
            assert packet['operations']==C+3 and len(sos)==C+(38 if variant=='four' else 32)-3*comp
            assert packet['equations']==(12 if variant=='four' else 10)-comp
            assert packet['positive_witnesses']==m+(30 if variant=='four' else 28)-comp
            assert degree==(22*nu*L+54 if variant=='four' else nu*(38*L+2*m+30)+60)
            encoded=highest.to_bytes((highest.bit_length()+7)//8,'big')
            records.append(dict(m=m,variant=variant,controller_mask=reuse,compute_length=comp,
                certificate_operations=packet['operations'],certificate_M=packet['multiplications'],
                certificate_A=packet['additions_subtractions'],equations=packet['equations'],
                positive_witnesses=packet['positive_witnesses'],polynomial_operations=len(sos),
                polynomial_M=counts['M'],polynomial_A=counts['A'],exact_degree=degree,
                residual_degrees=[int(v.degree()) if not v.is_zero else None for v in polys],
                weighted_highest_coefficient_sha256=hashlib.sha256(encoded).hexdigest()))
            if m==16 and variant=='six' and reuse and comp:example=packet
    assert example['operations']==261 and example['equations']==9 and example['positive_witnesses']==43
    assert len(polynomial_source(example)[0])==287
    return dict(records=records,source_example=example,full_graph_and_SOS_identities=cases,
                positive_supplied_assignments=3*cases//4,signed_supplied_assignments=cases//4,
                exact_residual_and_five_factor_degree_audits=len(records))


def positive_and_branch_checks():
    rng=random.Random(1615287);outer=normalizations=0;non_dyadic=0
    codes=((1,2),(3,4))
    for variant in ('four','six'):
      for reuse in (False,True):
       for comp in (False,True):
        old=parent.build(codes,variant=variant,controller_mask=reuse,compute_length=comp)
        packet=rewrite(old);sos,out=polynomial_source(packet);old_sos,old_out=polynomial_source(old)
        for case in range(64):
            z={name:rng.randrange(1,4) for name in packet['parameters']+packet['auxiliaries']}
            E=[rng.randrange(0,3) for _ in range(packet['m'])]
            if case==0:E=[1]+[0]*(packet['m']-1)
            if not any(E):E[0]=1
            J=sum(E);u=packet['alpha']*z['x']+packet['beta']+1;D=u+z['height_slack'];B=16*D;P=(B-1)*J+1
            if not comp:z['P']=P
            z.update({f'controller__edge_hat{i}':v+1 for i,v in enumerate(E)})
            H=[rng.randrange(1,1+P//32) for _ in range(4)];Z=[rng.randrange(0,1+P//64) for _ in range(8)]
            z.update({f'H{i}':v for i,v in enumerate(H)});z.update({f'Zhat{i}':v+1 for i,v in enumerate(Z)})
            z['selection__bound_global']=P-sum(H)-sum(Z)-7
            env=execute(packet['source'],z);T2=P**(packet['scale_exponent']-2)
            assert env['range_H']-T2*B<T2 and env['range_M']-T2*(B-1)<T2
            assert env['range_H']+env['range_M']-env['range_Z']<(2*B+1)*T2<P*P*T2
            assert env['computed_checksum_F0']>0 and env['computed_checksum_F0']%16==1
            assert min(extend(z,env).values())>0
            outer+=1;non_dyadic+=bool(B&(B-1) or P&(P-1))
            # Structured positive Q=+/-1 tuples: satisfy the packing and linear
            # unit relations, leaving all norm residuals unrestricted.
            for epsilon in (-1,1):
                oldz=extend(z,env);oldz['selection__F0']+=1-epsilon
                oe=execute(old['source'],oldz);r=oe['selection__bs_packed']
                if variant=='four':oldz['selection__r']=r
                oldz['selection__w']=(r+packet['scale_exponent'])//oe['selection__q']+1
                oe=execute(old['source'],oldz)
                oldz['selection__bound_beta']=oe['selection__wn2']-r
                oldz['selection__zeta']=r+oe['selection__hpm1']+epsilon-oldz['selection__eta']
                oe=execute(old['source'],oldz)
                if variant=='four':oldz['selection__c']=oe['selection__R10a']
                oe=execute(old['source'],oldz);c=oe['selection__R10a']
                oldz['selection__f']=1
                oldz['selection__o']=(oldz['selection__j']+1)*c-2*oe['selection__R11']+1
                oe=execute(old_sos,oldz)
                assert (oe['selection__bs_q'],oe['index_unit'],oe['linear_unit'])==(epsilon,epsilon,1)
                norm=parent.parent.normalize(old,oldz,epsilon)
                projected={name:v for name,v in norm.items() if name!='selection__F0'}
                ne=execute(sos,projected)
                assert norm['selection__F0']==ne['computed_checksum_F0']
                assert min(oldz.values())>0 and min(projected.values())>0
                assert residuals(old,oe)==residuals(packet,ne) and oe[old_out]==ne[out]
                assert ne['selection__bs_X_bound']==ne['selection__wn2']
                normalizations+=1
    return dict(positive_outer_bound_fixtures=outer,fixtures_with_nondyadic_B_or_P=non_dyadic,
                positive_both_branch_full_residual_SOS_normalizations=normalizations,
                scope='Outer-bound fixtures need no typing. Branch fixtures impose Q=Nk=epsilon,L=1 and the native X bound, but do not claim norm equations or full Pell zeros.')


def verify():
    return dict(status='PASS_GROUP_PROJECTIVE_COMPUTED_CHECKSUM_FIELD',source=source_checks(),
                positivity_and_normalization=positive_and_branch_checks(),
                scope='Complete ordinary-input equivalence on the Q=1 slice after the coupled parent\'s positive normalization. Not an erasure bijection for all parent tuples.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
