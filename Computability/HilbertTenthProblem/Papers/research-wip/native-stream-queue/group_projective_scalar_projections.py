"""Remove scalar guards after choosing the shift above the fixed table.

J is restored positively from the retained history and repunit equations.
The optional P substitution is unconditionally positive but raises degree.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import sympy as sp
import group_projective_unit_product as parent

execute = parent.execute
residuals = parent.residuals
polynomial_source = parent.polynomial_source


def build(codes, alpha=24, beta=12, variant='six', controller_mask=False, compute_length=False):
    old = parent.build(codes, alpha, beta, variant, controller_mask)
    m = old['m']
    checksum = next(pair for pair in old['comparisons'] if pair[1] == 'controller__edge_checksum')
    radix = ('controller__radix_margin','B')
    repunit = ('controller__geometry_power','P')
    assert radix in old['comparisons'] and repunit in old['comparisons']
    substitutions = {'J':'computed_J'}
    if compute_length:
        substitutions['P'] = 'controller__geometry_power'
    removed_pairs = [checksum,radix]+([repunit] if compute_length else [])
    removed_aux = {'J','controller__radix_beta'}|({'P'} if compute_length else set())
    def replace(value):
        return substitutions.get(value,value) if isinstance(value,str) else value
    source = []
    for name,op,left,right in old['source']:
        if name == 'controller__radix_margin':
            assert (op,left,right) == ('+',m,'controller__radix_beta')
            continue
        if name == 'controller__edge_checksum':
            assert (op,left,right) == ('+','J',m)
            source.append(('computed_J','-',checksum[0],m))
            continue
        if name == 'D':
            assert (op,left,right) == ('+','history__u','height_slack')
            source += [('height_sum','+','history__u','height_slack'),('D','+','height_sum',m)]
            continue
        source.append((name,op,replace(left),replace(right)))
    pairs = [(replace(left),replace(right)) for left,right in old['comparisons'] if (left,right) not in removed_pairs]
    aux = [name for name in old['auxiliaries'] if name not in removed_aux]
    source = parent.range_parent.sort_source(source,{'x',*aux})
    counts = Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert len(source) == old['operations']
    assert counts == {'M':old['multiplications'],'A':old['additions_subtractions']}
    packet = dict(old)
    packet.update(source=source,comparisons=pairs,auxiliaries=aux,equations=len(pairs),
                  positive_witnesses=len(aux),compute_length=compute_length,
                  scalar_substitutions=substitutions,removed_scalar_comparisons=removed_pairs,
                  removed_scalar_comparison_indices=[old['comparisons'].index(pair) for pair in removed_pairs],
                  expanded_height='D=u+height_slack+m',
                  boundary_source=[row for row in source if row[0] in ('history__input_product','history__u','height_sum','D','history__c0','history__d0')])
    assert len(pairs) == old['equations']-2-compute_length
    assert len(aux) == old['positive_witnesses']-2-compute_length
    return packet


def extension(packet,z,env):
    old = dict(z)
    old['height_slack'] += packet['m']
    old['J'] = env['computed_J']
    old['controller__radix_beta'] = env['B']-packet['m']
    if packet['compute_length']:
        old['P'] = env['controller__geometry_power']
    return old


def degree_top(packet,weights):
    m,L=packet['m'],packet['scale_exponent']
    if packet['compute_length']:
        Dtop=packet['alpha']*weights['x']+weights['height_slack']
        Jtop=sum(weights[f'controller__edge_hat{i}'] for i in range(m))
        Ptop=8*Dtop*Jtop;d=2
    else:
        Ptop=weights['P'];d=1
    qtop=16*Ptop**L
    stop=2*weights['selection__odd_half'];ktop=weights['selection__eta']+weights['selection__zeta']
    if packet['variant']=='four':
        degree=12*d*L+16
        top=weights['selection__w']**2*stop**4*ktop**2*qtop**6
    else:
        astar=weights['selection__w']*stop*qtop**2;ctop=ktop*stop*qtop
        rtop=16**4*weights['H2']*Ptop**(3*L+m+15)
        top=(8*weights['selection__ga']*astar**2*ctop)*(weights['selection__i']**2*ctop**4*(2*rtop)**2)*qtop
        degree=d*(32*L+4*m+60)+38
    return degree,top


def source_checks():
    rng=random.Random(1532310);records=[];cases=positive=signed=0
    example=None
    tables=((),((1,2),(3,4)),((1,2,3,4,5,6,7,8,1,2),))
    for codes in tables:
      for variant in ('four','six'):
       for reuse in (False,True):
        if reuse and parent.parent.build(codes)['m']<8:continue
        old=parent.build(codes,variant=variant,controller_mask=reuse)
        old_sos,old_out=polynomial_source(old)
        for compute_length in (False,True):
            new=build(codes,variant=variant,controller_mask=reuse,compute_length=compute_length)
            sos,out=polynomial_source(new)
            assert len(old_sos)-len(sos)==6+3*compute_length
            for case in range(64):
                z={name:rng.randrange(1,9) if case<48 else rng.randrange(-4,5)
                   for name in new['parameters']+new['auxiliaries']}
                # Include the off-zero J=0 boundary in the positive graph audit.
                if case==0:
                    z.update({f'controller__edge_hat{i}':1 for i in range(new['m'])})
                env=execute(sos,z);restored=extension(new,z,env);before=execute(old_sos,restored)
                rr,oldrr=residuals(new,env),residuals(old,before)
                omit=new['removed_scalar_comparison_indices']
                assert all(oldrr[i]==0 for i in omit)
                assert rr==[r for i,r in enumerate(oldrr) if i not in omit]
                assert env[out]==before[old_out]==sum(r*r for r in rr)
                old_outputs={row[0] for row in old['source']}
                assert all(env[name]==before[name] for name,_,_,_ in new['source'] if name in old_outputs)
                if case<48:
                    assert env['computed_J']>=0 and env['B']>new['m']
                    assert restored['height_slack']>0 and restored['controller__radix_beta']>0
                    if compute_length:assert restored['P']>=1
                    if env['computed_J']==0 and compute_length:
                        assert restored['P']==1
                        assert z['history_bound']+sum(z[f'H{i}'] for i in range(4))-1>=4
                    positive+=1
                else:signed+=1
                cases+=1
            t=sp.Symbol('t');names=new['parameters']+new['auxiliaries']
            weights={name:1+i%3 for i,name in enumerate(names)}
            z={name:sp.Poly(weights[name]*t+i+1,t) for i,name in enumerate(names)}
            env=execute(sos,z);degree,top=degree_top(new,weights)
            assert env[out].degree()==degree,(new['m'],variant,reuse,compute_length,env[out].degree(),degree)
            assert env[out].LC()==top**2
            counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in sos)
            records.append(dict(m=new['m'],variant=variant,controller_mask=reuse,compute_length=compute_length,
                                certificate_operations=new['operations'],equations=new['equations'],
                                positive_witnesses=new['positive_witnesses'],polynomial_operations=len(sos),
                                polynomial_M=counts['M'],polynomial_A=counts['A'],exact_degree=degree,
                                weighted_leading_coefficient_bits=(top**2).bit_length(),
                                weighted_leading_coefficient_sha256=hashlib.sha256((top**2).to_bytes(((top**2).bit_length()+7)//8,'big')).hexdigest(),
                                removed_comparisons=new['removed_scalar_comparisons']))
            if variant=='six' and reuse and compute_length:example=new
    return dict(records=records,full_source_and_SOS_graph_identities=cases,positive_assignments=positive,
                signed_assignments=signed,source_example=example)


def positive_outer_checks():
    physical=parent.parent.physical
    raw=physical.target_word(2);codes=parent.parent.reflect_codes((raw,physical.inverse_word(raw)))
    old=parent.parent.build(codes,alpha=1,beta=1)
    indices=list(range(1,1+len(codes[0])))+[0,0]
    word=[old['edges'][i][2] for i in indices];states=parent.parent.trace(word,3)
    assert states[-1]==[0,1,0,1]
    m=old['m'];limit=max(3+m,1+max(abs(v) for row in states for v in row));D=1<<limit.bit_length()
    B=8*D;t=len(word);P=B**t;J=(P-1)//(B-1);shift=D-1
    rows=[[shift+v for v in row] for row in states[:-1]]
    H=[sum(row[i]*B**j for j,row in enumerate(rows)) for i in range(4)]
    Z=[sum((label==i+1)*rows[j][(i//2)^1]*B**j for j,label in enumerate(word)) for i in range(8)]
    E=[sum((e==i)*B**j for j,e in enumerate(indices)) for i in range(m)]
    records=[]
    for variant in ('four','six'):
      for reuse in (False,True):
       for comp in (False,True):
        packet=build(codes,alpha=1,beta=1,variant=variant,controller_mask=reuse,compute_length=comp)
        z={name:1 for name in packet['parameters']+packet['auxiliaries']}
        z.update(height_slack=D-3-m,history_bound=P-sum(H))
        if not comp:z['P']=P
        z.update({f'H{i}':v for i,v in enumerate(H)});z.update({f'Zhat{i}':v+1 for i,v in enumerate(Z)})
        z.update({f'controller__edge_hat{i}':v+1 for i,v in enumerate(E)})
        z['selection__bound_global']=P-sum(Z)-7
        test=dict(z,P=P,J=J,height_slack=D-3)
        v=parent.region_data(packet,test)
        assert v['H']&v['M']==v['Z']
        fields=parent.range_parent.shared.parent.selection.parent.truth_fields(v['N'],v['H'],v['M'])
        z.update({f'selection__F{i}':fields[i] for i in range(3)})
        env=execute(packet['source'],z);rr=residuals(packet,env)
        assert min(z.values())>0 and env['computed_J']==J and env['controller__geometry_power']==P
        assert rr[:5]==[0]*5 and rr[-1]==0
        for name in ('range_H','range_M','range_Z'):
            assert env[name]==v[name[-1]]
        records.append(dict(variant=variant,controller_mask=reuse,compute_length=comp,m=m,duration=t,D=D,positive_outer=True))
    return dict(fixtures=records,scope='No full Pell zeros are materialized; the proof supplies the positive extension.')


def verify():
    return dict(status='PASS_GROUP_PROJECTIVE_SCALAR_PROJECTIONS',source=source_checks(),positive_outer=positive_outer_checks(),
                certificate_operations='3m+3h+p+186+f_flow-3min(h,3)-controller_mask',
                generic_relation='Complete paired action on(1,u) ending at(e2,e2); shifted fixed universal macros retain ordinary input.',
                scope='Repunit positivity is conditional on retained scalar equations; the stronger height convention preserves accepted inputs, not every old tuple.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
