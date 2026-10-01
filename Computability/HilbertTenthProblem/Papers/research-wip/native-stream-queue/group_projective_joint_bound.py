"""One positive joint bound for histories and selected outputs at radix16D."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import sympy as sp
import group_projective_padded_program_margin as parent
import group_projective_shifted_boundary as boundary
import group_projective_unit_product as unit

execute=parent.execute
residuals=parent.residuals
polynomial_source=parent.polynomial_source


def widen(packet):
    assert ('B','*',8,'D') in packet['source']
    return dict(packet,source=[(name,'*',16,'D') if name=='B' else (name,op,a,b)
                              for name,op,a,b in packet['source']],radix_multiplier=16)


def rewrite(packet):
    old=widen(packet)
    pair=next(pair for pair in old['comparisons'] if pair[0]=='history__history_bounded')
    assert ('history__history_bounded','+','history__history_sum','history_bound') in old['source']
    assert ('selection__Zglobal','+','selection__Zsum7','selection__bound_global') in old['source']
    replacements={
        'history__history_bounded':('+','history__history_sum','selection__Zsum7'),
        'selection__Zglobal':('+','history__history_bounded','selection__bound_global')}
    source=[(name,*replacements[name]) if name in replacements else (name,op,a,b)
            for name,op,a,b in old['source']]
    aux=[name for name in old['auxiliaries'] if name!='history_bound']
    assert len(aux)==len(old['auxiliaries'])-1
    source=unit.range_parent.sort_source(source,{'x',*aux})
    pairs=[p for p in old['comparisons'] if p!=pair]
    new=dict(old,source=source,auxiliaries=aux,comparisons=pairs,
             equations=len(pairs),positive_witnesses=len(aux),
             joint_bound=True,removed_history_bound_pair=pair)
    assert len(source)==old['operations'] and len(pairs)==old['equations']-1
    assert Counter(row[1] for row in source)==Counter(row[1] for row in old['source'])
    return new


def build(codes,alpha=24,beta=12,variant='six',controller_mask=False,compute_length=False):
    return rewrite(parent.build(codes,alpha,beta,variant,controller_mask,compute_length))


def extension(packet,z,env):
    P=env['controller__geometry_power'] if packet['compute_length'] else z['P']
    Hsum=sum(z[f'H{i}'] for i in range(4))
    return dict(z,history_bound=P-Hsum,
                selection__bound_global=Hsum+z['selection__bound_global'])


def degree_top(packet,w):
    m,L=packet['m'],packet['scale_exponent']
    if packet['compute_length']:
        Ptop=16*(packet['alpha']*w['x']+w['height_slack'])*sum(w[f'controller__edge_hat{i}'] for i in range(m))
        nu=2
    else:Ptop=w['P'];nu=1
    qtop=16*Ptop**L;stop=2*w['selection__odd_half'];ktop=w['selection__eta']+w['selection__zeta']
    if packet['variant']=='four':
        degree=12*nu*L+16
        top=w['selection__w']**2*stop**4*ktop**2*qtop**6
    else:
        astar=w['selection__w']*stop*qtop**2;ctop=ktop*stop*qtop
        rtop=16**4*w['H2']*Ptop**(3*L+m+15)
        top=(8*w['selection__ga']*astar**2*ctop)*(w['selection__i']**2*ctop**4*(2*rtop)**2)*qtop
        degree=nu*(32*L+4*m+60)+38
    return degree,top


def source_checks():
    rng=random.Random(1630297);records=[];cases=0;degree_cases=0;example=None
    tables=((),((1,2),(3,4)),((1,2,3,4,5,6,7,8,1,2),))
    for codes in tables:
      for variant in ('four','six'):
       for reuse in (False,True):
        if reuse and parent.build(codes)['m']<8:continue
        for comp in (False,True):
            old=widen(parent.build(codes,variant=variant,controller_mask=reuse,compute_length=comp))
            new=build(codes,variant=variant,controller_mask=reuse,compute_length=comp)
            old_sos,old_out=polynomial_source(old);sos,out=polynomial_source(new)
            assert len(sos)==len(old_sos)-3
            omit=old['comparisons'].index(new['removed_history_bound_pair'])
            for case in range(64):
                z={name:rng.randrange(1,10) if case<48 else rng.randrange(-4,5)
                   for name in new['parameters']+new['auxiliaries']}
                env=execute(sos,z);restored=extension(new,z,env);before=execute(old_sos,restored)
                rr= residuals(new,env);oldrr=residuals(old,before)
                assert oldrr[omit]==0
                assert rr==[v for i,v in enumerate(oldrr) if i!=omit]
                assert env[out]==before[old_out]==sum(v*v for v in rr)
                assert all(env[name]==before[name] for name,_,_,_ in new['source']
                           if name!='history__history_bounded')
                if case<48:assert restored['selection__bound_global']>0
                cases+=1
            weights={name:1+i%3 for i,name in enumerate(new['parameters']+new['auxiliaries'])}
            degree,top=degree_top(new,weights)
            # Four exact weighted polynomial evaluations cover both field and P choices.
            if new['m']==2:
                t=sp.Symbol('t')
                values={name:sp.Poly(weights[name]*t+i+1,t) for i,name in enumerate(weights)}
                env=execute(sos,values)
                assert env[out].degree()==degree and env[out].LC()==top**2
                degree_cases+=1
            counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in sos)
            records.append(dict(m=new['m'],variant=variant,controller_mask=reuse,compute_length=comp,
                certificate_operations=new['operations'],certificate_M=new['multiplications'],
                certificate_A=new['additions_subtractions'],equations=new['equations'],
                positive_witnesses=new['positive_witnesses'],polynomial_operations=len(sos),
                polynomial_M=counts['M'],polynomial_A=counts['A'],exact_degree=degree,
                weighted_leading_coefficient_bits=(top**2).bit_length(),
                weighted_leading_coefficient_sha256=hashlib.sha256((top**2).to_bytes(((top**2).bit_length()+7)//8,'big')).hexdigest()))
            if new['m']==16 and variant=='six' and reuse and comp:example=new
    return dict(records=records,source_example=example,full_source_residual_SOS_identities=cases,
                positive_assignments=3*cases//4,signed_assignments=cases//4,
                exact_weighted_polynomial_degree_checks=degree_cases)


def positive_outer_checks():
    codes=tuple((i,) for i in range(1,9))
    word=boundary.reflect_codes((boundary.physical.target_word(36),))[0]+(0,0)
    states=boundary.trace(word,37)
    assert states[-1]==[0,1,0,1]
    limit=max(37,1+max(abs(v) for row in states for v in row));D=1<<limit.bit_length()
    B=16*D;t=len(word);P=B**t;J=(P-1)//(B-1);shift=D-1
    rows=[[shift+v for v in row] for row in states[:-1]]
    H=[sum(row[i]*B**j for j,row in enumerate(rows)) for i in range(4)]
    Z=[sum((label==i+1)*rows[j][(i//2)^1]*B**j for j,label in enumerate(word)) for i in range(8)]
    E=[sum((label==i)*B**j for j,label in enumerate(word)) for i in range(16)]
    assert sum(H)+sum(Z)<=5*(2*D-1)*J
    beta=P-sum(H)-sum(Z)-7
    assert beta>= (6*D+4)*J-6>0
    records=[]
    for variant in ('four','six'):
      for reuse in (False,True):
       for comp in (False,True):
        packet=build(codes,variant=variant,controller_mask=reuse,compute_length=comp)
        z={name:1 for name in packet['parameters']+packet['auxiliaries']}
        z.update(height_slack=D-37,selection__bound_global=beta)
        if not comp:z['P']=P
        z.update({f'H{i}':v for i,v in enumerate(H)})
        z.update({f'Zhat{i}':v+1 for i,v in enumerate(Z)})
        z.update({f'controller__edge_hat{i}':v+1 for i,v in enumerate(E)})
        Hb=sum(H[(i//2)^1]*P**i for i in range(8))
        Mb=(B-1)*sum(E[i+1]*P**i for i in range(8));Zb=sum(Z[i]*P**i for i in range(8))
        Hc=sum(E[i]*P**i for i in range(16));Mc=J*sum(P**i for i in range(16))
        T=P**24;range_width=16 if reuse else 8;T2=T*P**range_width
        Rb=(2*D-1)*J*sum(P**i for i in range(range_width))
        A=Hb+P**8*Hc+T*Hb+T2*B;M=Mb+P**8*Mc+T*Rb+T2*(B-1)
        O=Zb+P**8*Hc+T*Hb;N=T2*P**2
        assert A&M==O and 0<=A<N and 0<=M<N
        fields=unit.range_parent.shared.parent.selection.parent.truth_fields(N,A,M)
        z.update({f'selection__F{i}':fields[i] for i in range(3)})
        assert min(z.values())>0
        env=execute(packet['source'],z);rr=residuals(packet,env)
        assert rr[:4]==[0]*4 and rr[-1]==0
        assert (env['range_H'],env['range_M'],env['range_Z'])==(A,M,O)
        for left,right in packet['comparisons']:
            if left in ('selection__input_A','selection__input_B','selection__Zglobal','controller__geometry_power'):
                assert env[left]==env[right]
        restored=extension(packet,z,env)
        assert min(restored.values())>0
        records.append(dict(variant=variant,controller_mask=reuse,compute_length=comp,
                            m=16,radix_multiplier=16,D=D,duration=t,positive_joint_bound=True))
    return dict(fixtures=records,scope='Exact joined-AND and positive outer equations; full native Pell extensions are parametric.')


def verify():
    return dict(status='PASS_GROUP_PROJECTIVE_JOINT_BOUND',source=source_checks(),positive_outer=positive_outer_checks(),
        certificate_saving=0,polynomial_saving=3,removed_positive_witnesses=1,
        domain='All ordinary inputs and supplied witnesses are strictly positive; fixed alpha+beta+1>=m.',
        theorem='Radix16D leaves enough room for one bound on four histories and eight mutually exclusive selected outputs.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
