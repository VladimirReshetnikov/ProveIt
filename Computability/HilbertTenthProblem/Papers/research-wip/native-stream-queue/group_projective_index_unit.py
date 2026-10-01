"""The native first-index equation joins the unit product, saving one SOS add."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import sympy as sp
import group_projective_first_norm_unit as parent

execute=parent.execute
residuals=parent.residuals
polynomial_source=parent.polynomial_source


def build(codes,alpha=24,beta=12,variant='six',controller_mask=False,compute_length=False):
    return rewrite(parent.build(codes,alpha,beta,variant,controller_mask,compute_length,True))


def rewrite(old):
    """Apply the local index merge to a compatible merged-first-norm packet."""
    assert old['merge_first']
    index_pair=('selection__R10b','selection__R11')
    product_pair=('four_units',1)
    assert index_pair in old['comparisons'] and product_pair in old['comparisons']
    assert ('selection__R11','+','selection__r1','selection__hpm1') in old['source']
    r1=next(row for row in old['source'] if row[0]=='selection__r1')
    assert r1[1]=='+' and r1[3]==1
    r_register=r1[2]
    source=[(name,'-','selection__R10b','selection__hpm1') if name=='selection__R11'
            else (name,op,left,right) for name,op,left,right in old['source']]
    source += [('index_unit','-','selection__R11',r_register),
               ('five_units','*','four_units','index_unit')]
    pairs=[('five_units',1) if pair==product_pair else pair
           for pair in old['comparisons'] if pair!=index_pair]
    source=parent.sort_source(source,{'x',*old['auxiliaries']})
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert counts=={'M':old['multiplications']+1,'A':old['additions_subtractions']+1}
    packet=dict(old)
    packet.update(source=source,comparisons=pairs,operations=len(source),equations=len(pairs),
                  multiplications=counts['M'],additions_subtractions=counts['A'],
                  native_r_register=r_register,
                  merged_index=True,index_parent_comparison=old['comparisons'].index(index_pair),
                  four_unit_parent_comparison=old['comparisons'].index(product_pair))
    assert len(source)==old['operations']+2 and len(pairs)==old['equations']-1
    return packet


def degree_top(packet,weights):
    old_degree,old_top=parent.degree_top(packet,weights)
    m,L=packet['m'],packet['scale_exponent']
    if packet['compute_length']:
        Dtop=packet['alpha']*weights['x']+weights['height_slack']
        Jtop=sum(weights[f'controller__edge_hat{i}'] for i in range(m))
        Ptop=8*Dtop*Jtop;nu=2
    else:
        Ptop=weights['P'];nu=1
    qtop=16*Ptop**L
    if packet['variant']=='four':
        index_degree=2*nu*L+3
        index_top=-weights['selection__h']*weights['selection__w']*(2*weights['selection__odd_half'])*qtop**2
        degree=20*nu*L+48
    else:
        index_degree=nu*(3*L+m+15)+1
        index_top=-16**4*weights['H2']*Ptop**(3*L+m+15)
        degree=nu*(44*L+6*m+90)+50
    assert degree==old_degree+2*index_degree
    return degree,old_top*index_top,index_degree,index_top


def source_checks():
    rng=random.Random(501762);records=[];cases=positive=signed=0
    tables=((),((1,2),(3,4)),tuple((i,) for i in range(1,9)))
    for codes in tables:
      for variant in ('four','six'):
       for reuse in (False,True):
        if reuse and parent.build(codes)['m']<8:continue
        for comp in (False,True):
            old=parent.build(codes,variant=variant,controller_mask=reuse,compute_length=comp,merge_first=True)
            packet=rewrite(old)
            sos,out=polynomial_source(packet)
            old_sos,old_out=polynomial_source(old)
            assert packet['auxiliaries']==old['auxiliaries']
            assert len(sos)==len(old_sos)-1
            old_counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in old_sos)
            counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in sos)
            assert counts=={'M':old_counts['M'],'A':old_counts['A']-1}
            a,b=packet['index_parent_comparison'],packet['four_unit_parent_comparison']
            for case in range(64):
                z={name:rng.randrange(1,9) if case<48 else rng.randrange(-4,5)
                   for name in packet['parameters']+packet['auxiliaries']}
                if case==0:
                    z.update({f'controller__edge_hat{i}':1 for i in range(packet['m'])})
                env=execute(sos,z);before=execute(old_sos,z)
                rr=residuals(old,before)
                assert env['index_unit']==rr[a]+1
                assert env['index_unit']==env['selection__R10b']-env[packet['native_r_register']]-env['selection__hpm1']
                target=[(rr[b]+1)*(rr[a]+1)-1 if i==b else r
                        for i,r in enumerate(rr) if i!=a]
                assert residuals(packet,env)==target and env[out]==sum(value*value for value in target)
                assert all(env[name]==before[name] for name,_,_,_ in old['source']
                           if name!='selection__R11')
                if case<48:
                    assert env['selection__q']>=16
                    assert env['selection__F3']>0
                    positive+=1
                else:signed+=1
                cases+=1
            names=packet['parameters']+packet['auxiliaries']
            weights={name:1+i%3 for i,name in enumerate(names)}
            weights['selection__tau_gap']=1
            degree,top,index_degree,index_top=degree_top(packet,weights)
            t=sp.Symbol('t')
            z={name:sp.Poly(weights[name]*t+i+1,t) for i,name in enumerate(names)}
            env=execute(packet['source'],z)
            assert env['index_unit'].degree()==index_degree and env['index_unit'].LC()==index_top
            rpolys=[sp.Poly(value,t) for value in residuals(packet,env)]
            largest=max(value.degree() for value in rpolys)
            leading=sum(value.LC()**2 for value in rpolys if value.degree()==largest)
            assert 2*largest==degree and leading==top**2
            top_bytes=(top**2).to_bytes(((top**2).bit_length()+7)//8,'big')
            records.append(dict(m=packet['m'],variant=variant,controller_mask=reuse,compute_length=comp,
                                certificate_operations=packet['operations'],equations=packet['equations'],
                                positive_witnesses=packet['positive_witnesses'],polynomial_operations=len(sos),
                                polynomial_M=counts['M'],polynomial_A=counts['A'],exact_degree=degree,
                                weighted_leading_coefficient_sha256=hashlib.sha256(top_bytes).hexdigest()))
    return dict(records=records,source_example=build(((1,2),(3,4)),variant='six',controller_mask=True,compute_length=True),
                complete_signed_source_and_SOS_identities=cases,positive_supplied_assignments=positive,
                signed_supplied_assignments=signed)


def pell(A,n):
    x,y=1,0
    for _ in range(n):
        x,y=A*x+(A*A-1)*y,x+A*y
    return x,y


def weak_checksum_checks():
    rng=random.Random(180251);cases=0
    for q in range(16,65):
      for checksum in (-1,1):
       for _ in range(16):
        total=q-checksum
        cuts=sorted(rng.sample(range(1,total),3))
        fields=[cuts[0],cuts[1]-cuts[0],cuts[2]-cuts[1],total-cuts[2]]
        r=sum(field*q**i for i,field in enumerate(fields))
        w=r//q+rng.randrange(1,5);X=w*q;Y=(2*rng.randrange(1,6)+1)*q
        E=X*Y;a=Y*(X+1);A=a+2;P=2*X*Y*Y+1
        assert q-sum(fields)==checksum and min(fields)>0
        assert q**3+q*q+q+1 <= r <= (q-2)*q**3+q*q+q+1 < q**4
        assert X>r and Y>=q and E>2*r+1 and P>A
        assert Y*(r-1)>2*(2*r+1)
        assert r>=7 and A**6>A*(A*A-1)**2
        for sign in (-1,1):
            assert 0<r+sign<E
        cases+=1
    return dict(weak_checksum_pretyping_fixtures=cases,
                scope='Both checksum signs, positive selector fields and retained bound only; no Boolean typing assumed.')


def duplication_checks():
    cases=0
    for X in range(1,13):
      for Y in range(1,13):
       for n in range(1,9):
        A=Y*(X+1)+2;P=2*X*Y*Y+1;Q2=2*A*A-1
        k=pell(P,n)[1]
        assert Q2>P and 2*A>Y+1
        twice=pell(A,2*n)[1]
        assert twice==2*A*pell(Q2,n)[1]
        assert twice>=2*A*k>k*(Y+1)
        assert pell(A,2*n+3)[1]>twice
        cases+=1
    return dict(exact_duplication_and_negative_branch_ratio_cases=cases,
                scope='Finite supplements to the parametric sign exclusion, not full native zero tuples.')


def verify():
    return dict(status='PASS_GROUP_PROJECTIVE_INDEX_UNIT',source=source_checks(),
                weak_checksum=weak_checksum_checks(),negative_branch=duplication_checks(),
                source_change=dict(multiplications_added=1,additions_added=1,equations_removed=1,
                                   polynomial_additions_saved=1),
                scope='Complete positive tuple equivalence with the merged first-root parent. '
                      'Strong norm, both ratio slacks, bound X>r and ordinary-input conditions remain explicit; '
                      'typing is invoked only after both checksum/index units are restored to+1.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
