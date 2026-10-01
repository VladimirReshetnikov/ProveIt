"""Merge the joint scalar bound after an independent native-sign recovery.

The negative native-index sign is excluded by the exact binary population
at r-2 and the unchanged computed checksum. This is a positive-domain
argument, not an integer-zero-set identity on arbitrary signed witnesses.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import sympy as sp
import group_projective_port_bias_folding as parent

execute=parent.execute
residuals=parent.residuals


def rewrite(old):
    assert old['strong_unit_merged'] and old['shifted_X_quotient']
    joint=('selection__Zglobal','controller__lane_factor0');unit=('seven_units',1)
    assert old['comparisons'].count(joint)==old['comparisons'].count(unit)==1
    P='controller__geometry_power' if old['compute_length'] else 'P'
    rows={row[0]:row for row in old['source']}
    assert rows['controller__lane_factor0']==('controller__lane_factor0','+',P,1)
    assert rows['selection__Zglobal']==('selection__Zglobal','+','history__history_bounded','selection__bound_global')
    assert {n for n,_,a,b in old['source'] if 'selection__bound_global' in (a,b)}=={'selection__Zglobal'}
    assert not any('selection__bound_global' in pair for pair in old['comparisons'])
    source=old['source']+[
        ('joint_bound_unit','-','selection__Zglobal',P),
        ('eight_units','*','seven_units','joint_bound_unit')]
    pairs=[('eight_units',1) if pair==unit else pair for pair in old['comparisons'] if pair!=joint]
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert counts=={'M':old['multiplications']+1,'A':old['additions_subtractions']+1}
    return dict(old,source=source,comparisons=pairs,operations=len(source),
                multiplications=counts['M'],additions_subtractions=counts['A'],equations=len(pairs),
                joint_bound_unit_merged=True,unit_register='eight_units',
                unit_comparison_index=pairs.index(('eight_units',1)),
                removed_joint_comparison_index=old['comparisons'].index(joint))


def build(codes,alpha=24,beta=12,controller_mask=False,compute_length=False):
    return rewrite(parent.build(codes,alpha,beta,'strong',controller_mask,compute_length))


def polynomial_source(packet):
    source=list(packet['source']);squares=[]
    for index,(a,b) in enumerate(packet['comparisons']):
        if (a,b)==('eight_units',1):continue
        name=f'joint_outer_residual{index}';square=f'joint_outer_square{index}'
        source += [(name,'-',a,b),(square,'*',name,name)];squares.append(square)
    total=squares[0]
    for index,square in enumerate(squares[1:],1):
        name=f'joint_outer_sum{index}';source.append((name,'+',total,square));total=name
    source += [('joint_outer_positive','+',total,1),
               ('joint_outer_product','*','eight_units','joint_outer_positive'),
               ('joint_outer_output','-','joint_outer_product',1)]
    return source,'joint_outer_output'


def degree_top(packet,w):
    degree,top,parts=parent.degree_top(packet,w)
    nu=1+packet['compute_length']
    if packet['compute_length']:
        joint_top=-16*(packet['alpha']*w['x']+w['height_slack'])*sum(w[f'controller__edge_hat{i}'] for i in range(packet['m']))
    else:
        joint_top=sum(w[f'H{i}'] for i in range(4))+sum(w[f'Zhat{i}'] for i in range(8))+w['selection__bound_global']-w['P']
    return degree+nu,top*joint_top,dict(parent_parts=parts,joint_degree=nu,joint_top=joint_top,
        unit_degree=parts['unit_degree']+nu,unit_top=parts['unit_top']*joint_top,
        outer_residual_degree=parts['outer_residual_degree'],outer_top=parts['outer_top'])


def population_checks():
    cases=0;hist={}
    for t in range(4,10):
        q=1<<t;N=q//16;count=0
        for a in range(N):
         for b in range(N-a):
          for c in range(N-a-b):
            fields=(q-15-16*(a+b+c),4+16*b,2+16*c,8+16*a)
            assert min(fields)>0 and sum(fields)==q-1 and max(fields)<q
            r=sum(F*q**i for i,F in enumerate(fields));rp=r-2
            assert q<rp and rp>156 and r%16==1
            j=((r-1)&-(r-1)).bit_length()-1
            assert j>=4 and rp.bit_count()==r.bit_count()+j-2
            assert r.bit_count()==sum(F.bit_count() for F in fields)>=t
            assert rp.bit_count()>=t+2
            count+=1;cases+=1
        hist[t]=count
    return dict(exhaustive_padded_checksum_cases=cases,counts_by_log2q=hist,
        scope='Integer packing/population identities only. Raw Pell exponent/valuation recovery is proved parametrically, not inferred from these fixtures.')


def source_checks():
    rng=random.Random(2773504);records=[];cases=0;example=None
    for codes in ((),((1,2),(3,4)),((1,2,3,4,5,6,7,8,1,2),)):
      for reuse in (False,True):
        if reuse and parent.build(codes)['m']<8:continue
        for comp in (False,True):
            old=parent.build(codes,controller_mask=reuse,compute_length=comp)
            packet=rewrite(old);source,out=polynomial_source(packet);prior,prior_out=parent.polynomial_source(old)
            assert packet['source'][:old['operations']]==old['source'] and packet['auxiliaries']==old['auxiliaries']
            counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
            before_counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in prior)
            assert counts=={'M':before_counts['M'],'A':before_counts['A']-1}
            omitted=packet['removed_joint_comparison_index'];old_ui=old['unit_comparison_index']
            for case in range(64):
                z={n:rng.randrange(1,8) if case<48 else rng.randrange(-4,5)
                   for n in packet['parameters']+packet['auxiliaries']}
                env=execute(source,z);before=execute(prior,z);rr=residuals(old,before)
                P=env['controller__geometry_power'] if comp else z['P']
                joint=sum(z[f'H{i}'] for i in range(4))+sum(z[f'Zhat{i}'] for i in range(8))+z['selection__bound_global']-P
                assert env['joint_bound_unit']==joint==rr[omitted]+1
                unit=(rr[old_ui]+1)*joint
                target=[unit-1 if i==old_ui else v for i,v in enumerate(rr) if i!=omitted]
                assert residuals(packet,env)==target
                outer=[v for i,v in enumerate(rr) if i not in (omitted,old_ui)]
                assert env[out]==unit*(1+sum(v*v for v in outer))-1
                assert all(env[n]==before[n] for n,_,_,_ in old['source'])
                cases+=1
            names=packet['parameters']+packet['auxiliaries'];w={n:1+i%3 for i,n in enumerate(names)}
            w['selection__tau_gap']=1
            for i in range(packet['m']):w[f'controller__edge_hat{i}']=1<<i
            degree,top,parts=degree_top(packet,w)
            t=sp.Symbol('t');vals={n:sp.Poly(w[n]*t+i+1,t) for i,n in enumerate(names)}
            # The parent exact factor audits certify the unchanged native prefix.
            # Replay only the small outer dependency closure here; all new full
            # products and complete residuals are checked numerically above.
            roots=['joint_bound_unit']+[v for pair in packet['comparisons'] if pair!=('eight_units',1) for v in pair if isinstance(v,str)]
            rows={row[0]:row for row in packet['source']};needed=set()
            def visit(n):
                if not isinstance(n,str) or n not in rows or n in needed:return
                needed.add(n);visit(rows[n][2]);visit(rows[n][3])
            for n in roots:visit(n)
            small=[row for row in packet['source'] if row[0] in needed]
            env=execute(small,vals)
            assert (env['joint_bound_unit'].degree(),env['joint_bound_unit'].LC())==(parts['joint_degree'],parts['joint_top'])
            def val(v):return env[v] if isinstance(v,str) else v
            outer=[sp.Poly(val(a)-val(b),t) for a,b in packet['comparisons'] if (a,b)!=('eight_units',1)]
            positive=sp.Poly(1,t)+sum((v*v for v in outer),sp.Poly(0,t))
            assert (positive.degree(),positive.LC())==(2*parts['outer_residual_degree'],parts['outer_top'])
            assert degree==parts['unit_degree']+positive.degree() and top==parts['unit_top']*positive.LC()!=0
            m,h,p=packet['m'],packet['h'],packet['projection_additions'];f=packet['flow']['operations'];b=packet['port_bias_saving']['operations']
            C=3*m+3*h+p+185+f-3*min(h,3)-reuse
            assert packet['operations']==C+3-b and packet['equations']==7-comp
            assert packet['positive_witnesses']==m+27-comp and len(source)==C+23-3*comp-b
            encoded=abs(top).to_bytes((abs(top).bit_length()+7)//8,'big')
            records.append(dict(m=m,controller_mask=reuse,compute_length=comp,port_bias_saving=b,
                certificate_operations=packet['operations'],certificate_M=packet['multiplications'],certificate_A=packet['additions_subtractions'],
                equations=packet['equations'],positive_witnesses=packet['positive_witnesses'],polynomial_operations=len(source),
                polynomial_M=counts['M'],polynomial_A=counts['A'],exact_degree=degree,
                unit_degree=parts['unit_degree'],outer_residual_degree=parts['outer_residual_degree'],
                weighted_leading_coefficient_sign=1 if top>0 else -1,
                weighted_leading_coefficient_sha256=hashlib.sha256(encoded).hexdigest()))
            if m==16 and reuse and comp:
                example=dict(packet,polynomial_finalizer=source[packet['operations']:],polynomial_output=out)
                assert (len(source),degree,packet['positive_witnesses'])==(277,3504,42)
    return dict(records=records,source_example=example,complete_signed_residual_and_output_cases=cases,
                positive_supplied_assignments=3*cases//4,signed_supplied_assignments=cases//4,
                exact_new_unit_and_outer_degree_audits=len(records))


def pretyping_checks():
    rng=random.Random(27716);cases=0
    codes=((1,2,3,4,5,6,7,8,1,2),)
    for reuse in (False,True):
     for comp in (False,True):
      old=parent.build(codes,controller_mask=reuse,compute_length=comp);packet=rewrite(old)
      for sign in (-1,1):
       for _ in range(16):
        z={n:rng.randrange(1,4) for n in packet['parameters']+packet['auxiliaries']}
        z['x']=1;D=rng.choice((64,128));u=packet['alpha']+packet['beta']+1
        z['height_slack']=D-u;J=rng.randrange(1,4);P=(16*D-1)*J+1
        for i in range(packet['m']):z[f'controller__edge_hat{i}']=1+(J if i==0 else 0)
        if not comp:z['P']=P
        z['selection__bound_global']=P+sign-sum(z[f'H{i}'] for i in range(4))-sum(z[f'Zhat{i}'] for i in range(8))
        assert min(z.values())>0
        env=execute(packet['source'],z)
        assert env['joint_bound_unit']==sign
        restored=dict(z,selection__bound_global=z['selection__bound_global']+1-sign)
        before=execute(old['source'],restored)
        assert min(restored.values())>0
        assert before['selection__Zglobal']==before['controller__lane_factor0']
        assert all(env[n]==before[n] for n,_,_,_ in old['source'] if n!='selection__Zglobal')
        q=env['selection__q'];F3=env['selection__F3']
        F1=16*env['range_H']+12-F3;F2=16*env['range_M']+10-F3;F0=q-1-F1-F2-F3
        fields=(F0,F1,F2,F3);r=sum(F*q**i for i,F in enumerate(fields))
        assert min(fields)>0 and max(fields)<q and sum(fields)==q-1
        assert tuple(F%16 for F in fields)==(1,4,2,8)
        assert r==env['selection__bs_packed'] and q<r-2 and env['selection__wn2']>r
        cases+=1
    return dict(both_sign_positive_bound_lifts=cases,
                scope='Structured positive off-zero tuples: joint sign, pretyping fields and full retained-register restoration are exact; native norms are not asserted one.')


def verify():
    return dict(status='PASS_GROUP_PROJECTIVE_JOINT_BOUND_UNIT',source=source_checks(),
                population=population_checks(),pretyping=pretyping_checks(),
                scope='Same strictly positive zeros on unchanged coordinates; no equality of unrestricted signed zero sets is asserted. One literal addition saved; ordinary input and full fixed-table theorem preserved.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
