"""Absorb the strong Pell comparison as a unit, lowering degree at equal cost."""
import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import random

import sympy as sp
import group_projective_shared_history_rhs as parent

execute=parent.execute
residuals=parent.residuals


def rewrite(old):
    assert old['shifted_X_quotient'] and old['variant']=='six'
    strong=('selection__ic22','selection__R16');unit=('six_units',1)
    assert old['comparisons'].count(strong)==old['comparisons'].count(unit)==1
    source=old['source']+[
        ('strong_unit_difference','-','selection__ic22','selection__R16'),
        ('strong_unit','+','strong_unit_difference',1),
        ('seven_units','*','six_units','strong_unit')]
    pairs=[('seven_units',1) if pair==unit else pair
           for pair in old['comparisons'] if pair!=strong]
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert counts=={'M':old['multiplications']+1,'A':old['additions_subtractions']+2}
    packet=dict(old,source=source,comparisons=pairs,operations=len(source),
                multiplications=counts['M'],additions_subtractions=counts['A'],
                equations=len(pairs),strong_unit_merged=True,
                unit_register='seven_units',unit_comparison_index=pairs.index(('seven_units',1)),
                removed_strong_comparison_index=old['comparisons'].index(strong))
    packet.pop('strong_comparison_index',None)
    return packet


def build(codes,alpha=24,beta=12,controller_mask=False,compute_length=False):
    return rewrite(parent.build(codes,alpha,beta,'shifted',controller_mask,compute_length))


def polynomial_source(packet):
    source=list(packet['source']);squares=[]
    for index,(a,b) in enumerate(packet['comparisons']):
        if (a,b)==('seven_units',1):continue
        name=f'strong_outer_residual{index}';square=f'strong_outer_square{index}'
        source += [(name,'-',a,b),(square,'*',name,name)];squares.append(square)
    total=squares[0]
    for index,square in enumerate(squares[1:],1):
        name=f'strong_outer_sum{index}';source.append((name,'+',total,square));total=name
    source += [('strong_outer_positive','+',total,1),
               ('strong_outer_product','*','seven_units','strong_outer_positive'),
               ('strong_outer_output','-','strong_outer_product',1)]
    return source,'strong_outer_output'


def degree_top(packet,w):
    _,_,old=parent.degree_top(packet,w)
    D=packet['alpha']*w['x']+w['height_slack'];B=16*D
    J=sum(w[f'controller__edge_hat{i}'] for i in range(packet['m']))
    diff=[sum((1 if label==2*i+1 else -1 if label==2*i+2 else 0)*w[f'controller__edge_hat{e}']
              for e,(_,_,label) in enumerate(packet['edges'])) for i in range(4)]
    moving=any(label for _,_,label in packet['edges'])
    outer_degree=3 if packet['compute_length'] or moving else 2
    if packet['compute_length']:
        history=[-B*D*(J+v) for v in diff];outer_top=sum(v*v for v in history)
    elif moving:
        history=[-B*D*v for v in diff];outer_top=sum(v*v for v in history)
    else:
        history=[B*(w[f'H{i}']+w[f'Zhat{2*i}']-w[f'Zhat{2*i+1}'])-D*w['P'] for i in range(4)]
        outer_top=sum(v*v for v in history)+(B*J)**2
    unit_degree=old['unit_degree']+old['strong_degree']
    unit_top=old['unit_top']*old['strong_top']
    degree=unit_degree+2*outer_degree
    m,L=packet['m'],packet['scale_exponent'];nu=1+packet['compute_length']
    assert degree==nu*(36*L+7*m+105)+38+2*outer_degree
    return degree,unit_top*outer_top,dict(parent_parts=old,unit_degree=unit_degree,unit_top=unit_top,
        outer_residual_degree=outer_degree,outer_factor_degree=2*outer_degree,
        history_highest_values=history,outer_top=outer_top,idle_only=not moving)


def unit_checks():
    residues=0
    for A,T,f in product(range(4),repeat=3):
        N=1+T*T-(A*A-1)*(f*f-1)
        assert N%4!=3
        residues+=1
    cases=0
    for A,T,f in product(range(-3,4),repeat=3):
      N=1+T*T-(A*A-1)*(f*f-1)
      for W in range(-2,3):
       for r,s in product(range(-1,2),repeat=2):
        actual=W*N*(1+r*r+s*s)-1
        assert (actual==0)==(W==1 and N==1 and r==s==0)
        cases+=1
    return dict(modulo_four_assignments=residues,integer_zero_equivalence_cases=cases,
                scope='Finite supplements to the unconditional modular exclusion and integer-unit proof.')


def source_checks():
    rng=random.Random(2793502);records=[];cases=0;example=None
    for codes in ((),((1,2),(3,4)),((1,2,3,4,5,6,7,8,1,2),)):
      for reuse in (False,True):
        if reuse and parent.build(codes)['m']<8:continue
        for comp in (False,True):
            old=parent.build(codes,controller_mask=reuse,compute_length=comp)
            packet=rewrite(old);source,out=polynomial_source(packet)
            prior,prior_out=parent.polynomial_source(old)
            assert packet['source'][:old['operations']]==old['source']
            assert packet['auxiliaries']==old['auxiliaries']
            assert len(source)==len(prior)
            counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
            assert counts==Counter('M' if op=='*' else 'A' for _,op,_,_ in prior)
            omitted=packet['removed_strong_comparison_index'];old_ui=old['unit_comparison_index']
            for case in range(64):
                z={n:rng.randrange(1,8) if case<48 else rng.randrange(-4,5)
                   for n in packet['parameters']+packet['auxiliaries']}
                env=execute(source,z);before=execute(prior,z);rr=residuals(old,before)
                A=before['selection__R12']+2
                T=z['selection__i']*before['selection__R10a']**2
                native_N=1+T*T-(A*A-1)*(z['selection__f']**2-1)
                assert env['strong_unit']==native_N==1+rr[omitted]
                assert native_N%4!=3
                unit=(rr[old_ui]+1)*native_N
                target=[unit-1 if i==old_ui else v for i,v in enumerate(rr) if i!=omitted]
                assert residuals(packet,env)==target
                outer=[v for i,v in enumerate(rr) if i not in (omitted,old_ui)]
                assert env[out]==unit*(1+sum(v*v for v in outer))-1
                assert (env[out]==0)==(before[prior_out]==0)==all(v==0 for v in rr)
                assert all(env[n]==before[n] for n,_,_,_ in old['source'])
                cases+=1
            names=packet['parameters']+packet['auxiliaries'];w={n:1+i%3 for i,n in enumerate(names)}
            w['selection__tau_gap']=1
            for i in range(packet['m']):w[f'controller__edge_hat{i}']=1<<i
            degree,top,parts=degree_top(packet,w);old_parts=parts['parent_parts']
            t=sp.Symbol('t');vals={n:sp.Poly(w[n]*t+i+1,t) for i,n in enumerate(names)}
            products={
                'unit_pair':('unit_pair','*','selection__R15','selection__P17'),
                'four_units':('four_units','*','unit_pair','first_unit'),
                'five_units':('five_units','*','four_units','index_unit'),
                'six_units':('six_units','*','five_units','linear_unit'),
                'seven_units':('seven_units','*','six_units','strong_unit')}
            rows={row[0]:row for row in packet['source']}
            assert all(rows[n]==row for n,row in products.items())
            assert not any(a in products or b in products for n,_,a,b in packet['source'] if n not in products)
            env=execute([row for row in packet['source'] if row[0] not in products],vals)
            for n,d in old_parts['unit_degrees'].items():
                assert (env[n].degree(),env[n].LC())==(d,old_parts['unit_tops'][n])
            assert (env['strong_unit'].degree(),env['strong_unit'].LC())==(old_parts['strong_degree'],old_parts['strong_top'])
            def value(v):return env[v] if isinstance(v,str) else v
            outer=[sp.Poly(value(a)-value(b),t) for a,b in packet['comparisons'] if (a,b)!=('seven_units',1)]
            d=parts['outer_residual_degree'];largest=max(v.degree() for v in outer)
            assert largest==d
            assert [v.nth(d) for v in outer[:4]]==parts['history_highest_values']
            positive=sp.Poly(1,t)+sum((v*v for v in outer),sp.Poly(0,t))
            assert (positive.degree(),positive.LC())==(2*d,parts['outer_top'])
            assert top==parts['unit_top']*positive.LC() and top!=0
            m,h,p=packet['m'],packet['h'],packet['projection_additions'];f=packet['flow']['operations']
            C=3*m+3*h+p+185+f-3*min(h,3)-reuse
            assert packet['operations']==C+1 and packet['equations']==8-comp
            assert packet['positive_witnesses']==m+27-comp and len(source)==C+24-3*comp
            encoded=abs(top).to_bytes((abs(top).bit_length()+7)//8,'big')
            records.append(dict(m=m,controller_mask=reuse,compute_length=comp,idle_only=parts['idle_only'],
                certificate_operations=packet['operations'],certificate_M=packet['multiplications'],
                certificate_A=packet['additions_subtractions'],equations=packet['equations'],
                positive_witnesses=packet['positive_witnesses'],polynomial_operations=len(source),
                polynomial_M=counts['M'],polynomial_A=counts['A'],exact_degree=degree,
                merged_unit_degree=parts['unit_degree'],outer_residual_degree=d,
                weighted_leading_coefficient_sign=1 if top>0 else -1,
                weighted_leading_coefficient_sha256=hashlib.sha256(encoded).hexdigest()))
            if m==16 and reuse and comp:
                example=dict(packet,polynomial_finalizer=source[packet['operations']:],polynomial_output=out)
                assert (len(source),degree,packet['positive_witnesses'])==(279,3502,42)
    return dict(records=records,source_example=example,full_signed_source_and_residual_cases=cases,
                positive_supplied_assignments=3*cases//4,signed_supplied_assignments=cases//4,
                exact_factor_and_outer_polynomial_degree_audits=len(records))


def verify():
    return dict(status='PASS_GROUP_PROJECTIVE_STRONG_UNIT_PRODUCT',source=source_checks(),units=unit_checks(),
                scope='Identical integer and strictly positive zero sets on unchanged supplied coordinates. Same operation count, smaller exact degree; complete fixed-table theorem and ordinary input unchanged.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
