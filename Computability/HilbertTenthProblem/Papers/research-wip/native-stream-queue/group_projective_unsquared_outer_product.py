"""Keep the integer unit product unsquared at the same arithmetic cost.

U*(1+sum_outer residual^2)-1 has exactly the certificate's integer zeros.
It is an explicit product polynomial, not a sum of squares.
"""
import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import random

import sympy as sp
import group_projective_strong_coefficient as parent

execute=parent.execute
residuals=parent.residuals
former_sos_source=parent.polynomial_source


def build(codes,alpha=24,beta=12,controller_mask=False,compute_length=False):
    old=parent.build(codes,alpha,beta,controller_mask,compute_length)
    return dict(old,polynomial_form='unsquared_unit_times_positive_outer_sum')


def polynomial_source(packet):
    assert packet['variant']=='six' and packet['strong_norm_coefficient']
    assert packet['comparisons'].count(('six_units',1))==1
    source=list(packet['source']);squares=[]
    for index,(left,right) in enumerate(packet['comparisons']):
        if (left,right)==('six_units',1):continue
        difference=f'outer_product_residual{index}'
        square=f'outer_product_square{index}'
        source += [(difference,'-',left,right),(square,'*',difference,difference)]
        squares.append(square)
    assert len(squares)>=1
    running=squares[0]
    for index,square in enumerate(squares[1:],1):
        next_register=f'outer_product_sum{index}'
        source.append((next_register,'+',running,square));running=next_register
    source += [('outer_product_positive','+',running,1),
               ('outer_product_product','*','six_units','outer_product_positive'),
               ('outer_product_output','-','outer_product_product',1)]
    return source,'outer_product_output'


def degree_top(packet,w):
    old_degree,unit_top,_,_=parent.degree_top(packet,w)
    nu=1+packet['compute_length'];m,L=packet['m'],packet['scale_exponent']
    P=(16*(packet['alpha']*w['x']+w['height_slack'])*sum(w[f'controller__edge_hat{i}'] for i in range(m))
       if packet['compute_length'] else w['P'])
    q=16*P**L;s=2*w['selection__odd_half'];k=w['selection__eta']+w['selection__zeta']
    c=k*s*q;strong_top=w['selection__i']**2*c**4
    strong_degree=4*nu*L+10
    degree=old_degree//2+2*strong_degree
    assert degree==nu*(27*L+m+15)+46
    return degree,unit_top*strong_top**2,dict(unit_degree=old_degree//2,
        strong_residual_degree=strong_degree,outer_sum_degree=2*strong_degree,
        unit_top=unit_top,strong_top=strong_top)


def degree_upper_bounds(packet):
    """Literal syntactic upper bounds; no equations or cancellation are used."""
    degrees={name:1 for name in packet['parameters']+packet['auxiliaries']}
    def degree(value):return degrees[value] if isinstance(value,str) else 0
    for name,op,a,b in packet['source']:
        degrees[name]=degree(a)+degree(b) if op=='*' else max(degree(a),degree(b))
    nu=1+packet['compute_length'];m,L=packet['m'],packet['scale_exponent']
    records=[]
    for a,b in packet['comparisons']:
        if (a,b)==('six_units',1):continue
        bound=max(degree(a),degree(b))
        if a=='selection__ic22':expected=4*nu*L+10;category='strong'
        elif a=='selection__bs_X_bound':expected=nu*(3*L+m+15)+1;category='native_bound'
        elif isinstance(a,str) and a.startswith('history__left'):expected=3;category='history'
        elif a=='selection__Zglobal':expected=nu;category='joint_bound'
        elif a=='controller__geometry_power':expected=2;category='repunit'
        else:
            assert (a,b)==(0,0) or (isinstance(a,str) and a.startswith('controller__flow')),(a,b)
            expected=2;category='flow'
        assert bound<=expected,(a,b,bound,expected)
        if category!='strong':assert expected<4*nu*L+10
        records.append(dict(comparison=[a,b],category=category,syntactic_degree_bound=bound,
                            proved_degree_bound=expected))
    return records


def source_checks():
    rng=random.Random(2872376);cases=0;records=[];example=None
    for codes in ((),((1,2),(3,4)),((1,2,3,4,5,6,7,8,1,2),)):
      for reuse in (False,True):
        if reuse and parent.build(codes)['m']<8:continue
        for comp in (False,True):
            packet=build(codes,controller_mask=reuse,compute_length=comp)
            source,out=polynomial_source(packet);sos,sos_out=former_sos_source(packet)
            assert len(source)==len(sos)==packet['operations']+3*packet['equations']-1
            counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
            assert counts==Counter('M' if op=='*' else 'A' for _,op,_,_ in sos)
            unit_index=packet['comparisons'].index(('six_units',1))
            for case in range(64):
                z={name:rng.randrange(1,9) if case<48 else rng.randrange(-4,5)
                   for name in packet['parameters']+packet['auxiliaries']}
                base=execute(packet['source'],z);env=execute(source,z);rr=residuals(packet,base)
                unit=rr[unit_index]+1;outer=sum(r*r for i,r in enumerate(rr) if i!=unit_index)
                assert env[out]==unit*(1+outer)-1
                assert env['outer_product_positive']==1+outer>=1
                before=execute(sos,z)
                assert before[sos_out]==sum(r*r for r in rr)
                assert (env[out]==0)==(before[sos_out]==0)==all(r==0 for r in rr)
                assert all(env[name]==base[name] for name,_,_,_ in packet['source'])
                cases+=1
            names=packet['parameters']+packet['auxiliaries']
            weights={name:1+i%3 for i,name in enumerate(names)};weights['selection__tau_gap']=1
            degree,top,parts=degree_top(packet,weights)
            t=sp.Symbol('t');values={name:sp.Poly(weights[name]*t+i+1,t) for i,name in enumerate(names)}
            cert=execute(packet['source'],values)
            rpolys=[sp.Poly(v,t) for v in residuals(packet,cert)]
            outer_polys=[r for i,r in enumerate(rpolys) if i!=unit_index]
            strong_index=packet['comparisons'].index(('selection__ic22','selection__R16'))
            strong=rpolys[strong_index];unit=sp.Poly(cert['six_units'],t)
            assert (unit.degree(),unit.LC())==(parts['unit_degree'],parts['unit_top'])
            assert (strong.degree(),strong.LC())==(parts['strong_residual_degree'],parts['strong_top'])
            assert all(r.is_zero or r.degree()<strong.degree() for i,r in enumerate(rpolys)
                       if i not in (unit_index,strong_index))
            # Exact lower-degree factor is expanded; the last product's degree
            # and leading coefficient then follow from two nonzero factors.
            positive=sp.Poly(1,t)+sum((r*r for r in outer_polys),sp.Poly(0,t))
            assert (positive.degree(),positive.LC())==(parts['outer_sum_degree'],parts['strong_top']**2)
            assert unit.degree()+positive.degree()==degree and int(unit.LC()*positive.LC())==top
            assert source[-2:]==[('outer_product_product','*','six_units','outer_product_positive'),
                                ('outer_product_output','-','outer_product_product',1)]
            encoded=abs(top).to_bytes((abs(top).bit_length()+7)//8,'big')
            old_degree=parent.degree_top(packet,weights)[0]
            records.append(dict(m=packet['m'],controller_mask=reuse,compute_length=comp,
                certificate_operations=packet['operations'],equations=packet['equations'],
                positive_witnesses=packet['positive_witnesses'],polynomial_operations=len(source),
                polynomial_M=counts['M'],polynomial_A=counts['A'],exact_degree=degree,
                former_SOS_operations=len(sos),former_SOS_degree=old_degree,
                outer_residual_degree_bounds=degree_upper_bounds(packet),
                weighted_leading_coefficient_sign=1 if top>0 else -1,
                weighted_leading_coefficient_sha256=hashlib.sha256(encoded).hexdigest()))
            if packet['m']==16 and reuse and comp:
                example=dict(packet,polynomial_source=source,polynomial_output=out)
                assert (len(source),degree,packet['positive_witnesses'])==(287,2376,43)
    return dict(records=records,source_example=example,full_numeric_product_and_SOS_cases=cases,
                positive_supplied_assignments=3*cases//4,signed_supplied_assignments=cases//4,
                exact_certificate_and_outer_factor_degree_audits=len(records),
                degree_method='Exact certificate and lower-degree positive factor polynomials; final source multiplication uses exact factor degree/leading-coefficient multiplication, without expanding the final product.')


def broad_outer_degree_checks():
    rng=random.Random(23761944);tables=[(),((1,2),),((1,2,3),)]
    tables += [tuple(tuple(rng.randrange(1,9) for _ in range(rng.randrange(1,17)))
                     for _ in range(rng.randrange(1,13))) for _ in range(32)]
    cases=0;hist={};largest=0
    for codes in tables:
      for comp in (False,True):
        packet=build(codes,alpha=4096,beta=12,compute_length=comp)
        degree_upper_bounds(packet);m=packet['m'];largest=max(largest,m)
        hist[m]=hist.get(m,0)+1;cases+=1
        if m>=8:
            packet=build(codes,alpha=4096,beta=12,controller_mask=True,compute_length=comp)
            degree_upper_bounds(packet);hist[m]+=1;cases+=1
    return dict(actual_DAG_outer_degree_bound_checks=cases,padded_edge_count_histogram=hist,
                largest_padded_edge_count=largest,
                scope='Syntactic degree bounds only; table size is not held fixed at the three exact symbolic audit examples.')


def integer_zero_checks():
    cases=0
    for length in range(5):
      for rs in product(range(-2,3),repeat=length):
       for unit in range(-4,5):
        factor=1+sum(r*r for r in rs)
        assert factor>=1
        assert (unit*factor-1==0)==(unit==1 and all(r==0 for r in rs))
        cases+=1
    return dict(integer_unit_and_outer_residual_fixtures=cases,
                scope='Finite supplement to the exact integer-factor proof; no sign restriction on the unsquared unit product.')


def verify():
    return dict(status='PASS_GROUP_PROJECTIVE_UNSQUARED_OUTER_PRODUCT',source=source_checks(),
                broad_degrees=broad_outer_degree_checks(),integer_equivalence=integer_zero_checks(),
                scope='Exactly the same integer zero set, hence the same positive ordinary-input relation. Output is a product polynomial, not an SOS; the former SOS remains a same-cost alternative.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
