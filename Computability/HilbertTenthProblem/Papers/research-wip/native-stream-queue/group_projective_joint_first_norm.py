"""Compose the joint bound with the positive first-norm coordinate.

Both rewrite orders have identical named DAGs and ordered comparisons.
Exact leading-term audits avoid expanding the final sum of squares.
"""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random

import sympy as sp
import group_projective_joint_bound as joint
import group_projective_first_norm_unit as first

execute=joint.execute
residuals=joint.residuals
polynomial_source=joint.polynomial_source


def build(codes,alpha=24,beta=12,variant='six',controller_mask=False,
          compute_length=False,merge_first=True):
    packet=first.rewrite(joint.build(codes,alpha,beta,variant,controller_mask,compute_length),merge_first)
    packet['composed_joint_and_first_norm']=True
    return packet


def degree_top(packet,w):
    m,L=packet['m'],packet['scale_exponent'];nu=1+packet['compute_length']
    Pstar=(16*(packet['alpha']*w['x']+w['height_slack'])*sum(w[f'controller__edge_hat{i}'] for i in range(m))
           if packet['compute_length'] else w['P'])
    q=16*Pstar**L;s=2*w['selection__odd_half'];k=w['selection__eta']+w['selection__zeta']
    a=w['selection__w']*s*q*q
    first_top=4*w['selection__w']*s*s*q**3*k*(w['selection__tau_gap']-k)
    first_degree=3*nu*L+5
    if packet['variant']=='four':
        c=w['selection__c'];ga=w['selection__ga']
        triple=(8*ga*a*a*(c+2*ga))*(w['selection__i']**2*w['selection__j']**2*c**6)*q
        triple_degree=5*nu*L+16
    else:
        c=k*s*q;r=16**4*w['H2']*Pstar**(3*L+m+15)
        triple=(8*w['selection__ga']*a*a*c)*(w['selection__i']**2*c**4*(2*r)**2)*q
        triple_degree=nu*(16*L+2*m+30)+19
    if packet['merge_first']:
        return 2*(first_degree+triple_degree),first_top*triple
    return 2*triple_degree,triple


def leading_records(separate,merged):
    """Exact residual polynomial degrees, then the exact last product's leading term."""
    t=sp.Symbol('t');names=separate['parameters']+separate['auxiliaries']
    weights={name:1+i%3 for i,name in enumerate(names)};weights['selection__tau_gap']=1
    values={name:sp.Poly(weights[name]*t+i+1,t) for i,name in enumerate(names)}
    env=execute(separate['source'],values)
    base={name:sp.Poly(value,t) for name,value in env.items()}
    assert ('four_units','*','unit_product','first_unit') in merged['source']
    def leading(value):
        return (None,0) if value.is_zero else (int(value.degree()),int(value.LC()))
    result={}
    for packet in (separate,merged):
        info=[]
        for left,right in packet['comparisons']:
            if left=='four_units':
                assert right==1
                d0,c0=leading(base['unit_product']);d1,c1=leading(base['first_unit'])
                assert d0>0 and d1>0
                # The source's final multiplication has no leading cancellation;
                # subtracting its constant comparison cannot change that term.
                info.append((d0+d1,c0*c1))
            else:
                a=base[left] if isinstance(left,str) else sp.Poly(left,t)
                b=base[right] if isinstance(right,str) else sp.Poly(right,t)
                info.append(leading(a-b))
        maximum=max(d for d,_ in info if d is not None)
        highest=sum(c*c for d,c in info if d==maximum)
        degree,top=degree_top(packet,weights)
        assert 2*maximum==degree and highest==top*top
        encoded=highest.to_bytes((highest.bit_length()+7)//8,'big')
        result[packet['merge_first']]=dict(exact_degree=degree,residual_degrees=[d for d,_ in info],
            weighted_highest_coefficient_bits=highest.bit_length(),
            weighted_highest_coefficient_sha256=hashlib.sha256(encoded).hexdigest())
    return result


def source_checks():
    rng=random.Random(162974);records=[];cases=half_integral=0;example=None
    tables=((),((1,2),(3,4)),((1,2,3,4,5,6,7,8,1,2),))
    for codes in tables:
      for variant in ('four','six'):
       for reuse in (False,True):
        if reuse and joint.parent.build(codes)['m']<8:continue
        for comp in (False,True):
            old=joint.build(codes,variant=variant,controller_mask=reuse,compute_length=comp)
            old_sos,old_out=polynomial_source(old)
            pairs={merge:build(codes,variant=variant,controller_mask=reuse,compute_length=comp,merge_first=merge)
                   for merge in (False,True)}
            for merge,packet in pairs.items():
                reverse=joint.rewrite(first.build(codes,variant=variant,controller_mask=reuse,
                                                 compute_length=comp,merge_first=merge))
                assert {name:(op,a,b) for name,op,a,b in packet['source']}=={name:(op,a,b) for name,op,a,b in reverse['source']}
                assert packet['comparisons']==reverse['comparisons'] and packet['auxiliaries']==reverse['auxiliaries']
                assert packet['operations']==reverse['operations']==old['operations']+merge
                assert packet['equations']==old['equations']-merge
                assert packet['positive_witnesses']==old['positive_witnesses']
                sos,out=polynomial_source(packet);rsos,rout=polynomial_source(reverse)
                assert len(sos)==len(old_sos)-2*merge
                fidx=old['comparisons'].index(('selection__L9','selection__R9'))
                uidx=old['comparisons'].index(('unit_product',1))
                for case in range(32):
                    z={name:rng.randrange(1,9) if case<24 else rng.randrange(-4,5)
                       for name in packet['parameters']+packet['auxiliaries']}
                    if case==0:z.update({f'controller__edge_hat{i}':1 for i in range(packet['m'])})
                    env=execute(sos,z);other=execute(rsos,z)
                    assert all(env[name]==other[name] for name,_,_,_ in packet['source'])
                    rr=residuals(packet,env)
                    assert rr==residuals(reverse,other) and env[out]==other[rout]==sum(r*r for r in rr)
                    restored={name:value for name,value in z.items() if name!='selection__tau_gap'}
                    restored['selection__tau']=env['first_root_base']+Fraction(z['selection__tau_gap']-1,2)
                    before=execute(old_sos,restored);br=residuals(old,before)
                    target=([(br[uidx]+1)*(1-4*br[fidx])-1 if i==uidx else r
                             for i,r in enumerate(br) if i!=fidx] if merge else
                            [-4*r if i==fidx else r for i,r in enumerate(br)])
                    assert rr==target
                    if case<24:assert env['selection__q']>=16 and restored['selection__tau']>0
                    half_integral+=restored['selection__tau'].denominator==2
                    cases+=1
            degrees=leading_records(pairs[False],pairs[True])
            for merge,packet in pairs.items():
                sos,_=polynomial_source(packet)
                counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in sos)
                m,h,p=packet['m'],packet['h'],packet['projection_additions'];flow=packet['flow']['operations']
                C=3*m+3*h+p+185+flow-3*min(h,3)-reuse
                e0=17 if variant=='four' else 15
                assert packet['operations']==C+merge
                assert packet['equations']==e0-comp-merge
                assert packet['positive_witnesses']==m+(33 if variant=='four' else 31)-comp
                assert len(sos)==C+(50 if variant=='four' else 44)-3*comp-2*merge
                records.append(dict(m=m,h=h,port_operations=p,flow_operations=flow,
                    variant=variant,controller_mask=reuse,compute_length=comp,merge_first=merge,
                    certificate_operations=packet['operations'],certificate_M=packet['multiplications'],
                    certificate_A=packet['additions_subtractions'],equations=packet['equations'],
                    positive_witnesses=packet['positive_witnesses'],polynomial_operations=len(sos),
                    polynomial_M=counts['M'],polynomial_A=counts['A'],**degrees[merge]))
                if m==16 and variant=='six' and reuse and comp and merge:example=packet
    assert example['operations']==259 and example['equations']==13 and example['positive_witnesses']==46
    assert len(polynomial_source(example)[0])==297
    return dict(records=records,source_example=example,commuting_named_DAGs=40,
                complete_numeric_graph_and_SOS_cases=cases,positive_supplied_cases=3*cases//4,
                signed_cases=cases//4,half_integral_off_zero_parent_roots=half_integral,
                exact_certificate_polynomial_evaluations=20,
                exact_residual_degree_and_leading_audits=40,
                degree_method='Separate certificate residuals evaluated exactly; merged last multiplication uses exact factor degrees/leading coefficients. No expanded SOS polynomial is needed.')


def verify():
    return dict(status='PASS_GROUP_PROJECTIVE_JOINT_FIRST_NORM',source=source_checks(),
                joint_positive_outer=joint.positive_outer_checks(),positive_root_maps=first.first_unit_checks(),
                scope='Complete positive fixed-table theorem by composition of commuting rewrites. Both scalar bounds remain restored through the joint bound. No numerical universal alphabet is instantiated.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
