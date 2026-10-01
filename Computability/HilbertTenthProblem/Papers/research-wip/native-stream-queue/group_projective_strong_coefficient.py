"""A retained strong equality reduces degree at unchanged arithmetic cost.

Only the six-field variant benefits. The auxiliary norm uses Delta(f²−1)
instead of (ic²)²; both paid quantities remain explicitly compared.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import sympy as sp
import group_projective_computed_checksum_field as parent
import group_projective_index_unit as index

execute=parent.execute
residuals=parent.residuals
polynomial_source=parent.polynomial_source


def rewrite(old):
    assert old['variant']=='six', 'This degree improvement is for the six-field variant.'
    strong=('selection__ic22','selection__R16')
    original=('selection__L17','*','selection__ic22','selection__aux_square_gap')
    assert strong in old['comparisons'] and original in old['source']
    source=[('selection__L17','*','selection__R16','selection__aux_square_gap')
            if row==original else row for row in old['source']]
    source=index.parent.sort_source(source,{'x',*old['auxiliaries']})
    assert Counter(row[1] for row in source)==Counter(row[1] for row in old['source'])
    return dict(old,source=source,strong_norm_coefficient=True,
                strong_comparison_index=old['comparisons'].index(strong),
                unit_comparison_index=old['comparisons'].index(('six_units',1)))


def build(codes,alpha=24,beta=12,controller_mask=False,compute_length=False):
    return rewrite(parent.build(codes,alpha,beta,'six',controller_mask,compute_length))


def degree_top(packet,w):
    _,_,degrees,tops=parent.degree_top(packet,w)
    m,L=packet['m'],packet['scale_exponent'];nu=1+packet['compute_length']
    P=(16*(packet['alpha']*w['x']+w['height_slack'])*sum(w[f'controller__edge_hat{i}'] for i in range(m))
       if packet['compute_length'] else w['P'])
    q=16*P**L;s=2*w['selection__odd_half'];k=w['selection__eta']+w['selection__zeta']
    a=w['selection__w']*s*q*q;c=k*s*q
    degrees['selection__P17']=6*nu*L+10
    tops['selection__P17']=a*a*w['selection__f']**2*c*c
    top=1
    for value in tops.values():top*=value
    degree=2*sum(degrees.values())
    assert degree==nu*(38*L+2*m+30)+52
    return degree,top,degrees,tops


def verify():
    rng=random.Random(2873368);records=[];cases=0;example=None
    for codes in ((),((1,2),(3,4)),((1,2,3,4,5,6,7,8,1,2),)):
      for reuse in (False,True):
        if reuse and parent.build(codes)['m']<8:continue
        for comp in (False,True):
            old=parent.build(codes,variant='six',controller_mask=reuse,compute_length=comp)
            packet=rewrite(old);sos,out=polynomial_source(packet);old_sos,old_out=polynomial_source(old)
            assert len(sos)==len(old_sos)
            for case in range(64):
                z={n:rng.randrange(1,9) if case<48 else rng.randrange(-4,5)
                   for n in packet['parameters']+packet['auxiliaries']}
                before=execute(old_sos,z);env=execute(sos,z)
                rr=residuals(old,before);delta=rr[packet['strong_comparison_index']]
                gap=before['selection__aux_square_gap']
                other=(before['first_unit']*before['selection__R15']*
                       before['index_unit']*before['linear_unit'])
                target=list(rr);target[packet['unit_comparison_index']]-=other*delta*gap
                assert env['selection__P17']==before['selection__P17']-delta*gap
                assert residuals(packet,env)==target
                assert env[out]==sum(v*v for v in target)
                assert env[out]-before[old_out]==sum(v*v for v in target)-sum(v*v for v in rr)
                cases+=1
            names=packet['parameters']+packet['auxiliaries']
            weights={n:1+i%3 for i,n in enumerate(names)};weights['selection__tau_gap']=1
            degree,top,uds,tops=degree_top(packet,weights)
            t=sp.Symbol('t');z={n:sp.Poly(weights[n]*t+i+1,t) for i,n in enumerate(names)}
            env=execute(packet['source'],z)
            for n in uds:assert (env[n].degree(),env[n].LC())==(uds[n],tops[n]),n
            polys=[sp.Poly(v,t) for v in residuals(packet,env)]
            maximum=max(v.degree() for v in polys)
            assert sum(v.degree()==maximum for v in polys)==1
            highest=int(sum(v.LC()**2 for v in polys if v.degree()==maximum))
            assert 2*maximum==degree and highest==top*top
            counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in sos)
            encoded=highest.to_bytes((highest.bit_length()+7)//8,'big')
            records.append(dict(m=packet['m'],controller_mask=reuse,compute_length=comp,
                certificate_operations=packet['operations'],certificate_M=packet['multiplications'],
                certificate_A=packet['additions_subtractions'],equations=packet['equations'],
                positive_witnesses=packet['positive_witnesses'],polynomial_operations=len(sos),
                polynomial_M=counts['M'],polynomial_A=counts['A'],exact_degree=degree,
                residual_degrees=[int(v.degree()) if not v.is_zero else None for v in polys],
                weighted_highest_coefficient_sha256=hashlib.sha256(encoded).hexdigest()))
            if packet['m']==16 and reuse and comp:
                example=packet
                assert (len(sos),degree,packet['positive_witnesses'])==(287,3368,43)
    assert len(records)==10 and cases==640
    return dict(status='PASS_GROUP_PROJECTIVE_STRONG_COEFFICIENT',records=records,
                source_example=example,complete_residual_SOS_transformation_checks=cases,
                signed_assignments=cases//4,exact_degree_audits=len(records),
                scope='Exact same positive zero set under the unchanged strong comparison. Arithmetic, equations, witnesses and ordinary input are unchanged; six-field degree drops by eight.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
