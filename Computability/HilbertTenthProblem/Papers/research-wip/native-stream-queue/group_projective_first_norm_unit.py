"""A positive first-root gap joins the native unit product, saving two SOS adds."""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random

import sympy as sp
import group_projective_padded_program_margin as parent

execute=parent.execute
residuals=parent.residuals
polynomial_source=parent.polynomial_source
sort_source=parent.parent.parent.range_parent.sort_source


def build(codes,alpha=24,beta=12,variant='six',controller_mask=False,
          compute_length=False,merge_first=True):
    old=parent.build(codes,alpha,beta,variant,controller_mask,compute_length)
    return rewrite(old,merge_first)


def rewrite(old,merge_first=True):
    """Apply the local native rewrite to a compatible complete packet."""
    deleted={
        'selection__tauplus1':('+','selection__tau',1),
        'selection__R9':('*','selection__tau','selection__tauplus1'),
        'selection__UM2':('*','selection__UM','selection__UM'),
        'selection__scaled_norm_coefficient':('+','selection__UM2','selection__wn2'),
        'selection__ratio_product2':('*','selection__ksn2','selection__ksn2'),
        'selection__L9':('*','selection__scaled_norm_coefficient','selection__ratio_product2')}
    nodes={name:(op,left,right) for name,op,left,right in old['source']}
    assert all(nodes[name]==row for name,row in deleted.items())
    source=[row for row in old['source'] if row[0] not in deleted]
    source += [
        ('first_gap_square','*','selection__tau_gap','selection__tau_gap'),
        ('first_root_base','*','selection__UM','selection__ksn2'),
        ('first_signed_gap','-','selection__tau_gap','selection__R10b'),
        ('first_cross','*','first_root_base','first_signed_gap'),
        ('first_four_cross','*',4,'first_cross'),
        ('first_unit','+','first_gap_square','first_four_cross')]
    first_pair=('selection__L9','selection__R9')
    assert first_pair in old['comparisons']
    if merge_first:
        source.append(('four_units','*','unit_product','first_unit'))
        pairs=[('four_units',1) if pair==('unit_product',1) else pair
               for pair in old['comparisons'] if pair!=first_pair]
    else:
        pairs=[('first_unit',1) if pair==first_pair else pair for pair in old['comparisons']]
    aux=['selection__tau_gap' if name=='selection__tau' else name for name in old['auxiliaries']]
    source=sort_source(source,{'x',*aux})
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert counts=={'M':old['multiplications']+merge_first,'A':old['additions_subtractions']}
    packet=dict(old)
    packet.update(source=source,comparisons=pairs,auxiliaries=aux,operations=len(source),
                  multiplications=counts['M'],additions_subtractions=counts['A'],
                  equations=len(pairs),merge_first=merge_first,
                  first_parent_comparison=old['comparisons'].index(first_pair),
                  unit_parent_comparison=old['comparisons'].index(('unit_product',1)))
    assert len(source)==old['operations']+merge_first
    assert len(pairs)==old['equations']-merge_first
    return packet


def degree_top(packet,weights):
    m,L=packet['m'],packet['scale_exponent']
    if packet['compute_length']:
        Dtop=packet['alpha']*weights['x']+weights['height_slack']
        Jtop=sum(weights[f'controller__edge_hat{i}'] for i in range(m))
        Ptop=8*Dtop*Jtop;nu=2
    else:
        Ptop=weights['P'];nu=1
    qtop=16*Ptop**L
    w=weights['selection__w'];s=2*weights['selection__odd_half']
    k=weights['selection__eta']+weights['selection__zeta']
    a=w*s*qtop**2
    first_top=4*w*s*s*qtop**3*k*(weights['selection__tau_gap']-k)
    first_degree=3*nu*L+5
    if packet['variant']=='four':
        c=weights['selection__c'];ga=weights['selection__ga']
        triple_top=(8*ga*a*a*(c+2*ga))*(weights['selection__i']**2*weights['selection__j']**2*c**6)*qtop
        triple_degree=5*nu*L+16
    else:
        _,triple_top=parent.parent.degree_top(packet,weights)
        triple_degree=nu*(16*L+2*m+30)+19
    if packet['merge_first']:
        return 2*(first_degree+triple_degree),first_top*triple_top
    return 2*triple_degree,triple_top


def source_checks():
    rng=random.Random(420218);records=[];cases=positive=signed=half_integral=0
    tables=((),((1,2),(3,4)),tuple((i,) for i in range(1,9)))
    for codes in tables:
      for variant in ('four','six'):
       for reuse in (False,True):
        if reuse and parent.build(codes)['m']<8:continue
        for comp in (False,True):
         for merge in (False,True):
            old=parent.build(codes,variant=variant,controller_mask=reuse,compute_length=comp)
            packet=build(codes,variant=variant,controller_mask=reuse,compute_length=comp,merge_first=merge)
            sos,out=polynomial_source(packet)
            old_sos,old_out=polynomial_source(old)
            assert len(sos)==len(old_sos)-2*merge
            a,b=packet['first_parent_comparison'],packet['unit_parent_comparison']
            for case in range(32):
                z={name:rng.randrange(1,9) if case<24 else rng.randrange(-4,5)
                   for name in packet['parameters']+packet['auxiliaries']}
                if case==0:
                    z.update({f'controller__edge_hat{i}':1 for i in range(packet['m'])})
                env=execute(sos,z)
                restored={name:value for name,value in z.items() if name!='selection__tau_gap'}
                restored['selection__tau']=env['first_root_base']+Fraction(z['selection__tau_gap']-1,2)
                before=execute(old_sos,restored)
                rr=residuals(old,before)
                assert env['first_unit']==1-4*rr[a]
                if merge:
                    target=[(rr[b]+1)*(1-4*rr[a])-1 if i==b else r
                            for i,r in enumerate(rr) if i!=a]
                else:
                    target=[-4*r if i==a else r for i,r in enumerate(rr)]
                assert residuals(packet,env)==target
                assert env[out]==sum(value*value for value in target)
                if not merge:
                    assert env[out]==before[old_out]+15*rr[a]*rr[a]
                old_names={row[0] for row in old['source']}
                assert all(env[name]==before[name] for name,_,_,_ in packet['source'] if name in old_names)
                if case<24:
                    assert env['selection__q']>=16 and env['first_root_base']>0
                    assert restored['selection__tau']>0
                    positive+=1
                else:signed+=1
                half_integral+=restored['selection__tau'].denominator==2
                cases+=1
            counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in sos)
            names=packet['parameters']+packet['auxiliaries']
            weights={name:1+i%3 for i,name in enumerate(names)}
            weights['selection__tau_gap']=1
            degree,top=degree_top(packet,weights)
            # Every configuration gets literal degree/leading-form verification.
            t=sp.Symbol('t')
            z={name:sp.Poly(weights[name]*t+i+1,t) for i,name in enumerate(names)}
            env=execute(packet['source'],z)
            weighted_residuals=[sp.Poly(value,t) for value in residuals(packet,env)]
            max_degree=max(value.degree() for value in weighted_residuals)
            leading_square_sum=sum(value.LC()**2 for value in weighted_residuals
                                   if value.degree()==max_degree)
            # Over the reals, highest squares cannot cancel. This is an exact
            # SOS degree audit without expanding its redundant final squares.
            assert 2*max_degree==degree,(packet['m'],variant,reuse,comp,merge,2*max_degree,degree)
            assert leading_square_sum==top**2
            top_bytes=(top**2).to_bytes(((top**2).bit_length()+7)//8,'big')
            records.append(dict(m=packet['m'],variant=variant,controller_mask=reuse,
                                compute_length=comp,merge_first=merge,
                                certificate_operations=packet['operations'],equations=packet['equations'],
                                positive_witnesses=packet['positive_witnesses'],polynomial_operations=len(sos),
                                polynomial_M=counts['M'],polynomial_A=counts['A'],exact_degree=degree,
                                weighted_leading_coefficient_sha256=hashlib.sha256(top_bytes).hexdigest()))
    example=build(((1,2),(3,4)),variant='six',controller_mask=True,compute_length=True)
    return dict(records=records,source_example=example,full_source_and_SOS_identities=cases,
                positive_supplied_assignments=positive,signed_supplied_assignments=signed,
                half_integral_off_zero_parent_root_cases=half_integral)


def first_unit_checks():
    residue_cases=pell_cases=0
    for g in range(4):
      for V in range(4):
       for k in range(4):
        assert (g*g+4*V*k*(g-k))%4 != 3
        residue_cases+=1
    for V in range(1,33):
        P=2*V+1;root,k=1,0
        for _ in range(12):
            root,k=P*root+(P*P-1)*k,root+P*k
            tau=(root-1)//2;g=root-2*V*k
            assert root%2==1 and min(tau,k,g)>0
            assert tau*(tau+1)==V*(V+1)*k*k
            assert g*g+4*V*k*(g-k)==1
            assert tau==V*k+(g-1)//2
            pell_cases+=1
    return dict(mod4_residue_cases=residue_cases,positive_component_bijection_cases=pell_cases,
                scope='Component identities supplement the parametric full-source positive bijection.')


def verify():
    return dict(status='PASS_GROUP_PROJECTIVE_FIRST_NORM_UNIT',source=source_checks(),
                unit_and_coordinate_checks=first_unit_checks(),
                merged_saving=dict(certificate_multiplications_added=1,equations_removed=1,
                                   polynomial_additions_saved=2),
                scope='Complete positive equivalence with the padded fixed-table parent, by a first-root coordinate bijection. '
                      'Both ratio slacks and the strong auxiliary comparison remain unchanged; no numerical universal alphabet is instantiated.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
