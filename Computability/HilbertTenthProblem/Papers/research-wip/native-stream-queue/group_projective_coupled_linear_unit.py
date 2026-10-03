"""Couple the auxiliary linear unit to the native first-index difference.

Both checksum branches normalize to the same complete outer certificate.
The normalization is conditional on the unit signs, not a graph bijection.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import sympy as sp
import group_projective_index_unit as index
import group_projective_joint_first_norm as joint

execute=joint.execute
residuals=joint.residuals
polynomial_source=joint.polynomial_source


def rewrite(old):
    assert old['merged_index']
    removed={'selection__r1','selection__tr1','selection__H17'}
    linear_pair=('selection__H17','selection__aux_u_rhs')
    assert linear_pair in old['comparisons'] and ('five_units',1) in old['comparisons']
    rows={row[0]:row for row in old['source']}
    r=old['native_r_register']
    assert rows['selection__r1']==('selection__r1','+',r,1)
    assert rows['selection__tr1']==('selection__tr1','+','selection__r1',r)
    assert rows['selection__H17']==('selection__H17','-','selection__jc','selection__tr1')
    assert rows['selection__H2']==('selection__H2','*','selection__H17','selection__H17')
    consumers={name:set() for name in removed}
    for name,_,a,b in old['source']:
        for operand in (a,b):
            if operand in consumers:consumers[operand].add(name)
    assert consumers=={'selection__r1':{'selection__tr1'},
                       'selection__tr1':{'selection__H17'},
                       'selection__H17':{'selection__H2'}}
    source=[(name,op,'selection__aux_u_rhs','selection__aux_u_rhs')
            if name=='selection__H2' else (name,op,a,b)
            for name,op,a,b in old['source'] if name not in removed]
    source += [('twice_index_difference','+','selection__R11','selection__R11'),
               ('linear_difference','-','selection__aux_u_rhs','selection__jc'),
               ('linear_unit','+','linear_difference','twice_index_difference'),
               ('six_units','*','five_units','linear_unit')]
    pairs=[('six_units',1) if pair==('five_units',1) else pair
           for pair in old['comparisons'] if pair!=linear_pair]
    source=index.parent.sort_source(source,{'x',*old['auxiliaries']})
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert counts=={'M':old['multiplications']+1,'A':old['additions_subtractions']}
    packet=dict(old,source=source,comparisons=pairs,operations=len(source),equations=len(pairs),
                multiplications=counts['M'],additions_subtractions=counts['A'],
                coupled_linear=True,deleted_linear_comparison=old['comparisons'].index(linear_pair),
                old_unit_comparison=old['comparisons'].index(('five_units',1)),
                deleted_gate_consumers={k:sorted(v) for k,v in consumers.items()})
    assert len(source)==old['operations']+1 and len(pairs)==old['equations']-1
    return packet


def build(codes,alpha=24,beta=12,variant='six',controller_mask=False,compute_length=False):
    return rewrite(index.rewrite(joint.build(codes,alpha,beta,variant,controller_mask,compute_length,True)))


def normalize(packet,z,epsilon):
    assert epsilon in (-1,1)
    delta=1-epsilon
    restored=dict(z)
    restored['selection__F0']-=delta
    restored['selection__bound_beta']+=delta
    if packet['variant']=='four':restored['selection__r']-=delta
    return restored


def degree_top(packet,w):
    m,L=packet['m'],packet['scale_exponent'];nu=1+packet['compute_length']
    P=(16*(packet['alpha']*w['x']+w['height_slack'])*sum(w[f'controller__edge_hat{i}'] for i in range(m))
       if packet['compute_length'] else w['P'])
    q=16*P**L;s=2*w['selection__odd_half'];k=w['selection__eta']+w['selection__zeta']
    a=w['selection__w']*s*q*q
    n0=4*w['selection__w']*s*s*q**3*k*(w['selection__tau_gap']-k)
    linear=-2*w['selection__h']*w['selection__w']*s*q*q
    if packet['variant']=='four':
        c=w['selection__c'];ga=w['selection__ga']
        n1=8*ga*a*a*(c+2*ga)
        n3=w['selection__i']**2*c**4*w['selection__o']**2*w['selection__f']**2
        nk=linear//2
        degree=24*nu*L+54
        unit_degrees={'first_unit':3*nu*L+5,'selection__R15':4*nu*L+6,
                      'selection__P17':10,'selection__bs_q':nu*L,
                      'index_unit':2*nu*L+3,'linear_unit':2*nu*L+3}
    else:
        c=k*s*q;n1=8*w['selection__ga']*a*a*c
        n3=w['selection__i']**2*c**6
        nk=-16**4*w['H2']*P**(3*L+m+15)
        degree=nu*(40*L+2*m+30)+60
        unit_degrees={'first_unit':3*nu*L+5,'selection__R15':5*nu*L+7,
                      'selection__P17':6*nu*L+14,'selection__bs_q':nu*L,
                      'index_unit':nu*(3*L+m+15)+1,'linear_unit':2*nu*L+3}
    tops={'first_unit':n0,'selection__R15':n1,'selection__P17':n3,
          'selection__bs_q':q,'index_unit':nk,'linear_unit':linear}
    assert 2*sum(unit_degrees.values())==degree
    top=1
    for value in tops.values():top*=value
    return degree,top,unit_degrees,tops


def source_checks():
    rng=random.Random(2943544);records=[];cases=0;example=None
    tables=((),((1,2),(3,4)),((1,2,3,4,5,6,7,8,1,2),))
    for codes in tables:
      for variant in ('four','six'):
       for reuse in (False,True):
        if reuse and joint.build(codes)['m']<8:continue
        for comp in (False,True):
            old=index.rewrite(joint.build(codes,variant=variant,controller_mask=reuse,compute_length=comp))
            packet=rewrite(old);sos,out=polynomial_source(packet)
            old_sos,old_out=polynomial_source(old)
            assert len(sos)==len(old_sos)-2 and packet['auxiliaries']==old['auxiliaries']
            i=packet['old_unit_comparison'];j=packet['deleted_linear_comparison']
            changed={'selection__H2','selection__aux_square_gap','selection__L17','selection__P17',
                     'unit_pair','unit_product','four_units','five_units'}
            for case in range(64):
                z={name:rng.randrange(1,9) if case<48 else rng.randrange(-4,5)
                   for name in packet['parameters']+packet['auxiliaries']}
                env=execute(sos,z);before=execute(old_sos,z);rr=residuals(old,before)
                U=before['selection__H17'];V=before['selection__aux_u_rhs']
                n3=before['selection__P17']+before['selection__ic22']*(V*V-U*U)
                linear=2*before['index_unit']-1-rr[j]
                merged=(before['first_unit']*before['selection__R15']*n3*
                        before['selection__bs_q']*before['index_unit']*linear-1)
                target=[merged if k==i else r for k,r in enumerate(rr) if k!=j]
                assert env['linear_unit']==linear and env['selection__P17']==n3
                assert residuals(packet,env)==target and env[out]==sum(r*r for r in target)
                assert all(env[name]==before[name] for name,_,_,_ in packet['source']
                           if name in before and name not in changed)
                cases+=1
            names=packet['parameters']+packet['auxiliaries']
            weights={name:1+i%3 for i,name in enumerate(names)};weights['selection__tau_gap']=1
            degree,top,uds,tops=degree_top(packet,weights)
            t=sp.Symbol('t');values={name:sp.Poly(weights[name]*t+i+1,t) for i,name in enumerate(names)}
            env=execute(packet['source'],values)
            for name in uds:
                assert (env[name].degree(),env[name].LC())==(uds[name],tops[name]),name
            polys=[sp.Poly(v,t) for v in residuals(packet,env)]
            maximum=max(v.degree() for v in polys)
            highest=int(sum(v.LC()**2 for v in polys if v.degree()==maximum))
            assert degree==2*maximum and highest==top*top
            counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in sos)
            m,h,p=packet['m'],packet['h'],packet['projection_additions'];f=packet['flow']['operations']
            C=3*m+3*h+p+185+f-3*min(h,3)-reuse
            assert packet['operations']==C+4
            assert packet['equations']==(14 if variant=='four' else 12)-comp
            assert packet['positive_witnesses']==m+(33 if variant=='four' else 31)-comp
            assert len(sos)==C+(45 if variant=='four' else 39)-3*comp
            encoded=highest.to_bytes((highest.bit_length()+7)//8,'big')
            records.append(dict(m=m,variant=variant,controller_mask=reuse,compute_length=comp,
                certificate_operations=packet['operations'],certificate_M=packet['multiplications'],
                certificate_A=packet['additions_subtractions'],equations=packet['equations'],
                positive_witnesses=packet['positive_witnesses'],polynomial_operations=len(sos),
                polynomial_M=counts['M'],polynomial_A=counts['A'],exact_degree=degree,
                residual_degrees=[int(v.degree()) if not v.is_zero else None for v in polys],
                weighted_highest_coefficient_sha256=hashlib.sha256(encoded).hexdigest()))
            if m==16 and variant=='six' and reuse and comp:example=packet
    assert example['operations']==262 and example['equations']==11 and example['positive_witnesses']==46
    assert len(polynomial_source(example)[0])==294
    return dict(records=records,source_example=example,complete_source_residual_SOS_identities=cases,
                positive_supplied_assignments=3*cases//4,signed_supplied_assignments=cases//4,
                exact_residual_and_six_factor_degree_audits=len(records))


def restoration_checks():
    rng=random.Random(216326);positive=signed=0;branches={-1:0,1:0}
    codes=((1,2),(3,4))
    for variant in ('four','six'):
      for reuse in (False,True):
       for comp in (False,True):
        old=index.rewrite(joint.build(codes,variant=variant,controller_mask=reuse,compute_length=comp))
        packet=rewrite(old);sos,out=polynomial_source(packet);old_sos,old_out=polynomial_source(old)
        linear_index=old['comparisons'].index(('selection__H17','selection__aux_u_rhs'))
        for epsilon in (-1,1):
         for case in range(32):
            z={name:rng.randrange(1,4) for name in packet['parameters']+packet['auxiliaries']}
            if not comp:z['P']=8
            if case>=24:
                for name in ('selection__tau_gap','selection__ga','selection__i','selection__y_aux'):
                    z[name]=-z[name]
            env=execute(packet['source'],z)
            z['selection__F0']=env['selection__q']-epsilon-z['selection__F1']-z['selection__F2']-env['selection__F3']
            assert z['selection__F0']>2
            env=execute(packet['source'],z);r=env['selection__bs_packed']
            if variant=='four':z['selection__r']=r
            z['selection__zeta']=r+env['selection__hpm1']+epsilon-z['selection__eta']
            assert z['selection__zeta']>0
            env=execute(packet['source'],z)
            if variant=='four':z['selection__c']=env['selection__R10a']
            env=execute(packet['source'],z);c=env['selection__R10a']
            z['selection__f']=1
            z['selection__o']=(z['selection__j']+1)*c-2*env['selection__R11']+1
            assert z['selection__o']>0
            env=execute(sos,z)
            assert (env['selection__bs_q'],env['index_unit'],env['linear_unit'])==(epsilon,epsilon,1)
            restored=normalize(packet,z,epsilon);before=execute(old_sos,restored)
            rr=residuals(old,before)
            assert rr[linear_index]==0
            assert residuals(packet,env)==[r for i,r in enumerate(rr) if i!=linear_index]
            assert env[out]==before[old_out]
            assert before['selection__H17']==env['selection__aux_u_rhs']
            assert before['selection__bs_q']==before['index_unit']==1
            for name,_,_,_ in packet['source']:
                if not name.startswith('selection__') and name not in ('unit_pair','unit_product','four_units','five_units','index_unit',
                        'twice_index_difference','linear_difference','linear_unit','six_units'):
                    assert env[name]==before[name],name
            if case<24:
                assert min(z.values())>0 and min(restored.values())>0;positive+=1
            else:signed+=1
            branches[epsilon]+=1
    return dict(positive_conditional_restorations=positive,signed_conditional_restorations=signed,
                cases_by_index_sign=branches,
                scope='Structured off-zero identities impose only Q=Nk=epsilon,L=1 and the native packing/definitions; Pell equations are not claimed to hold.')


def sign_checks():
    residues=0
    for f0 in range(16):
      for sign in (-1,1):
        if (f0+4+2+8+sign)%16==0:
            assert f0==(1 if sign==1 else 3);residues+=1
    rank_bounds=0
    for q in range(16,80):
        r=q**3+q*q+q+1;Y=q;X=r+1;E=X*Y
        assert E>2*r+3 and Y*(r-1)>2*(2*r+3)
        for epsilon in (-1,1):
          for linear in (-1,1):
            target=2*(r+epsilon)-linear
            assert 0<target<E and 2*r-3<=target<=2*r+3
            rank_bounds+=1
    return dict(padding_residue_cases=residues,weak_signed_target_bound_cases=rank_bounds,
                scope='Finite arithmetic checks supplement the parametric sign and Pell-index proof.')


def verify():
    return dict(status='PASS_GROUP_PROJECTIVE_COUPLED_LINEAR_UNIT',source=source_checks(),
                normalization=restoration_checks(),signs=sign_checks(),
                scope='Complete ordinary-input equivalence by conditional positive normalization. The negative index/checksum branch changes only native F0,r,bound_beta; this is not a positive-tuple bijection.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
