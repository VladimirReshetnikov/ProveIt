#!/usr/bin/env python3
"""Auxiliary-gap circuits and normalized-root elimination, using stdlib only.

The gap coordinate e replaces y by V+e.  The scripts and exact leading-form
certificates audit the algebra; the existence equivalences are proved in
GAP_AUXILIARY_PROOF.md, rather than inferred from the finite diagnostics.
"""
from __future__ import annotations
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random

from build_improved import build as ordinary_build
from build_improved import require, ledger, evaluate, line_degrees, formula as ordinary_formula
from build_fourteen import build as fourteen_build

HERE=Path(__file__).resolve().parent
GAP='auxiliary_gap'
SIGNED15={'h','f','auxiliary_quotient','tau_root',GAP,'gamma'}
SIGNED14=SIGNED15-{'f'}


def finish(packet):
    packet['ledger']=ledger(packet)
    packet['source_sha256']=hashlib.sha256(json.dumps(packet['source'],separators=(',',':')).encode()).hexdigest()
    return packet


def make_gap15(packet):
    rows=[]
    for row in packet['source']:
        if row[0]=='aux_y2':
            continue
        rows.append(row[:])
        if row[0]=='aux_u_rhs':
            rows += [['gap_y','+','aux_u_rhs',GAP],['aux_y2','*','gap_y','gap_y']]
    out=dict(packet,source=rows,
             witnesses=[GAP if n=='y_aux' else n for n in packet['witnesses']],
             coordinate_change='y_aux=V+auxiliary_gap, V=c*(T*f-1)-R*f^2',
             domain_proof='GAP_AUXILIARY_PROOF.md: canonical positive gap and expanded signed-domain equivalence.')
    if 'factors' in out:
        out.update(name='ordinary_gap70',exact_degree=93,
                   factor_exact_degrees=[22,18,22,7,2,22],
                   leading_form='-16*Q0^52*h*gamma*i^2*(eta+zeta)^8*w^7*s^15*T*f^3*e*(w*(Q0-F-alpha)-z*Q0), Q0=Bm1*Jrep')
        out['leading_monomial_certificate']={
            'exponents':{'Jrep':53,'h':1,'gamma':1,'i':2,'eta':8,'w':7,'s':15,'auxiliary_quotient':1,'f':3,GAP:1,'transport_quotient':1},
            'coefficient':'16*Bm1^53','nonzero_condition':'Bm1 > 0'}
    elif 'comparisons' in out:
        out.update(name='ordinary_gap_system61',exact_maximum_degree=22,
                   residual_exact_degrees=[22,18,22,7,2,22])
    else:
        out.update(name='ordinary_gap_sos78',exact_degree=44,
                   leading_form='(w^2*k0^2*s^4*Q0^14)^2+(2*e*k0*w^2*s^3*Q0^11*T*f^3)^2+(i^2*k0^4*s^4*Q0^12)^2, Q0=Bm1*Jrep, k0=eta+zeta')
    finish(out)
    require(out['ledger']['operations']==packet['ledger']['operations']+1,'gap insertion count')
    return out


def lift(packet,signed,degree=None,factor_degrees=None,residual_degrees=None):
    rows=[]; witnesses=[]
    guarded=[n for n in packet['witnesses'] if n not in signed]
    for n in packet['witnesses']:
        if n in signed:
            witnesses.append(n)
            continue
        u,v,t=[n+s for s in ('_u','_v','_t')]; witnesses += [u,v,t]
        rows += [[n+'_u2','*',u,u],[n+'_v2','*',v,v],
                 [n+'_t1','+',t,1],[n+'_tt1','*',t,n+'_t1'],
                 [n+'_uv2','+',n+'_u2',n+'_v2'],[n+'_sum','+',n+'_uv2',n+'_tt1'],
                 [n,'+',n+'_sum',1]]
    rows+=packet['source']
    count=len(witnesses)
    out=dict(packet,name=packet['name']+'_over_Z'+str(count),source=rows,
             witnesses=witnesses,witness_domain='all integers',
             positive_guarded_coordinates=guarded,
             unrestricted_original_coordinates=sorted(signed),
             positive_substitution='x=1+x_u^2+x_v^2+x_t*(x_t+1)')
    out.pop('leading_monomial_certificate',None)
    positive_form=out.pop('leading_form',None)
    if positive_form:
        out['weighted_leading_form_before_substitution']=positive_form
        if packet['name']=='ordinary_gap_sos78':
            out['weighted_leading_form_before_substitution']='(w^2*k0^2*s^4*Q0^14)^2+(i^2*k0^4*s^4*Q0^12)^2, Q0=Bm1*Jrep, k0=eta+zeta'
        out['leading_substitution']='In the weighted leading form, substitute x_u^2+x_v^2+x_t^2 for each guarded x.'
    if degree is not None: out['exact_degree']=degree
    if factor_degrees is not None: out['factor_exact_degrees']=factor_degrees
    if residual_degrees is not None:
        out.update(residual_exact_degrees=residual_degrees,exact_maximum_degree=max(residual_degrees))
    require(len(guarded)==9 and count in (32,33),'lift dimension')
    finish(out)
    require(out['ledger']['operations']==packet['ledger']['operations']+63,'lift count')
    return out


ROOT_COMMON=[
 ['gg_ic2','*','i','c2'],['gg_dminus1','*','gg_ic2','aux_coefficient_root'],
 ['gg_d','+','gg_dminus1',1],['gg_Rd','*','r_lhs','gg_d'],
 ['gg_b','+','R10a','gg_Rd'],['gg_v','*','R10a','auxiliary_quotient'],
 ['gg_v2','*','gg_v','gg_v'],['gg_p','*','gg_d','gg_v2'],
 ['gg_S','-','R16',1],['gg_Se','*','gg_S',GAP],
 ['gg_r','+','gg_b','gg_Se'],['gg_r2','*','gg_r','gg_r'],
 ['gg_See','*','gg_Se',GAP],['gg_QSee','*','R16','gg_See'],
 ['gg_sum','+','gg_p','gg_r2'],['gg_Aplus1','-','gg_sum','gg_QSee'],
 ['gg_P4a','*','norm_pair','norm_index'],['gg_P4','*','gg_P4a','norm_transport']]
ROOT_NORM=[
 ['gg_A','-','gg_Aplus1',1],['gg_A2','*','gg_A','gg_A'],
 ['gg_cross','*','gg_p','gg_r2'],['gg_four','*',4,'gg_cross'],
 ['gg_K','-','gg_A2','gg_four'],['gg_unit','+','gg_K',1],
 ['gg_product','*','gg_P4','gg_unit'],['polynomial14','-','gg_product',1]]
ROOT_OUTER=[
 ['gg_PA','*','gg_P4','gg_Aplus1'],['gg_AO','-','gg_PA',1],
 ['gg_AO2','*','gg_AO','gg_AO'],['gg_Pp','*','gg_P4','gg_p'],
 ['gg_Pr2','*','gg_P4','gg_r2'],['gg_cross','*','gg_Pp','gg_Pr2'],
 ['gg_four','*',4,'gg_cross'],['polynomial14','-','gg_AO2','gg_four']]


def make_gap14():
    old,_=fourteen_build()
    prefix=[]
    for row in old['source']:
        if row[0]=='ng_ic2': break
        if row[0]!='aux_y2': prefix.append(row[:])
    require(len(prefix)==49,'root-free gap prefix count')
    common={k:old[k] for k in ('fixed_numerals','witness_domain','repository_commit','coefficient_binding','output')}
    common.update(witnesses=[GAP if n=='y_aux' else n for n in old['witnesses']],
                  source_provenance='Authenticated package06 baseline67, with both f and the original y-square deleted; gap norm tail in build_gap.py.',
                  domain_proof='GAP_AUXILIARY_PROOF.md, including the nonzero remainder r and the T=0 exclusion.',
                  strong_coordinate='Normalized i; restoration uses ordinary i_O=Delta*i.')
    norm=dict(common,name='blank14_gap_norm75',source=prefix+ROOT_COMMON+ROOT_NORM,
              exact_degree=219,
              leading_form='32*h*gamma*e^2*i^8*k0^19*w^17*s^36*Q0^131*(Q0-F)^2*(w*(Q0-F-alpha)-z*Q0), Q0=Bm1*Jrep, k0=eta+zeta',
              leading_monomial_certificate={
                'exponents':{'Jrep':134,'h':1,'gamma':1,GAP:2,'i':8,'eta':19,'w':17,'s':36,'transport_quotient':1},
                'coefficient':'-32*Bm1^134','nonzero_condition':'Bm1 > 0'})
    outer=dict(common,name='blank14_gap_outer75',source=prefix+ROOT_COMMON+ROOT_OUTER,
               exact_degree=268,
               leading_form='256*h^2*gamma^2*e^2*i^8*k0^22*w^22*s^44*Q0^160*(Q0-F)^2*(w*(Q0-F-alpha)-z*Q0)^2, Q0=Bm1*Jrep, k0=eta+zeta',
               leading_monomial_certificate={
                 'exponents':{'Jrep':164,'h':2,'gamma':2,GAP:2,'i':8,'eta':22,'w':22,'s':44,'transport_quotient':2},
                 'coefficient':'256*Bm1^164','nonzero_condition':'Bm1 > 0'},
               comparison_note='This valid outer-norm form is dominated by blank14_gap_norm75 at the same operation count. It does not dominate the old 73-operation outer form.')
    for packet in (norm,outer):
        finish(packet)
        require(packet['ledger']['operations']==75,'gap14 count')
    return norm,outer


def supplied_gap_as_y(v):
    """Independent direct formula, without reading circuit registers."""
    q=v['Bm1']*v['Jrep']+1; C=q-v['F']-v['alpha']
    Y=v['s']*q**3; c=(v['eta']+v['zeta'])*Y+v['eta']
    R=(q*(q-v['F'])-C)*(q*q-1)+(v['MC']+q*v['MF'])*v['Jrep']
    V=c*(v['auxiliary_quotient']*v['f']-1)-R*v['f']*v['f']
    out={n:x for n,x in v.items() if n!=GAP}
    out['y_aux']=V+v[GAP]
    return out


def root_formula(v):
    J,F,al,z,h,i,T,s,w,tau,eta,zeta,e,gamma=[v[n] for n in
      ('Jrep','F','alpha','transport_quotient','h','i','auxiliary_quotient','s','w','tau_root','eta','zeta',GAP,'gamma')]
    beta,K,MC,MF=[v[n] for n in ('Bm1','Kconstant','MC','MF')]
    q=beta*J+1; C=q-F-al; X=w*q; Y=s*q**3; E=X*Y
    k=eta+zeta; c=k*Y+eta; a=E+Y; H=4*a+3; Delta=a*a+H
    D=X+a*c+gamma*H; R=(q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J
    L=E*k*Y; Q=(Delta*i*c*c)**2; d=1+Delta*i*i*c**4
    b=c+R*d; vv=c*T; S=Q-1; rr=b+S*e; p=d*vv*vv
    AA=p+b*b+S*e*(2*b-e)-1; BB=2*vv*rr
    P4=(tau*tau-L*(L+k))*(D*D-Delta*c*c)*(k-h*E-R)*((K+w)*C+q-F-z*(q-1))
    norm=AA*AA-d*BB*BB
    outerA=P4*(AA+1)-1
    return P4*(1+norm)-1,outerA*outerA-d*(P4*BB)**2


def leading_value(packet,prime,seed):
    """Evaluate the independently derived highest homogeneous form."""
    rng=random.Random(seed)
    v={}
    for n in packet['witnesses']:
        rng.randrange(1,11)
        v[n]=rng.randrange(1,17)
    if 'positive_guarded_coordinates' in packet:
        for n in packet['positive_guarded_coordinates']:
            v[n]=sum(v[n+s]**2 for s in ('_u','_v','_t'))
    q=31*v['Jrep']; k=v['eta']+v['zeta']; w=v['w']; s=v['s']
    T2=w*(q-v['F']-v['alpha'])-v['transport_quotient']*q
    name=packet['name'].split('_over_')[0]
    if name=='ordinary_gap70':
        value=-16*q**52*v['h']*v['gamma']*v['i']**2*k**8*w**7*s**15*v['auxiliary_quotient']*v['f']**3*v[GAP]*T2
    elif name=='ordinary_gap_sos78':
        value=(w*w*k*k*s**4*q**14)**2+(v['i']**2*k**4*s**4*q**12)**2
        if 'positive_guarded_coordinates' not in packet:
            value+=(2*v[GAP]*k*w*w*s**3*q**11*v['auxiliary_quotient']*v['f']**3)**2
    elif name=='blank14_gap_norm75':
        value=32*v['h']*v['gamma']*v[GAP]**2*v['i']**8*k**19*w**17*s**36*q**131*(q-v['F'])**2*T2
    elif name=='blank14_gap_outer75':
        value=256*v['h']**2*v['gamma']**2*v[GAP]**2*v['i']**8*k**22*w**22*s**44*q**160*(q-v['F'])**2*T2**2
    else:
        raise ValueError('no leading output formula')
    return value%prime


def verify(packets15,packets14,lifts15,lifts14):
    rng=random.Random(7014219)
    for case in range(100):
        supplied={n:rng.randrange(-8,10) for n in packets15[0]['witnesses']+packets15[0]['fixed_numerals']}
        if case>=50: supplied={n:Fraction(v,rng.randrange(1,5)) for n,v in supplied.items()}
        old=supplied_gap_as_y(supplied)
        product,_,factors=ordinary_formula(old)
        values=evaluate(packets15[0]['source'],supplied)
        require(values[packets15[0]['output']]==product,'gap15 product formula')
        require([values[n] for n in packets15[0]['factors']]==factors,'gap15 factor formulas')
        _,residuals,_=ordinary_formula(old,shifted=True)
        values=evaluate(packets15[1]['source'],supplied)
        def get(x): return x if type(x) is int else values[x]
        require([get(a)-get(b) for a,b in packets15[1]['comparisons']]==residuals,'gap15 residuals')
        require(evaluate(packets15[2]['source'],supplied)[packets15[2]['output']]==sum(x*x for x in residuals),'gap15 sos')
        del supplied['f']
        for packet,wanted in zip(packets14,root_formula(supplied)):
            require(evaluate(packet['source'],supplied)[packet['output']]==wanted,'gap14 independent formula')
    for _ in range(100):
        f,c,Q,R,T,e,P4=[rng.randrange(-10,12) for _ in range(7)]
        d=f*f; b=c+R*d; vv=c*T; S=Q-1; rr=b+S*e; V=vv*f-b; y=V+e
        A=d*vv*vv+rr*rr-Q*S*e*e-1; B=2*vv*rr
        N=Q*(V*V-y*y)+y*y
        require(N==V*V-(Q-1)*e*(2*V+e),'gap auxiliary expansion')
        require(A==d*vv*vv+b*b+S*e*(2*b-e)-1,'root cancellation identity')
        require(A-B*f==N-1,'gap14 root remainder')
        require(P4*(A+1)-1-P4*B*f==P4*N-1,'gap14 outer remainder')
        if T==0: require(A+1==Q*b*b-(Q-1)*(e-b)**2,'zero-T identity')
    for base,lifted in zip(packets15+packets14,lifts15+lifts14):
        for _ in range(32):
            v={n:rng.randrange(-5,7) for n in lifted['witnesses']+lifted['fixed_numerals']}
            original={n:v[n] for n in lifted['unrestricted_original_coordinates']+lifted['fixed_numerals']}
            for n in lifted['positive_guarded_coordinates']:
                u,z,t=[v[n+s] for s in ('_u','_v','_t')]
                original[n]=1+u*u+z*z+t*(t+1)
                require(original[n]>0,'positive substitution')
            before=evaluate(base['source'],original); after=evaluate(lifted['source'],v)
            require(all(before[n]==after[n] for n,_,_,_ in base['source']),'gap integer substitution')
    diagnostics={p['name']:[line_degrees(p,1000000007,701),line_degrees(p,1000000009,219)]
                 for p in packets15+packets14+lifts15+lifts14}
    for packet in packets15+packets14+lifts15+lifts14:
        for diagnostic in diagnostics[packet['name']]:
            if 'output' in packet:
                require(diagnostic['leading_coefficient']==leading_value(packet,diagnostic['prime'],diagnostic['seed']),
                        'independent highest homogeneous form')
        if 'leading_monomial_certificate' in packet:
            require(sum(packet['leading_monomial_certificate']['exponents'].values())==packet['exact_degree'],
                    'distinguished monomial degree')
    return {'status':'PASS','signed_integer_and_rational_full_formula_cases':100,
            'local_gap_and_root_identity_cases':100,'integer_substitution_cases':160,
            'leading_form_evaluation_checks':16,
            'degree_diagnostics':diagnostics,
            'scope':'Exact algebraic and circuit diagnostics. Nonzero leading forms and domain/existence claims are separately proved in GAP_AUXILIARY_PROOF.md. No accepting K215 computation is materialized.'}


def build_all():
    packets15=tuple(make_gap15(p) for p in ordinary_build())
    packets14=make_gap14()
    lifts15=(lift(packets15[0],SIGNED15,degree=179,factor_degrees=[44,35,39,13,4,44]),
             lift(packets15[1],SIGNED15,residual_degrees=[44,35,39,13,4,44]),
             lift(packets15[2],SIGNED15,degree=88))
    lifts14=(lift(packets14[0],SIGNED14,degree=434),lift(packets14[1],SIGNED14,degree=530))
    return packets15,packets14,lifts15,lifts14


def main():
    groups=build_all(); receipt=verify(*groups)
    for group in groups:
        for p in group: (HERE/(p['name']+'.json')).write_text(json.dumps(p,indent=2,sort_keys=True)+'\n')
    (HERE/'gap_verification.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'PASS','packets':[{k:p[k] for k in ('name','ledger')} for group in groups for p in group]},indent=2))


if __name__=='__main__': main()
