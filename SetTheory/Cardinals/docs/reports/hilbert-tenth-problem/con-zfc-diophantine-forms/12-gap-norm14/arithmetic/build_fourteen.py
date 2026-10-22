#!/usr/bin/env python3
"""Eliminate the normalized strong root f from the fixed blank circuit."""
from __future__ import annotations
import json
import hashlib
import random
from pathlib import Path
from fractions import Fraction
from build_improved import require, ledger, evaluate, line_degrees

HERE=Path(__file__).resolve().parent
NORM_TAIL=[
 ['ng_ic2','*','i','c2'],['ng_Dminus1','*','ng_ic2','aux_coefficient_root'],
 ['ng_D','+','ng_Dminus1',1],['ng_RD','*','r_lhs','ng_D'],
 ['ng_b','+','R10a','ng_RD'],['ng_u','*','R10a','auxiliary_quotient'],
 ['ng_u2','*','ng_u','ng_u'],['ng_p','*','ng_D','ng_u2'],
 ['ng_b2','*','ng_b','ng_b'],['ng_P4a','*','norm_pair','norm_index'],
 ['ng_P4','*','ng_P4a','norm_transport'],['ng_sum','+','ng_p','ng_b2'],
 ['ng_gap','-','ng_sum','aux_y2'],['ng_Qgap','*','R16','ng_gap'],
 ['ng_Aplus1','+','ng_Qgap','aux_y2'],['ng_A','-','ng_Aplus1',1],
 ['ng_Qp','*','R16','ng_p'],['ng_Qb2','*','R16','ng_b2'],
 ['ng_cross','*','ng_Qp','ng_Qb2'],['ng_four','*',4,'ng_cross'],
 ['ng_A2','*','ng_A','ng_A'],['ng_K','-','ng_A2','ng_four'],
 ['ng_unit','+','ng_K',1],['ng_product','*','ng_P4','ng_unit'],
 ['polynomial14','-','ng_product',1]]
OUTER_TAIL=[
 ['er_ic2','*','i','c2'],['er_kS','*','er_ic2','aux_coefficient_root'],
 ['er_D','+','er_kS',1],['er_RD','*','r_lhs','er_D'],
 ['er_b','+','R10a','er_RD'],['er_u','*','R10a','auxiliary_quotient'],
 ['er_u2','*','er_u','er_u'],['er_p','*','er_D','er_u2'],
 ['er_b2','*','er_b','er_b'],['er_P4a','*','norm_pair','norm_index'],
 ['er_P','*','er_P4a','norm_transport'],['er_C','*','er_P','R16'],
 ['er_L','*','er_C','er_p'],['er_M','*','er_C','er_b2'],
 ['er_Pc','-','er_P','er_C'],['er_Z','*','er_Pc','aux_y2'],
 ['er_LM','+','er_L','er_M'],['er_LMZ','+','er_LM','er_Z'],
 ['er_alpha','-','er_LMZ',1],['er_alpha2','*','er_alpha','er_alpha'],
 ['er_prod','*','er_L','er_M'],['er_four','*',4,'er_prod'],
 ['polynomial14','-','er_alpha2','er_four']]

def build():
    base=json.loads((HERE/'baseline67.json').read_text())['packet']
    require(hashlib.sha256(json.dumps(base['source'],sort_keys=True,separators=(',',':')).encode()).hexdigest()
            =='a3031aa143c392b9ccb1fba3e9dfe7259dcba50df179b05c46fbc47140eccac0',
            'baseline67 source authentication failed')
    dep={'f'}; prefix=[]
    for row in base['source']:
        if any(x in dep for x in row[2:] if isinstance(x,str)): dep.add(row[0])
        else: prefix.append(row)
    common={k:base[k] for k in ('fixed_numerals','witness_domain')}
    common.update(witnesses=[x for x in base['witnesses'] if x!='f'],
                  source_provenance='Baseline67 plus the norm-elimination identities of package05; fixed-input marker cone omitted.',
                  repository_commit='3b201cdea32d2c816f5f3d20734051f25fd3ef14',
                  coefficient_binding='compiler/cross_constants.json: four fixed cross-compiler ports; MF is the shifted source port. The coherent original 06-blank67 coefficient tuple is an alternative.',
                  output='polynomial14')
    norm=dict(common,name='blank14_norm75',source=prefix+NORM_TAIL,exact_degree=293,
              leading_form='8*h*gamma*i^12*(eta+zeta)^27*w^21*s^48*Q^177*(Q-F)^4*(w*(Q-F-alpha)-z*Q), Q=Bm1*Jrep')
    outer=dict(common,name='blank14_outer73',source=prefix+OUTER_TAIL,exact_degree=342,
               leading_form='64*h^2*gamma^2*i^12*(eta+zeta)^30*w^26*s^56*Q^206*(Q-F)^4*(w*(Q-F-alpha)-z*Q)^2, Q=Bm1*Jrep')
    for p in (norm,outer): p['ledger']=ledger(p)
    require(norm['ledger']['operations']==75 and outer['ledger']['operations']==73,'counts')
    return norm,outer

def formula(v):
    J,F,al,z,h,i,T,s,w,tau,eta,zeta,y,gamma=[v[n] for n in
      ('Jrep','F','alpha','transport_quotient','h','i','auxiliary_quotient','s','w','tau_root','eta','zeta','y_aux','gamma')]
    beta,K,MC,MF=[v[n] for n in ('Bm1','Kconstant','MC','MF')]
    q=beta*J+1; C=q-F-al; X=w*q; Y=s*q**3; E=X*Y
    k=eta+zeta; c=k*Y+eta; a=E+Y; H=4*a+3; Delta=a*a+H
    Dmain=X+a*c+gamma*H; R=(q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J
    L=E*k*Y; Q=(Delta*i*c*c)**2; D=1+Delta*i*i*c**4
    b=c+R*D; u=c*T; A=Q*(D*u*u+b*b-y*y)+y*y-1; B=2*Q*u*b
    P4=(tau*tau-L*(L+k))*(Dmain*Dmain-Delta*c*c)*(k-h*E-R)*((K+w)*C+q-F-z*(q-1))
    N=A*A-D*B*B
    AO=P4*(Q*(D*u*u+b*b)+(1-Q)*y*y)-1
    BO=P4*B
    return P4*(1+N)-1,AO*AO-D*BO*BO

def lift32(packet):
    signed={'h','auxiliary_quotient','tau_root','y_aux','gamma'}
    guarded=[x for x in packet['witnesses'] if x not in signed]
    rows=[]; witnesses=[]
    for n in packet['witnesses']:
        if n in signed: witnesses.append(n); continue
        u,v,t=[n+s for s in ('_u','_v','_t')]; witnesses += [u,v,t]
        rows += [[n+'_u2','*',u,u],[n+'_v2','*',v,v],[n+'_t1','+',t,1],
                 [n+'_tt1','*',t,n+'_t1'],[n+'_uv2','+',n+'_u2',n+'_v2'],
                 [n+'_sum','+',n+'_uv2',n+'_tt1'],[n,'+',n+'_sum',1]]
    rows += packet['source']
    out=dict(packet,name=packet['name']+'_over_Z32',source=rows,witnesses=witnesses,
             witness_domain='all integers',positive_guarded_coordinates=guarded,
             unrestricted_original_coordinates=sorted(signed),
             positive_substitution='x=1+x_u^2+x_v^2+x_t*(x_t+1)',
             exact_degree=584 if packet['name']=='blank14_norm75' else 680,
             domain_proof='ROOT_ELIMINATION_PROOF.md, including exclusion of T=0 before root restoration.')
    out.pop('leading_form')
    out['ledger']=ledger(out)
    require(len(witnesses)==32,'lift dimension')
    return out

def verify(packets,lifts):
    rng=random.Random(147573)
    for case in range(100):
        v={n:rng.randrange(-6,8) for n in packets[0]['witnesses']+packets[0]['fixed_numerals']}
        if case>=50: v={n:Fraction(x,rng.randrange(1,5)) for n,x in v.items()}
        outputs=formula(v)
        for packet,wanted in zip(packets,outputs):
            require(evaluate(packet['source'],v)[packet['output']]==wanted,'formula mismatch')
    for packet,lift in zip(packets,lifts):
        for _ in range(32):
            v={n:rng.randrange(-5,7) for n in lift['witnesses']+lift['fixed_numerals']}
            orig={n:v[n] for n in lift['unrestricted_original_coordinates']+lift['fixed_numerals']}
            for n in lift['positive_guarded_coordinates']:
                u,z,t=[v[n+s] for s in ('_u','_v','_t')]; orig[n]=1+u*u+z*z+t*(t+1)
            require(evaluate(lift['source'],v)[lift['output']]==evaluate(packet['source'],orig)[packet['output']],'lift mismatch')
    # Exact local resultant/restoration identities, off compiler zeros.
    for _ in range(100):
        f,c,Q,R,T,y,P4=[rng.randrange(-10,12) for _ in range(7)]
        D=f*f; b=c+R*D; u=c*T; V=u*f-b
        A=Q*(D*u*u+b*b-y*y)+y*y-1; B=2*Q*u*b
        require(A-B*f==Q*(V*V-y*y)+y*y-1,'local norm remainder')
        AO=P4*(A+1)-1; BO=P4*B
        require(AO-BO*f==P4*(Q*(V*V-y*y)+y*y)-1,'outer norm remainder')
    diagnostics={p['name']:[line_degrees(p,1000000007,1475),line_degrees(p,1000000009,1473)] for p in packets+lifts}
    return {'status':'PASS','formula_cases':100,'root_identity_cases':100,'substitution_cases':64,
            'degree_diagnostics':diagnostics,
            'scope':'Circuit, formula, resultant and degree diagnostics; no numerical K215 halting or compiler witness is materialized.'}

def main():
    packets=build(); lifts=tuple(lift32(p) for p in packets); receipt=verify(packets,lifts)
    for p in packets+lifts: (HERE/(p['name']+'.json')).write_text(json.dumps(p,indent=2,sort_keys=True)+'\n')
    (HERE/'root_elimination_verification.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'PASS','packets':[{k:p[k] for k in ('name','ledger','exact_degree')} for p in packets+lifts]},indent=2))

if __name__=='__main__': main()
