#!/usr/bin/env python3
"""Reproducible blank-input ordinary-strong circuits; no third-party imports.

The emitter audits arithmetic, liveness, degrees and restoration identities.
These diagnostics are not an end-to-end formalized Diophantine compiler proof.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random

HERE=Path(__file__).resolve().parent
def require(ok, message):
    if not ok: raise ValueError(message)

def prune(source, outputs):
    need=set(x for x in outputs if isinstance(x,str)); result=[]
    for row in reversed(source):
        if row[0] in need:
            result.append(row)
            need.update(x for x in row[2:] if isinstance(x,str))
    return result[::-1]

def ledger(packet):
    source=packet['source']; ports=packet['witnesses']+packet['fixed_numerals']
    known=set(ports)
    for name,op,a,b in source:
        require(name not in known, 'duplicate register')
        require(op in ('+','-','*'), 'bad operation')
        require(all(type(x) is int or isinstance(x,str) and x in known for x in (a,b)), 'unknown operand')
        known.add(name)
    outputs=([packet['output']] if 'output' in packet else [x for pair in packet['comparisons'] for x in pair])
    require(prune(source,outputs)==source, 'dead operation')
    used={x for row in source for x in row[2:] if isinstance(x,str)}
    require(set(ports)<=used, 'unused port')
    counts=Counter(row[1] for row in source)
    return {'operations':len(source),'multiplications':counts['*'],
            'additions_subtractions':counts['+']+counts['-'],
            'all_gates_live':True,'all_ports_live':True}

def evaluate(source, supplied):
    vals=dict(supplied)
    def get(x): return x if type(x) is int else vals[x]
    for name,op,a,b in source:
        av,bv=get(a),get(b)
        vals[name]=av+bv if op=='+' else av-bv if op=='-' else av*bv
    return vals

def formula(supplied, shifted=False):
    v=supplied
    J,F,al,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma=[v[n] for n in
      ('Jrep','F','alpha','transport_quotient','f','h','i','auxiliary_quotient',
       's','w','tau_root','eta','zeta','y_aux','gamma')]
    Bm1,K,MC,MF=[v[n] for n in ('Bm1','Kconstant','MC','MF')]
    q=Bm1*J+1; C=q-F-al; X=w*q; Y=s*q**3; E=X*Y
    k=eta+zeta; c=k*Y+eta; a=E+Y; H=4*a+3; Delta=a*a+H
    D=X+a*c+gamma*H; R=(q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J
    L=E*k*Y; V=c*(T*f-1)-R*f*f; I=i*c*c; A0=Delta*(f*f-1)
    fs=[tau*tau-L*(L+k),D*D-Delta*c*c,A0*(V*V-y*y)+y*y,
        k-h*E-R,(K+w)*C+q-F-z*(q-1),1+I*I-A0]
    residuals=[fs[0]-1,fs[1]-1,fs[2]-1,fs[3]-1,
               (K+w)*C-F-z*(q-1) if shifted else fs[4]-1,I*I-A0]
    product=1
    for x in fs: product*=x
    return product-1,residuals,fs

def build():
    base=json.loads((HERE/'baseline67.json').read_text())['packet']
    require(hashlib.sha256(json.dumps(base['source'],sort_keys=True,separators=(',',':')).encode()).hexdigest()
            =='a3031aa143c392b9ccb1fba3e9dfe7259dcba50df179b05c46fbc47140eccac0',
            'baseline67 source authentication failed')
    ordinary=[]
    drop={'aux_coefficient_root','R16','scaled_f_square','norm_strong'}
    for row in base['source']:
        if row[0]=='aux_coefficient_root':
            ordinary += [['f2_minus_one','-','L16',1],
                         ['R16','*','A','f2_minus_one'],
                         ['ordinary_ic2','*','i','c2'],
                         ['ordinary_ic2_square','*','ordinary_ic2','ordinary_ic2'],
                         ['ordinary_strong_sum','+','ordinary_ic2_square',1],
                         ['norm_strong','-','ordinary_strong_sum','R16']]
        elif row[0] not in drop:
            ordinary.append([row[0],row[1],row[2],1 if row[0]=='polynomial' else row[3]])
    common={k:base[k] for k in ('witness_domain','witnesses','fixed_numerals')}
    common['repository_commit']='3b201cdea32d2c816f5f3d20734051f25fd3ef14'
    common['coefficient_binding']='compiler/cross_constants.json: four fixed cross-compiler ports; MF is the shifted source port. The coherent original 06-blank67 coefficient tuple is an alternative.'
    common['source_provenance']='baseline67.json, Git blob 43c89cc0dba71df42138bbdbe448e4fdcce7d85e'
    product=dict(common,name='ordinary_blank69',source=ordinary,output='polynomial',
                 factors=base['factors'],exact_degree=99,factor_exact_degrees=[22,18,28,7,2,22],
                 leading_form='8*Q^55*h*gamma*i^2*(eta+zeta)^9*w^7*s^16*T^2*f^4*(w*(Q-F-alpha)-z*Q), Q=Bm1*Jrep')
    comp=[['norm_first',1],['norm_main',1],['norm_aux',1],['norm_index',1],
          ['innerC','transport_rhs'],['ordinary_ic2_square','R16']]
    shifted=[]
    for row in ordinary:
        if row[0]=='norm_transport':
            shifted.append(['transport_rhs','+','F','local_rhs'])
        elif row[0] not in {'transport_partial','norm_strong','ordinary_strong_sum'}:
            shifted.append(row)
    system_source=prune(shifted,[x for pair in comp for x in pair])
    system=dict(common,name='ordinary_blank_system60',source=system_source,comparisons=comp,
                residual_exact_degrees=[22,18,28,7,2,22],exact_maximum_degree=28,
                transport_witness='This packet uses z_new=z_old-1, both strictly positive on corresponding zeros.')
    sos_source=list(system_source)
    for n,(a,b) in enumerate(comp):
        sos_source += [[f'residual_{n}','-',a,b],[f'square_{n}','*',f'residual_{n}',f'residual_{n}']]
    prev='square_0'
    for n in range(1,len(comp)):
        sos_source.append([f'sum_{n}','+',prev,f'square_{n}']); prev=f'sum_{n}'
    sos=dict(common,name='ordinary_blank_sos77',source=sos_source,output=prev,exact_degree=56,
             transport_witness=system['transport_witness'],
             leading_form='(eta+zeta)^4*w^4*s^8*Q^28*T^4*f^8, Q=Bm1*Jrep')
    for packet in (product,system,sos):
        packet['ledger']=ledger(packet)
        packet['source_sha256']=hashlib.sha256(json.dumps(packet['source'],separators=(',',':')).encode()).hexdigest()
    require(product['ledger']['operations']==69,'product count')
    require(system['ledger']['operations']==60,'system count')
    require(sos['ledger']['operations']==77,'sos count')
    return product,system,sos

def line_degrees(packet, prime, seed):
    rng=random.Random(seed)
    vals={n:[rng.randrange(1,11),rng.randrange(1,17)] for n in packet['witnesses']}
    vals.update({n:[v] for n,v in zip(packet['fixed_numerals'],(31,127,10,45))})
    def get(x): return [x] if type(x) is int else vals[x]
    for name,op,a,b in packet['source']:
        aa,bb=get(a),get(b)
        if op=='*':
            cc=[0]*(len(aa)+len(bb)-1)
            for j,x in enumerate(aa):
                for k,y in enumerate(bb): cc[j+k]=(cc[j+k]+x*y)%prime
        else:
            cc=[((aa[j] if j<len(aa) else 0)+(1 if op=='+' else -1)*(bb[j] if j<len(bb) else 0))%prime for j in range(max(len(aa),len(bb)))]
        while len(cc)>1 and cc[-1]==0: cc.pop()
        vals[name]=cc
    if 'output' in packet:
        deg=len(vals[packet['output']])-1
        require(deg==packet['exact_degree'], 'degree not attained')
        if 'factors' in packet:
            factors=[len(vals[n])-1 for n in packet['factors']]
            require(factors==packet['factor_exact_degrees'],'factor degree')
        else: factors=None
        return {'prime':prime,'seed':seed,'degree':deg,'factor_degrees':factors,'leading_coefficient':vals[packet['output']][-1]}
    residuals=[]
    for a,b in packet['comparisons']:
        aa,bb=get(a),get(b)
        cc=[((aa[j] if j<len(aa) else 0)-(bb[j] if j<len(bb) else 0))%prime for j in range(max(len(aa),len(bb)))]
        while len(cc)>1 and cc[-1]==0: cc.pop()
        residuals.append(len(cc)-1)
    require(residuals==packet['residual_exact_degrees'],'system degrees')
    return {'prime':prime,'seed':seed,'residual_degrees':residuals}

def verify(product,system,sos):
    rng=random.Random(603369)
    for case in range(100):
        supplied={n:rng.randrange(-8,10) for n in product['witnesses']+product['fixed_numerals']}
        if case>=50: supplied={k:Fraction(v,rng.randrange(1,5)) for k,v in supplied.items()}
        p,_,fs=formula(supplied)
        values=evaluate(product['source'],supplied)
        require(values['polynomial']==p,'full product formula')
        require([values[n] for n in product['factors']]==fs,'factors')
        _,rs,_=formula(supplied,True)
        values=evaluate(system['source'],supplied)
        def get(x): return x if type(x) is int else values[x]
        require([get(a)-get(b) for a,b in system['comparisons']]==rs,'system residuals')
        require(evaluate(sos['source'],supplied)[sos['output']]==sum(x*x for x in rs),'sos')
        # Exact off-zero transport-coordinate substitution.
        shifted=dict(supplied); shifted['transport_quotient']+=1
        _,oldrs,_=formula(shifted,False)
        require(oldrs==rs,'shift transport identity')
    diagnostics={p['name']:[line_degrees(p,1000000007,603),line_degrees(p,1000000009,336)] for p in (product,system,sos)}
    # Strong reparametrization and auxiliary restoration identities use rational
    # fixtures with f^2-1=Delta*t^2*c^4 exactly; use f, c, t as rational data
    # and solve for Delta, rather than claim a positive Pell witness.
    for case in range(50):
        c,f,iN,R,T=[rng.randrange(2,15) for _ in range(5)]
        Delta=Fraction(f*f-1,iN*iN*c**4); iO=Delta*iN
        A0=Delta*(f*f-1); I2=(iO*c*c)**2
        require(A0==I2,'normalized to ordinary strong map')
        V=c*(T*f-1)-R*f*f
        o=c*T-R*f; j=T*f-1-Fraction(R*(f*f-1),c)
        require(o*f-c==V==j*c-R,'restoration identities')
    return {'status':'PASS','signed_integer_and_rational_formula_cases':100,
            'strong_and_auxiliary_identity_cases':50,'degree_diagnostics':diagnostics,
            'scope':'Algebraic and circuit diagnostics. Does not instantiate astronomical coefficients, exhibit an accepting K215 computation, or kernel-check the compiler proof.'}

def integer_lift(packet):
    signed={'h','f','auxiliary_quotient','tau_root','y_aux','gamma'}
    guarded=[x for x in packet['witnesses'] if x not in signed]
    source=[]; witnesses=[]
    for name in packet['witnesses']:
        if name in signed:
            witnesses.append(name); continue
        u,v,t=[name+suffix for suffix in ('_u','_v','_t')]
        witnesses.extend((u,v,t))
        source += [[name+'_u2','*',u,u],[name+'_v2','*',v,v],
                   [name+'_t1','+',t,1],[name+'_tt1','*',t,name+'_t1'],
                   [name+'_uv2','+',name+'_u2',name+'_v2'],
                   [name+'_sum','+',name+'_uv2',name+'_tt1'],
                   [name,'+',name+'_sum',1]]
    source+=packet['source']
    result=dict(packet,name=packet['name']+'_over_Z33',source=source,witnesses=witnesses,
                witness_domain='all integers',
                positive_guarded_coordinates=guarded,
                unrestricted_original_coordinates=sorted(signed),
                positive_substitution='x=1+x_u^2+x_v^2+x_t*(x_t+1)',
                domain_proof='Signed auxiliary and signed main-root lemmas in ORDINARY_BLANK_PROOF.md; h and gamma are automatically positive on every zero.')
    result.pop('leading_form',None)
    if 'factors' in result:
        result.update(exact_degree=190,factor_exact_degrees=[44,35,50,13,4,44])
    elif 'comparisons' in result:
        result.update(exact_maximum_degree=50,residual_exact_degrees=[44,35,50,13,4,44])
    else: result['exact_degree']=100
    result['ledger']=ledger(result)
    result['source_sha256']=hashlib.sha256(json.dumps(source,separators=(',',':')).encode()).hexdigest()
    require(len(witnesses)==33 and len(guarded)==9,'signed lift dimension')
    return result

def verify_lifts(base_packets,lift_packets):
    rng=random.Random(33190)
    for base,lift in zip(base_packets,lift_packets):
        for _ in range(32):
            assignment={n:rng.randrange(-6,8) for n in lift['witnesses']}
            assignment.update({n:v for n,v in zip(lift['fixed_numerals'],(31,127,10,45))})
            original={n:assignment[n] for n in lift['unrestricted_original_coordinates']}
            for n in lift['positive_guarded_coordinates']:
                u,v,t=[assignment[n+s] for s in ('_u','_v','_t')]
                original[n]=1+u*u+v*v+t*(t+1)
                require(original[n]>0,'positive substitution')
            original.update({n:assignment[n] for n in lift['fixed_numerals']})
            a=evaluate(base['source'],original); b=evaluate(lift['source'],assignment)
            require(all(a[n]==b[n] for n,_,_,_ in base['source']),'integer substitution identity')
    return {'status':'PASS','substitution_cases':96,
            'degree_diagnostics':{p['name']:[line_degrees(p,1000000007,331),line_degrees(p,1000000009,903)] for p in lift_packets},
            'scope':'Exact substitution and degree diagnostics; surjectivity and signed-domain soundness are mathematical lemmas.'}

def main():
    packets=build(); receipt=verify(*packets)
    lifts=tuple(integer_lift(p) for p in packets)
    lift_receipt=verify_lifts(packets,lifts)
    for p in packets+lifts:
        (HERE/(p['name']+'.json')).write_text(json.dumps(p,indent=2,sort_keys=True)+'\n')
    (HERE/'algebra_verification.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    (HERE/'integer_lift_verification.json').write_text(json.dumps(lift_receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'PASS','packets':[{k:p[k] for k in ('name','ledger')} for p in packets+lifts]},indent=2))

if __name__=='__main__': main()

