#!/usr/bin/env python3
"""Independent exact arithmetic checks; no accepting computation is claimed."""
from pathlib import Path
from collections import Counter
from fractions import Fraction
import json, random

ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'evidence/base67.json'
CIRCUITS=ROOT/'circuits'
VERIFICATION=ROOT/'verification'
CIRCUITS.mkdir(parents=True,exist_ok=True)
VERIFICATION.mkdir(parents=True,exist_ok=True)
SIGNED={'tau_root','y_aux','w','h','f','auxiliary_quotient'}

def check(ok,msg):
    if not ok: raise ValueError(msg)

def evaluate(rows,inputs):
    v=dict(inputs)
    for n,op,a,b in rows:
        a=a if type(a) is int else v[a]
        b=b if type(b) is int else v[b]
        v[n]=a+b if op=='+' else a-b if op=='-' else a*b
    return v

def ledger(p):
    rows=p['source']; available=set(p['witnesses']+p['fixed_numerals'])
    for n,op,a,b in rows:
        check(n not in available,'duplicate register '+n)
        check(op in ['+','-','*'],'unknown operator')
        check(all(type(t) is int or t in available for t in (a,b)),'unbound operand '+n)
        available.add(n)
    need=set(p.get('outputs',[p.get('output','polynomial')]))
    live=[]
    for row in reversed(rows):
        if row[0] in need:
            live.append(row[0]); need.update(t for t in row[2:] if type(t) is str)
    check(len(live)==len(rows),'dead register')
    check(set(p['witnesses']+p['fixed_numerals'])<=need,'dead port')
    c=Counter(row[1] for row in rows)
    return {'operations':len(rows),'M':c['*'],'A':c['+']+c['-'],
            'all_gates_live':True,'all_ports_live':True}

def reduced(p):
    p=json.loads(json.dumps(p)); rows=[]
    for row in p['source']:
        if row[0]=='L17':
            rows.append(['reduced_coefficient','-','scaled_f_square','A'])
            row=['L17','*','reduced_coefficient','aux_square_gap']
        rows.append(row)
    p['source']=rows; p['name']='fixed_blank_68'; p['exact_degree']=123
    p['ledger']=ledger(p)
    return p

def lift(p):
    rows=[]; witnesses=[]
    for x in p['witnesses']:
        if x in SIGNED: witnesses.append(x); continue
        a,b,c=(x+'__'+s for s in ('a','b','c'))
        witnesses.extend([a,b,c])
        rows.extend([[x+'__a2','*',a,a],[x+'__b2','*',b,b],
                     [x+'__c1','+',c,1],[x+'__tri','*',c,x+'__c1'],
                     [x+'__sum2','+',x+'__a2',x+'__b2'],
                     [x+'__sum3','+',x+'__sum2',x+'__tri'],
                     [x,'+',x+'__sum3',1]])
    rows.extend(p['source'])
    out={'name':p['name']+'_integer33','witness_domain':'unrestricted integers',
         'witnesses':witnesses,'fixed_numerals':p['fixed_numerals'],
         'source':rows,'output':'polynomial',
         'exact_degree':292 if p['name']=='fixed_blank_67' else 228,
         'signed_coordinates':sorted(SIGNED),
         'substitution':'x=1+x__a^2+x__b^2+x__c*(x__c+1)',
         'proof':'proofs/signed_domain.md; full-domain theorem is mathematical, not inferred from these tests'}
    out['ledger']=ledger(out)
    check(len(witnesses)==33,'wrong variable count')
    return out

def poly_eval(rows,inputs,prime):
    v=dict(inputs)
    for n,op,a,b in rows:
        a=[a] if type(a) is int else v[a]
        b=[b] if type(b) is int else v[b]
        if op=='*':
            c=[0]*(len(a)+len(b)-1)
            for i,x in enumerate(a):
                for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%prime
        else:
            c=[0]*max(len(a),len(b))
            for i in range(len(c)):
                c[i]=((a[i] if i<len(a) else 0)+(1 if op=='+' else -1)*(b[i] if i<len(b) else 0))%prime
        while len(c)>1 and c[-1]==0:c.pop()
        v[n]=c
    return v

def degree_line(p,degree,seed=33):
    rng=random.Random(seed); prime=1000000007
    v={n:[rng.randrange(1,8),rng.randrange(1,12)] for n in p['witnesses']}
    v.update({n:[x] for n,x in zip(p['fixed_numerals'],(31,127,10,45))})
    got=poly_eval(p['source'],v,prime)['polynomial']
    check(len(got)-1==degree,'degree line failure '+p['name'])
    return {'modulus':prime,'seed':seed,'degree':len(got)-1,'leading_coefficient':got[-1],
            'scope':'attainment diagnostic; uniform upper bound and nonzero leading form proved in the report'}

def root_formula(values,outer=False):
    J,F,alpha,z,h,i,T,s,w,tau,eta,zeta,y,gamma=(values[n] for n in
       ['Jrep','F','alpha','transport_quotient','h','i','auxiliary_quotient','s','w','tau_root','eta','zeta','y_aux','gamma'])
    m,K,MC,MF=(values[n] for n in ['Bm1','Kconstant','MC','MF'])
    q=m*J+1; C=q-F-alpha; X=w*q; Y=s*q**3; E=X*Y
    k=eta+zeta; c=k*Y+eta; a=E+Y; H=4*a+3; delta=a*a+H
    mainroot=X+a*c+gamma*H
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    L=E*k*Y
    P4=(tau*tau-L*(L+k))*(mainroot*mainroot-delta*c*c)*(k-h*E-R)*((K+w)*C+q-F-z*(q-1))
    u=i*c*c; S=delta*u; Q=S*S; D=1+u*S
    v=c*T; zz=c+R*D
    A=Q*(D*v*v+zz*zz-y*y)+y*y-1
    B=2*Q*v*zz
    if outer:return (P4*(A+1)-1)**2-D*(P4*B)**2
    return P4*(1+A*A-D*B*B)-1

def main():
    raw=json.loads(BASE.read_text()); p=raw.get('packet',raw)
    p68=reduced(p); integer=[lift(p),lift(p68)]
    report={'status':'PASS','scope':'circuit algebra, liveness, degree diagnostics; not a finite-witness proof of the Diophantine theorem','integer_forms':[],'root_forms':[]}
    rng=random.Random(21533)
    for b,k in zip([p,p68],integer):
        for _ in range(40):
            inp={n:rng.randrange(-3,4) for n in k['witnesses']}
            inp.update({n:x for n,x in zip(k['fixed_numerals'],(31,127,10,45))})
            restored={n:inp[n] if n in SIGNED else 1+inp[n+'__a']**2+inp[n+'__b']**2+inp[n+'__c']*(inp[n+'__c']+1) for n in b['witnesses']}
            restored.update({n:inp[n] for n in k['fixed_numerals']})
            check(evaluate(k['source'],inp)['polynomial']==evaluate(b['source'],restored)['polynomial'],'substitution mismatch')
        d=degree_line(k,k['exact_degree'])
        (CIRCUITS/(k['name']+'.json')).write_text(json.dumps(k,indent=2)+'\n')
        report['integer_forms'].append({'name':k['name'],'variables':len(k['witnesses']),'ledger':k['ledger'],'degree':d,'substitution_identity_cases':40})
    for filename,deg,outer in [('root14_product75.json',293,False),('root14_outer73.json',342,True)]:
        path=CIRCUITS/filename
        check(path.exists(),'Missing root circuit '+filename+'; run code/build_root14.py first')
        k=json.loads(path.read_text()); l=ledger(k)
        for _ in range(40):
            vals={n:Fraction(rng.randrange(-3,5),rng.randrange(1,4)) for n in k['witnesses']+k['fixed_numerals']}
            check(evaluate(k['source'],vals)['polynomial']==root_formula(vals,outer),'root formula mismatch')
        report['root_forms'].append({'name':k['name'],'variables':len(k['witnesses']),'ledger':l,'degree':degree_line(k,deg,14),'signed_rational_formula_cases':40})
    (VERIFICATION/'signed_root.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
