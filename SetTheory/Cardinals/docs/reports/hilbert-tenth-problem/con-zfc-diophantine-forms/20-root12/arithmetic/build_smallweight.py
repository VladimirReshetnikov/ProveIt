#!/usr/bin/env python3
"""Remove the k multiplier from package 09's lower-degree resultant weight.
Validity uses the new main-norm bootstrap in SMALL_WEIGHT_PROOF.md.
"""
from pathlib import Path
import json,hashlib
import build_integer27 as lib
HERE=Path(__file__).resolve().parent

def smaller_weight(base):
    p=json.loads(json.dumps(base)); src=[]
    for n,op,a,b in p['source']:
        if n=='Qr':src += [['ic2','*','i','c2'],['i2','*','ic2','ic2']]
        elif n in ['Q','ic2']:continue
        elif n=='Dm1':src.append(['Dm1','*','A','i2'])
        elif n=='D':src += [[n,op,a,b],['Q','*','A','Dm1']]
        elif n=='v':src.append(['T2','*','auxiliary_quotient','auxiliary_quotient'])
        elif n=='v2':src.append(['v2','*','c2','T2'])
        elif n=='M':src.append(['M','+','i2','T2'])
        else:src.append([n,op,a,b])
    p.update(source=src,name=p['name']+'_smallweight')
    p.pop('degree_diagnostics',None)
    p['residual_exact_degrees']=[18,7,2,488]
    if 'comparisons' in p:p['exact_maximum_degree']=488
    elif p['name'].startswith('sos'):p['exact_degree']=976
    else:p['exact_degree']=515
    p['ledger']=lib.ledger(p)
    p['source_sha256']=hashlib.sha256(json.dumps(src,separators=(',',':')).encode()).hexdigest()
    p['weight']='M=(i*c*c)^2+T^2'
    return p

def independent(p,vals):
    J,F,alpha,z,h,i,T,s,w,eta,zeta,gamma,t=[vals[x] for x in ['Jrep','F','alpha','transport_quotient','h','i','auxiliary_quotient','s','w','eta','zeta','gamma','t']]
    beta,K,MC,MF=[vals[x] for x in p['fixed_numerals']]
    q=beta*J+1;Cw=q-F-alpha;X=w*q;Y=s*q**3;E=X*Y;k=eta+zeta;c=k*Y+eta;a=E+Y;H=4*a+3;delta=a*a+H
    Dmain=X+a*c+gamma*H;R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    Nmain=Dmain*Dmain-delta*c*c;Nk=k-h*E-R;Nt=(K+w)*Cw+q-F-z*(q-1)
    L0=E*k*Y;A=1+L0*(L0+k);I=i*c*c;D=1+delta*I*I;Q=delta*(D-1);v=c*T;b=c+R*D;d=Q-1;e=Q*(D*v*v+b*b)-1;B=2*Q*v*b;M=I*I+T*T
    C=d*(t*t+M*M*A)-e;U=C*C+D*B*B-4*d*d*t*t*M*M*A;Res=U*U-4*C*C*B*B*D
    return [Nmain-1,Nk-1,Nt-1,Res],Nmain*Nk*Nt*(1+Res)-1

def check_formula(p):
    rng=lib.random.Random(5151004)
    for n in range(120):
        v={n:rng.randrange(-3,5) for n in p['witnesses']+p['fixed_numerals']}
        if n>=60:v={k:lib.Fraction(x,rng.randrange(1,5)) for k,x in v.items()}
        truth,product=independent(p,v);ev=lib.evaluate(p,v)
        if 'comparisons' in p:
            def get(x):return x if type(x) is int else ev[x]
            actual=[get(a)-get(b) for a,b in p['comparisons']]
            lib.require(actual==truth,'independent comparison')
        else:
            expect=sum(x*x for x in truth) if p['name'].startswith('sos') else product
            lib.require(ev[p['output']]==expect,'independent full formula')
    return 120

def main():
    receipt={'status':'PASS','source_commit':lib.PIN,'new_weight':'M=I^2+T^2, I=i c^2','packets':[]}
    for name in ['polynomial13_84.json','system13_78.json','sos13_89.json']:
        old,lift=lib.lift(name);small=smaller_weight(old)
        small['coefficient_binding']=lift['coefficient_binding']
        small['historical_source_provenance']=lift['historical_source_provenance']
        fc=check_formula(small)
        lib.require(len(small['source'])==len(old['source']),'operation preservation')
        lift['source']=lift['source'][:-len(old['source'])]+small['source']
        lift['name']+='_smallweight';lift['residual_exact_degrees']=[35,13,4,952]
        if 'comparisons' in lift:lift['exact_maximum_degree']=952
        elif 'sos' in lift['name']:lift['exact_degree']=1904
        else:lift['exact_degree']=1004
        lift['ledger']=lib.ledger(lift)
        lift['source_sha256']=hashlib.sha256(json.dumps(lift['source'],separators=(',',':')).encode()).hexdigest()
        lift['weight']='M=(i*c*c)^2+T^2'
        sc=lib.substitution_checks(small,lift)
        for p in [small,lift]:
            ds=[lib.degree_line(p,1000000007,271),lib.degree_line(p,1000000009,136)]
            p['degree_diagnostics']=ds
            (HERE/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
            receipt['packets'].append(dict(name=p['name'],variables=len(p['witnesses']),ledger=p['ledger'],degree_diagnostics=ds,independent_signed_rational_formula_cases=fc,integer_substitution_cases=sc if p is lift else 0))
    # Exact rational coefficient margin used in the proof.
    lam=lib.Fraction(16,15)**4
    margin=lib.Fraction(9,20)-lam*(lib.Fraction(1,4)+lib.Fraction(4,49))
    lib.require(margin>0,'weight-bound margin')
    receipt['exact_domination_margin']=str(margin)
    receipt['scope']='Polynomial identity, count, substitution and degree diagnostics; semantic validity uses SMALL_WEIGHT_PROOF.md and INTEGER27_PROOF.md.'
    (HERE/'smallweight_verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
