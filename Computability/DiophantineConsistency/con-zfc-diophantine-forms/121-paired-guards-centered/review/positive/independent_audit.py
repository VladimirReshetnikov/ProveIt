#!/usr/bin/env python3
"""Independent direct-chart transcription and live-gate audit; no producer imports."""
import copy, gzip, hashlib, json, random
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / 'positive'

def require(test, message):
    if not test:
        raise ValueError(message)

def evaluate(obj, inputs):
    values = dict(inputs)
    for name, op, a, b in obj['source']:
        a = values[a] if isinstance(a, str) else a
        b = values[b] if isinstance(b, str) else b
        values[name] = a+b if op == '+' else a-b if op == '-' else a*b
    return values[obj['output']]

def formula(d, kind):
    ordinary=kind.startswith('ordinary_')
    kind=kind.removeprefix('ordinary_')
    d=dict(d)
    if ordinary: d['x']=0
    J,F,alpha,i,T,x,Y,n,eta,zeta = (d[k] for k in ['J','F','alpha','i','T','x','Y','n','eta','zeta'])
    beta,K0,MC,MF = (d[k] for k in ['beta','K0','MC','MF'])
    q=beta*J+1; X=q*d['w'] if ordinary else q+x; mu=q*q+1; A=mu*Y*(X+1)+1
    delta0=A*A-1; H=4*A-5; k=eta+zeta; c=k*Y+eta
    v0=X*mu*mu*Y*Y; D=v0*(v0+1)*k*k+1; E=i*c*c
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    e=k-R-1; C=q-F-alpha; B=(K0+d['w'])*C-F if ordinary else (q*K0+X)*C-q*F
    Fs=1+delta0*D*E*E; Q=delta0*delta0*D*E*E
    b=c*(T+alpha)-R; V=Fs*b-c; Dnum=Q*V*V-1
    P=q**(3 if ordinary else 4)*(q-1); M=P*mu*mu*H; Kpos=X*(3*c-2*X)+2
    center=0 if kind=='uncentered' else (A+(kind=='upper'))*D*E
    inner=(q-1)*Y-q**3*B if ordinary else q*(q-1)*Y-q**3*B-(q-1)*X
    Z=P*mu*mu*(H*(n+V+center-b*B)+Kpos)+H*(mu*mu*inner-P*e)
    s=(Q-1)*Z*Z; u=(Q-1)*M*M*D*Fs; v=M*M*Dnum
    return (s-v-u)**2-4*u*v, center+H*D*E*B

def main():
    rng=random.Random(202610242242)
    parent=json.loads((SRC/'source/prior96_equation.json').read_text())
    tests=[]
    for _ in range(32):
        d={k:rng.randrange(-4,6) for k in parent['witnesses']}
        d.update(beta=31,K0=7,MC=13,MF=47,w=rng.randrange(1,6))
        tests.append(d)
    for _ in range(16):
        d={k:rng.randrange(1,6) for k in parent['witnesses']}
        d.update(beta=31,K0=7,MC=13,MF=47,w=rng.randrange(1,6))
        tests.append(d)
    results={}
    for kind,count,degree in [('uncentered',94,262),('upper',96,258),('sharp',97,254),('ordinary_uncentered',89,288),('ordinary_upper',91,283),('ordinary_sharp',92,278)]:
        obj=json.loads((SRC/(kind+'.json')).read_text())
        require(len(obj['source'])==count, 'gate count')
        require(obj['exact_degree']==degree, 'declared degree')
        used={obj['output']}
        for name,op,a,b in reversed(obj['source']):
            require(name in used, 'dead gate '+name)
            used.update(v for v in (a,b) if isinstance(v,str))
        require(set(obj['witnesses']+obj['fixed_numerals'])<=used, 'unused input')
        for d in tests:
            expected,shift=formula(d,kind)
            require(evaluate(obj,d)==expected, 'direct formula mismatch')
            if not kind.startswith('ordinary_'):
                old=dict(d);old['n']+=shift
                require(evaluate(parent,old)==expected, 'whole carrier transfer mismatch')
        rejected=0
        for index in range(count):
            corrupt=copy.deepcopy(obj)
            op=corrupt['source'][index][1]
            corrupt['source'][index][1]={'*':'+','+':'-','-':'+'}[op]
            require(any(evaluate(corrupt,d)!=formula(d,kind)[0] for d in tests), 'undetected live mutation')
            rejected+=1
        for name,port in obj['coefficient_binding']['ports'].items():
            raw=(SRC/'coefficients'/port['file']).read_bytes()
            require(hashlib.sha256(raw).hexdigest()==port['gzip_sha256'], 'compressed coefficient '+name)
            require(hashlib.sha256(gzip.decompress(raw)).hexdigest()==port['raw_sha256'], 'coefficient '+name)
        results[kind]={'gates':count,'degree_reviewed_mathematically':degree,'independent_assignments':len(tests),'opcode_controls_rejected':rejected,'sha256':hashlib.sha256((SRC/(kind+'.json')).read_bytes()).hexdigest()}
    print(json.dumps({'status':'PASS','scope':'Independent six-chart transcription and integrity checks, with direct-chart predecessor transfers; finite tests supplement the unbounded proof review.','results':results},indent=2))

if __name__=='__main__':
    main()
