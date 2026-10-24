#!/usr/bin/env python3
"""Read-only independent modular transcription review of the P13 circuit."""
import gzip,hashlib,json,random
from collections import Counter
from pathlib import Path
HERE=Path(__file__).resolve().parent
PARENT=HERE.parent
BASE=HERE.parent/'native/coefficients'
p=json.loads((PARENT/'p13_degree28.json').read_text())
prime=(1<<127)-1
native={port:int.from_bytes(gzip.decompress((BASE/(name+'.bin.gz')).read_bytes()),'little')%prime for port,name in [('beta','beta'),('K0','K'),('MC','MC'),('MF','MF_source')]}
def need(x,msg):
    if not x:raise ValueError(msg)
def run_dag(values):
    env=dict(values)
    def fixed(x):
        if isinstance(x,int):return x%prime
        if isinstance(x,str):return env[x]
        op,a,b=x;return do(op,fixed(a),fixed(b))
    def do(op,a,b):
        if op=='+':return (a+b)%prime
        if op=='-':return (a-b)%prime
        if op=='*':return a*b%prime
        raise ValueError(op)
    for name,expr in p['derived_fixed_leaves'].items():env[name]=fixed(expr)
    for name,op,a,b in p['source']:env[name]=do(op,fixed(a),fixed(b))
    return env
def direct(v):
    F,al,C,f0,i,T,X,Y,r,eta,zeta,u,ga=[v[n] for n in p['witnesses']]
    beta,K,mc,mf=[v[n] for n in p['fixed_ports']]
    b=3*beta;L=beta*b*b
    q=F+al+C;k=eta+zeta;c=k*Y+eta;E=X*Y;l=E*k*Y;a=E+Y
    H=4*a+3;de=a*a+H;I=i*c*c;nf=b*f0+q-beta-1
    rh=beta*((q-1)*(q-F)+al)*(q*q-1)+(mc+q*mf)*(q-1)
    m0=q**3*(q-1);bt=(q*K+X)*C-q*F;Z=m0*(l+r)+(q-1)*Y-q**3*bt
    sb=4*beta*q*Y;mb=q*sb
    dh=mb*(X+a*c)+H*(mb*ga+sb*X-beta*(k-1)+rh)
    vh=nf*nf*(beta*c*T-rh)-L*c;yh=vh+L*u
    rs=[Z*Z-m0*m0*(l*(l+k)+1),dh*dh-mb*mb*(1+de*c*c),
        b*b*yh*yh-de*(nf*nf-b*b)*(yh*yh-vh*vh)-b*b*L*L,
        nf*nf-b*b*(1+de*I*I)]
    return [x%prime for x in rs]
rng=random.Random(340013)
for case in range(32):
    values={name:rng.randrange(-10,25) for name in p['witnesses']};values.update(native)
    env=run_dag(values);expected=direct(values)
    need([env[n] for n in p['residuals']]==expected,'Residual transcription '+str(case))
    need(env[p['output']]==sum(x*x for x in expected)%prime,'Output '+str(case))
needed={p['output']}
for n,op,a,b in reversed(p['source']):
    if n in needed:needed.update((a,b))
live=[row for row in p['source'] if row[0] in needed]
need(len(live)==len(p['source'])==98,'Live operation count')
counts=dict(Counter(row[1] for row in live))
need(counts=={'+':25,'-':16,'*':57},'Operation breakdown')
out={'status':'PASS','scope':'Independent read-only transcription diagnostics and count, not proof of unbounded semantic equivalence',
 'circuit_sha256':hashlib.sha256((PARENT/'p13_degree28.json').read_bytes()).hexdigest(),
 'actual_coefficient_specialization_modulus':str(prime),'synthetic_diagnostic_assignments':32,
 'operations':98,'operation_breakdown':counts,
 'reviewed_source_hashes':{name:hashlib.sha256((PARENT/name).read_bytes()).hexdigest() for name in ['section13.tex','PROOF13.md','p13_degree28.json']}}
(HERE/'REVIEW13_DIAGNOSTICS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
