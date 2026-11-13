#!/usr/bin/env python3
"""Finite identity controls for a symbolic full zero at different toy ports."""
from collections import Counter
from math import comb
import hashlib
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent;D=HERE.parents[1]
pins={
 'research/current14-carrier64-transport-proposal/graph.json':'f3bc67492c0aa88c9881bf7e2c39e1586e38b3324305b025b010c0912625af43',
 'research/current14-carrier64-pell-floor/result.json':'8edbf8c5b59d4ba77d2bea5beb54f380bef1b7c1ddb3df8ef98e79c009b8181a'}
for path,digest in pins.items():
    if hashlib.sha256((D/path).read_bytes()).hexdigest()!=digest:raise RuntimeError('pin mismatch')
g=json.loads((D/'research/current14-carrier64-transport-proposal/graph.json').read_bytes())
beta,K,lo,mf=31,1,22,43;q=beta+1;hi=mf-beta;F,C=2,577;G=q*(q-F)-C
R=G*(q*q-1)+lo+q*mf;N=(R-1)//2
if not (q==32 and G==383 and R==393207 and R%4==3 and R.bit_count()==17 and
        N.bit_count()==16 and lo%4==2 and hi%8==4 and lo.bit_count()+hi.bit_count()==5 and lo+hi>beta):
    raise RuntimeError('toy scalar facts failed')
wmod=pow(2,R-5,beta);Mmod=(K+wmod)%beta
if not (wmod==4 and (Mmod*C-F)%beta==0):raise RuntimeError('candidate transport congruence failed')
u,r=divmod(G,beta);F0=q-u;C0=u-r
if not ((u,r,F0,C0)==(12,11,20,1) and (Mmod*C0-F0)%beta!=0):
    raise RuntimeError('old restricted transport obstruction failed')
if (q-F-C)!=-547:raise RuntimeError('negative recovered alpha mismatch')

def add(a,b):
    r=Counter(a);r.update(b)
    return {k:v for k,v in r.items() if v}
def scale(n,a):return {k:n*v for k,v in a.items() if n*v}
def mul(a,b):
    r=Counter()
    for i,x in a.items():
        for j,y in b.items():r[i+j]+=x*y
    return {k:v for k,v in r.items() if v}
one={0:1};v={1:1}
# Q_n(v)=T_(2n+1)(S)/S for v=S².
Q0=one;Q1={1:4,0:-3};cheb_cases=0
for n in range(0,13):
    Q=Q0 if n==0 else Q1
    expected={}
    for j in range(n+1):
        coefficient=(-1)**(n+j)*comb(2*n-j,j)*2**(2*n-2*j)
        power=n-j
        for l in range(power+1):
            expected=add(expected,{l:coefficient*comb(power,l)*(-1)**l})
    if Q!=expected or Q.get(0,0)!=(-1)**n*(2*n+1):
        raise RuntimeError('Chebyshev polynomial identity failed')
    if n>=1:
        Q0,Q1=Q1,add(mul({1:4,0:-2},Q1),scale(-1,Q0))
    cheb_cases+=1

def unit_mul(u,v,d):return (u[0]*v[0]+d*u[1]*v[1],u[0]*v[1]+u[1]*v[0])
def unit_pow(u,n,d):
    out=(1,0)
    while n:
        if n&1:out=unit_mul(out,u,d)
        u=unit_mul(u,u,d);n//=2
    return out
pell_cases=0
for a in range(1,6):
    d=a*a+4*a+3;p=a+2
    D0,c=unit_pow((p,1),3,d)
    f,L=unit_pow((D0,c),c,d)
    if L%(c*c) or f*f-d*L*L!=1:raise RuntimeError('strong Pell control failed')
    S=d*L;xx,yy=unit_pow((S,1),3,S*S-1)
    if xx%S:raise RuntimeError('auxiliary x divisibility failed')
    V=xx//S
    if (V+c)%(f*f) or (V+3)%c or S*S*V*V-(S*S-1)*yy*yy!=1:
        raise RuntimeError('auxiliary congruence control failed')
    pell_cases+=1

# Symbolic graph comparison modulo a prime for finite random-like controls.
def evaluate(inputs,mod):
    env=dict(inputs)
    for name,op,left,right in g['source']:
        x=env[left] if isinstance(left,str) else left;y=env[right] if isinstance(right,str) else right
        env[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()%mod
    return env[g['output']]
def direct(v,mod):
    J,F,C,z,f,i,T,s,w,n,eta,zeta,y,gamma=[v[x] for x in g['witnesses']]
    beta,K,lo,mf=[v[x] for x in g['fixed_numerals']]
    b=beta*J;q=b+1;X=w*q;Y=s*q**3;E=X*Y;k=eta+zeta
    ell=E*k*Y;c=k*Y+eta;a=E+Y;H=4*a+3;delta=a*a+H
    D0=X+a*c+gamma*H;R=(q*(q-F)-C)*(q*q-1)+(lo+q*mf)*J
    tau=E*n+k-R;V=f*f*(c*T-R)-c;S=i*delta*c*c
    return ((tau*tau-ell*(ell+k))*(D0*D0-delta*c*c)*
            (S*S*(V*V-y*y)+y*y)*((K+w)*C+q-F-z*b)*(delta*f*f-S*S)-delta)%mod
for seed in range(1,51):
    inp={name:(seed*(j+3)+1)%101 for j,name in enumerate(g['witnesses']+g['fixed_numerals'])}
    if evaluate(inp,101)!=direct(inp,101):raise RuntimeError('graph transcription mismatch')
print(json.dumps({'pins':pins,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'toy_ports':{'beta':beta,'K':K,'MC':lo,'MF':mf},'q':q,'gap':G,'rank':R,
 'rank_mod_4':3,'rank_popcount':R.bit_count(),'N_popcount':N.bit_count(),
 'candidate_F':F,'candidate_C':C,'candidate_alpha_recovered':-547,
 'old_same_q_R_w_repair':False,'chebyshev_polynomial_controls':cheb_cases,
 'small_strong_auxiliary_controls':pell_cases,'modular_graph_controls':50,
 'scope':'symbolic toy-port construction only; no actual-port conclusion or expanded witness'},sort_keys=True,indent=2))
