#!/usr/bin/env python3
"""Exact finite algebra checks; the unbounded proof is in PROOF.md."""
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import product
from math import gcd
from pathlib import Path
import json, random, sys
import sympy as S

ROOT=Path(__file__).resolve().parent
PARENT=ROOT/'parents'

def require(b,label):
    if not b: raise RuntimeError(label)

def evaluate(p, values):
    env=dict(values)
    def val(x): return x if type(x) is int else env[x]
    for name,op,x,y in p['source']:
        a,b=val(x),val(y)
        env[name]=a+b if op=='+' else a-b if op=='-' else a*b
    return env

reports=[]
for n,degree,ops,m in [(12,70,98,6),(13,51,88,3)]:
    path=ROOT/f'p{n}_free_J.json'
    p=json.loads(path.read_text())
    oldpath=PARENT/f'p{n}_ordinary_degree{degree}.json'
    old=json.loads(oldpath.read_text())
    require(sha256(oldpath.read_bytes()).hexdigest()==p['parent_sha256'],'parent hash')
    require(p['source']==old['source'][2:],'literal remainder of parent')
    require(p['witnesses']==['J']+old['witnesses'][1:],'input promotion')
    known=set(p['witnesses']+p['fixed_numerals']);parents={}
    for name,op,a,b in p['source']:
        require(name not in known and op in ['+','-','*'],'fresh arithmetic gate')
        require(all(type(x) is int or x in known for x in [a,b]),'topology')
        known.add(name);parents[name]=(a,b)
    live=set();todo=[p['output']]
    while todo:
        x=todo.pop()
        if type(x) is int or x in live: continue
        live.add(x);todo.extend(parents.get(x,()))
    require(live==known,'full liveness')
    require(len(p['witnesses'])==n and len(p['source'])==ops==p['operations'],'count')
    require(dict(Counter(row[1] for row in p['source']))==p['operation_breakdown'],'operation types')
    rng=random.Random(n*degree)
    for _ in range(100):
        v={x:rng.randrange(-3,7) for x in old['witnesses']+old['fixed_numerals']}
        new={x:v[x] for x in p['witnesses']+p['fixed_numerals'] if x!='J'}
        new['J']=m*v['j']+1
        require(evaluate(p,new)[p['output']]==evaluate(old,v)[old['output']], 'parent substitution identity diagnostic')
    lam=S.Symbol('lambda')
    vals={v:S.Poly(lam,lam) for v in p['witnesses']}
    vals.update(beta=2,K0=2,MC=3,MF=4)
    exact_univ=evaluate(p,vals)[p['output']].degree()
    require(exact_univ==degree,'full univariate degree specialization')
    reports.append(dict(variables=n,operations=ops,degree=degree,
                        operation_breakdown=p['operation_breakdown'],all_live=True,
                        parent_substitution_diagnostics=100,
                        circuit_sha256=sha256(path.read_bytes()).hexdigest()))

unit_cases=0
for q,z,r in product(range(4),repeat=3):
    M=q**3*(q-1)
    require((1+z*z-M*M*r)%4!=3,'first factor cannot be -1');unit_cases+=1
for a,c,D,U in product(range(4),repeat=4):
    delta=a*a+4*a+3
    require((1+D*D-U*U*(1+delta*c*c))%4!=3,'main factor cannot be -1');unit_cases+=1
for a,f,V,y in product(range(4),repeat=4):
    Q=(a*a+4*a+3)*(f*f-1)
    require((Q*V*V+(1-Q)*y*y)%4!=3,'auxiliary factor cannot be -1');unit_cases+=1
for a,f,I in product(range(4),repeat=3):
    Q=(a*a+4*a+3)*(f*f-1)
    require((1+I*I-Q)%4!=3,'strong factor cannot be -1');unit_cases+=1
for An,d,Q,bhalf in product(range(4),repeat=4):
    require((1+An*An-d*(2*bhalf)**2*Q)%4!=3,'merger factor cannot be -1');unit_cases+=1

gcd_cases=0
for q in range(2,101):
    for X,s in product(range(1,9),repeat=2):
        Y=q**3*s;H=4*Y*(X+1)+3;g=gcd(q,3)
        require(gcd(q,H)==gcd(q**5,H)==g,'exact gcd lemma diagnostic')
        require((q**5//g)%(q**4)==0,'early index modulus')
        gcd_cases+=1

X,Y=S.symbols('X Y')
A=(X+1)*Y+2;P0=2*X*Y**2+1
ratio=12*X*Y*(X+1)+9*X-2*(X+1)**2
require(S.expand(X*(2*A-1)**2-2*P0*(X+1)**2-ratio)==0,'exact Pell ratio identity')
require(S.expand(ratio.subs(Y,1)-(10*X**2+17*X-2))==0,'positive ratio lower bound')
require(9**16>6*8**16,'exact exponential threshold')
for r in range(24,101):
    require(Fraction(9,2)**r/2-1>2**(2*r+1),'growth comparison diagnostic')
for R in range(3,101):
    require((3*2**R-6)%8==2,'X=1 obstruction')
mersenne_cases=0
for d in range(4,101):
    beta=2**d-1
    for u in range(3*d):
        require((3*pow(2,u,beta))%beta!=1,'Mersenne exceptional-factor exclusion')
        mersenne_cases+=1

# Nonzero highest homogeneous coefficients, independent of K0, MC, MF.
J,F,al,X,Y,eta,zeta,ga,f,i,u,t,n,beta,K=S.symbols('J F alpha X Y eta zeta gamma f i u t n beta K0')
q0=beta*J;k0=eta+zeta;R0=q0**3*(q0-F)
Bt0=(K*q0+X)*(q0-F-al)-q0*F
L0=-2*q0**8*k0**2*X*Y**2*Bt0
L1=8*q0**2*k0*X**2*Y**4*(q0*q0*Y*ga+R0)
La=2*X**2*Y**2*f**4*u*R0;Ls=i*i*k0**4*Y**4
v13=[J,F,al,X,Y,eta,zeta,ga,f,i,u]
p13=S.Poly(S.expand(L0*L1*La*Ls),*v13)
mon13=J**15*F*eta**7*X**6*Y**13*f**4*i**2*u*ga*al
require(p13.total_degree()==51,'13-variable leading degree')
require(S.expand(p13.coeff_monomial(mon13)+32*beta**15)==0,'13-variable fixed-slice nonzero coefficient')
LN=4*k0**8*X**4*Y**12*t**8*R0**2*n**2
v12=[J,F,al,X,Y,eta,zeta,ga,t,n]
p12=S.Poly(S.expand(L0*L1*LN),*v12)
mon12=J**18*F**2*eta**11*X**8*Y**19*t**8*n**2*ga*al
require(p12.total_degree()==70,'12-variable leading degree')
require(S.expand(p12.coeff_monomial(mon12)-64*beta**18)==0,'12-variable fixed-slice nonzero coefficient')

report=dict(status='PASS',circuits=reports,unit_cases=unit_cases,gcd_diagnostics=gcd_cases,
            mersenne_diagnostics=mersenne_cases,ratio_identity=True,
            nonzero_leading_coefficients={'12':'64*beta^18','13':'-32*beta^15'},
            optimization=sys.flags.optimize,
            scope='Finite exact algebra and diagnostic checks. Unbounded proof is PROOF.md; native calibration inherited.')
(ROOT/('CHECKS_OPTIMIZED.json' if sys.flags.optimize else 'CHECKS.json')).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
