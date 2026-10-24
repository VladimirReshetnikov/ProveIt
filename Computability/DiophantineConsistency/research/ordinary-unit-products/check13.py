#!/usr/bin/env python3
"""Independent local algebra, liveness/count and degree checks for P13/51."""
from collections import Counter
from hashlib import sha256
import itertools,json,random,sys
from pathlib import Path
import sympy as S
ROOT=Path(__file__).resolve().parent
def require(b,label):
    if not b:raise RuntimeError(label)
p=json.loads((ROOT/'p13_ordinary_degree51.json').read_text())
known=set(p['witnesses']+p['fixed_numerals']);parents={}
for n,op,a,b in p['source']:
    require(n not in known and op in ['+','-','*'],'fresh arithmetic gate')
    require(all(type(x)is int or x in known for x in [a,b]),'topology')
    known.add(n);parents[n]=(a,b)
live=set();todo=[p['output']]
while todo:
    x=todo.pop()
    if type(x)is int or x in live:continue
    live.add(x);todo.extend(parents.get(x,()))
require(live==known,'every gate and input live')
require(len(p['witnesses'])==13 and len(p['source'])==p['operations']==90,'literal counts')
require(dict(Counter(x[1]for x in p['source']))==p['operation_breakdown']=={'*':49,'+':24,'-':17},'gate types')
old=json.loads((ROOT.parent/'short-unit-products/p13_product_degree55.json').read_text())
prefix=lambda a:a['source'][:next(i for i,r in enumerate(a['source'])if r[0]=='A1')+1]
require(prefix(p)==prefix(old),'exact previously checked carrier')
def evaluate(v):
    e=dict(v)
    def get(x):return x if type(x)is int else e[x]
    for n,op,a,b in p['source']:
        x,y=get(a),get(b);e[n]=x+y if op=='+' else x-y if op=='-' else x*y
    return e
cases=0
for q,z,r in itertools.product(range(4),repeat=3):
    M=q**3*(q-1);require((1+z*z-M*M*r)%4!=3,'first negative unit');cases+=1
for a,c,D,U in itertools.product(range(4),repeat=4):
    delta=a*a+4*a+3;require((1+D*D-U*U*(1+delta*c*c))%4!=3,'main negative unit');cases+=1
for a,f,V,y in itertools.product(range(4),repeat=4):
    Q=(a*a+4*a+3)*(f*f-1);require((Q*V*V+(1-Q)*y*y)%4!=3,'aux negative unit');cases+=1
for a,f,I in itertools.product(range(4),repeat=3):
    Q=(a*a+4*a+3)*(f*f-1);require((1+I*I-Q)%4!=3,'ordinary strong negative unit');cases+=1
j,F,al,X,Y,eta,zeta,ga,f,i,u,beta,K=S.symbols('j F alpha X Y eta zeta gamma f i u beta K0')
q0=3*beta*j;k0=eta+zeta;R0=q0**3*(q0-F);Bt0=(K*q0+X)*(q0-F-al)-q0*F
L0=-2*q0**8*k0**2*X*Y**2*Bt0
L1=8*q0**2*k0*X**2*Y**4*(q0*q0*Y*ga+R0)
La=2*X**2*Y**2*f**4*u*R0;Ls=i*i*k0**4*Y**4
variables=[j,F,al,X,Y,eta,zeta,ga,f,i,u]
poly=S.Poly(S.expand(L0*L1*La*Ls),*variables)
require(poly.total_degree()==51,'homogeneous degree')
mon=j**15*F*eta**7*X**6*Y**13*f**4*i**2*u*ga*al
require(S.expand(poly.coeff_monomial(mon)+32*(3*beta)**15)==0,'nonzero actual-slice coefficient')
lam=S.Symbol('lambda');vals={v:S.Poly(lam,lam)for v in p['witnesses']}
vals.update(beta=1,K0=2,MC=3,MF=4)
require(evaluate(vals)[p['output']].degree()==51,'entire circuit univariate degree')
rng=random.Random(139051)
for _ in range(160):
    v={x:rng.randrange(1,12)for x in p['witnesses']+p['fixed_numerals']};e=evaluate(v)
    J=3*v['j']+1;q=v['beta']*J+1;E=v['X']*v['Y'];k=v['eta']+v['zeta']
    c=k*v['Y']+v['eta'];a=E+v['Y'];delta=a*a+4*a+3
    R=((q-1)*(q-v['F'])+v['alpha'])*(q*q-1)+(v['MC']+q*v['MF'])*J
    Q=delta*(v['f']**2-1);V=v['f']**2*(c*v['T']-R)-c;y=V+v['u']
    Fa=Q*V*V+(1-Q)*y*y;Fs=1+(v['i']*c*c)**2-Q
    require(e['Fa']==Fa and e['Fs']==Fs,'new factor specification')
    require(e[p['output']]==(1+e['A0'])*(1+e['A1'])*Fa*Fs-1,'finalizer specification')
out=dict(status='PASS',domain='strictly positive integers',variables=13,operations=90,
 operation_breakdown=p['operation_breakdown'],all_gates_and_inputs_live=True,
 exact_degree=51,factor_degrees=[15,13,13,10],unit_residue_cases=cases,
 selected_monomial=str(mon),selected_coefficient='-32*(3*beta)^15',
 selected_coefficient_independent_of=['K0','MC','MF'],univariate_degree=51,
 scalar_transcription_trials=160,circuit_sha256=sha256((ROOT/'p13_ordinary_degree51.json').read_bytes()).hexdigest(),
 sympy=S.__version__,python_optimization=sys.flags.optimize,
 scope='Local finite algebra only. Ordinary rank/source proof is in ORDINARY13.md; whole native calibration and internal-ZFC formalization are not newly proved.')
name='CHECKS13_OPTIMIZED.json'if sys.flags.optimize else'CHECKS13.json'
(ROOT/name).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
