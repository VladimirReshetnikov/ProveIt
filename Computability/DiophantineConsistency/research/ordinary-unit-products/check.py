#!/usr/bin/env python3
"""Independent algebra/count checks for the materialized manuscript equation."""
from collections import Counter
from hashlib import sha256
import itertools,json,random,sys
from pathlib import Path
import sympy as S

ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[3]
BASE=REPO/'Computability/DiophantineConsistency/con-zfc-diophantine-forms'
def require(b,label):
    if not b:raise RuntimeError(label)
def eq(a,b,label):require(S.expand(a-b)==0,label)

p=json.loads((ROOT/'p12_ordinary_degree70.json').read_text())
known=set(p['witnesses']+p['fixed_numerals']);dependencies={}
for n,op,a,b in p['source']:
    require(n not in known and op in ['+','-','*'],'fresh division-free node')
    require(all(type(x)is int or x in known for x in [a,b]),'topology')
    known.add(n);dependencies[n]=(a,b)
live=set();todo=[p['output']]
while todo:
    n=todo.pop()
    if type(n)is int or n in live:continue
    live.add(n);todo.extend(dependencies.get(n,()))
require(live==known,'every gate and input live')
require(len(p['witnesses'])==12 and len(p['source'])==p['operations']==100,'counts')
require(dict(Counter(x[1]for x in p['source']))==p['operation_breakdown']=={'*':55,'+':26,'-':19},'operation types')

def evaluate(packet,values,mod=None,targets=None):
    e=dict(values);needed=None
    if targets is not None:
        needed=set(targets)
        for n,op,a,b in reversed(packet['source']):
            if n in needed and n not in e:needed.update((a,b))
    def get(x):return x if type(x)is int else e[x]
    for n,op,a,b in packet['source']:
        if n in e or (needed is not None and n not in needed):continue
        x,y=get(a),get(b);out=x+y if op=='+' else x-y if op=='-' else x*y
        e[n]=out%mod if mod else out
    return e

# The complete early carrier is literally the previously checked carrier.
old=json.loads((ROOT.parent/'short-unit-products/p12_adaptive_degree78.json').read_text())
prefix=lambda a:a['source'][:next(i for i,r in enumerate(a['source'])if r[0]=='A1')+1]
require(prefix(p)==prefix(old),'exact adaptive carrier prefix')

# Exact, freely varying polynomial cuts. No builder import.
d,Q,V,n,i=S.symbols('d Q V n i')
h=lambda x:(1-Q)*x*x+2*(1-Q)*V*x+V*V-1
bn=2*(1-Q)*(n+V);AN=d*h(n)+(1-Q)*Q
N=AN*AN-d*bn*bn*Q
cut=evaluate(p,{'den':d,'Q':Q,'V':V,'n':n},targets=['N'])
eq(cut['N'],N,'literal ordinary merger')
eq(N.subs(Q,d*i*i),d*d*h(n-i).subs(Q,d*i*i)*h(n+i).subs(Q,d*i*i),'ordinary exact factorization')
AN0,dd,rr,bb=S.symbols('AN dd rr bb')
eq((AN0/(dd*bb))**2-rr/dd,(AN0*AN0-dd*bb*bb*rr)/(dd*dd*bb*bb),'rational strong reconstruction')
y=S.symbols('y');eq(h(y-V),Q*V*V-(Q-1)*y*y-1,'adjacent norm recovery')
A=S.symbols('A');psi6=32*A**5-32*A**3+6*A
eq(psi6-A*(A*A-1)**2,A*(31*A**4-30*A*A+5),'early rank growth margin')

# All negative-unit exclusions on the imposed parity domain.
residue_cases=0
for z,mm,rad in itertools.product(range(4),[0,2],range(4)):
    require((1+z*z-mm*mm*rad)%4!=3,'carrier unit');residue_cases+=1
for an,dd,qq,bn0 in itertools.product(range(4),range(4),range(4),[0,2]):
    require((1+an*an-dd*bn0*bn0*qq)%4!=3,'merged unit');residue_cases+=1

# Exact highest homogeneous form with fixed ports retained symbolically.
j,F,alpha,X,Y,eta,zeta,ga,t,nn,beta,K=S.symbols('j F alpha X Y eta zeta gamma t n beta K0')
q0=6*beta*j;k0=eta+zeta;R0=q0**3*(q0-F)
Bt0=(K*q0+X)*(q0-F-alpha)-q0*F
L0=-2*q0**8*k0**2*X*Y**2*Bt0
L1=8*q0**2*k0*X**2*Y**4*(q0*q0*Y*ga+R0)
LN=4*k0**8*X**4*Y**12*t**8*R0**2*nn**2
vs=[j,F,alpha,X,Y,eta,zeta,ga,t,nn]
leader=S.Poly(S.expand(L0*L1*LN),*vs)
require(leader.total_degree()==70,'homogeneous degree')
mon=j**18*F**2*eta**11*X**8*Y**19*t**8*nn**2*ga*alpha
eq(leader.coeff_monomial(mon),64*(6*beta)**18,'actual-slice nonzero coefficient')
lam=S.Symbol('lambda')
vals={v:S.Poly(lam,lam)for v in p['witnesses']};vals.update(beta=1,K0=2,MC=3,MF=4)
degree=evaluate(p,vals)[p['output']].degree();require(degree==70,'whole-circuit univariate degree')

# Independent direct formula, exact scalar evaluations reduced only at gates.
def specification(v):
    j,F,al,t,T,X,Y,r,eta,zeta,n,ga=[v[k]for k in p['witnesses']]
    beta,K,MC,MF=[v[k]for k in p['fixed_numerals']]
    J=6*j+1;q=beta*J+1;C=q-F-al;E=X*Y;k=eta+zeta;c=k*Y+eta
    a=E+Y;H=4*a+3;Delta=a*a+H;ell=E*k*Y;M=q**3*(q-1);W=(q-1)*k+1
    Bt=(q*K+X)*C-q*F;Z=M*(ell+k+r)+(q-1)*Y-q**3*W*Bt
    A0=Z*Z-M*M*(ell*(ell+k)+1)
    R=((q-1)*(q-F)+al)*(q*q-1)+(MC+q*MF)*J;U=q*q*Y
    D=U*(X+a*c)+H*(U*ga+q*E-(k-R-1));A1=D*D-U*U*(1+Delta*c*c)
    f=t+1;rho=f*f-1;Q=Delta*rho;d=c**4;V=f*f*(c*T-R)-c
    h=(1-Q)*n*n+2*(1-Q)*V*n+V*V-1;bn=2*(1-Q)*(n+V)
    N=(d*h+(1-Q)*Q)**2-d*bn*bn*Q
    return {'A0':A0,'A1':A1,'N':N,'P12':(1+A0)*(1+A1)*(1+N)-1}
rng=random.Random(10070)
for trial in range(160):
    vals={v:rng.randrange(1,12)for v in p['witnesses']+p['fixed_numerals']}
    mod=[1000000007,1000000009][trial%2];actual=evaluate(p,vals,mod);expected=specification(vals)
    require(all(actual[k]==v%mod for k,v in expected.items()),'independent scalar formula')

source='35-cancel12/sources/catalogue/25-hybrid12/upstream/ORDINARY_BLANK_PROOF.md'
pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
for path,hsh in pins.items():
    if not path.startswith('manuscript '):require(sha256((REPO/path).read_bytes()).hexdigest()==hsh,'pinned carrier/source bytes')
receipt=dict(status='PASS',domain='strictly positive integers',variables=12,operations=100,
 operation_breakdown=p['operation_breakdown'],all_gates_and_inputs_live=True,
 exact_degree=70,residual_degrees=[15,13,42],unit_residue_cases=residue_cases,
 selected_monomial=str(mon),selected_coefficient='64*(6*beta)^18',
 selected_coefficient_independent_of=['K0','MC','MF'],univariate_degree=degree,
 scalar_transcription_trials=160,circuit_sha256=sha256((ROOT/'p12_ordinary_degree70.json').read_bytes()).hexdigest(),
 ordinary_source_path=source,ordinary_source_sha256=sha256((BASE/source).read_bytes()).hexdigest(),
 sympy=S.__version__,python_optimization=sys.flags.optimize,
 scope='Finite algebra/data only; the note supplies ordinary witness maps and early rank proof. Native calibration and object-ZFC formalization remain inherited/open.')
name='CHECKS_OPTIMIZED.json'if sys.flags.optimize else'CHECKS.json'
(ROOT/name).write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
