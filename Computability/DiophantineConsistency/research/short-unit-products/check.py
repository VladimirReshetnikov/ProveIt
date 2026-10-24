#!/usr/bin/env python3
"""Independent finite checks of the new equations; never imports build.py.

Requires SymPy. These checks do not certify the unbounded inherited native
calibration, do not find consistency witnesses, and do not run Lean.
"""
from collections import Counter
from hashlib import sha256
import itertools,json,random
from pathlib import Path
import sympy as S
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[3]
BASE=REPO/'Computability/DiophantineConsistency/con-zfc-diophantine-forms'
def require(b,label):
    if not b:raise RuntimeError(label)
def eq(a,b,label):require(S.expand(a-b)==0,label)
def topology(p):
    known=set(p['witnesses']+p['fixed_numerals']); parents={}
    for n,op,a,b in p['source']:
        require(n not in known and op in ['+','-','*'],'fresh node')
        for x in [a,b]:require(type(x)is int or x in known,'topological operand')
        known.add(n);parents[n]=a,b
    live=set();todo=[p['output']]
    while todo:
        x=todo.pop()
        if type(x)is int or x in live:continue
        live.add(x);todo.extend(parents.get(x,()))
    require(live==known,'every gate/input live')
    require(len(p['source'])==p['operations'],'literal count')
    require(dict(Counter(r[1]for r in p['source']))==p['operation_breakdown'],'op breakdown')
    return dict(operations=len(p['source']),all_gates_and_inputs_live=True,**p['operation_breakdown'])
def evaluate(p,e,mod=None,targets=None):
    e=dict(e)
    needed=None
    if targets is not None:
        needed=set(targets)
        for n,op,a,b in reversed(p['source']):
            if n in needed:needed.update((a,b))
    def get(x):return x if type(x)is int else e[x]
    for n,op,a,b in p['source']:
        if needed is not None and n not in needed:continue
        x,y=get(a),get(b);v=x+y if op=='+' else x-y if op=='-' else x*y
        e[n]=v%mod if mod else v
    return e

def independent_spec(v,m,kind):
    j,F,al,X,Y,r,eta,zeta,ga=[v[k]for k in ['j','F','alpha','X','Y','r','eta','zeta','gamma']]
    beta,K,MC,MF=[v[k]for k in ['beta','K0','MC','MF']]
    J=m*j+1;q=beta*J+1;C=q-F-al;E=X*Y;k=eta+zeta;c=k*Y+eta;a=E+Y
    H=4*a+3;Delta=a*a+H;ell=E*k*Y;W=(q-1)*k+1;M=q**3*(q-1)
    Bt=(q*K+X)*C-q*F
    Z=M*(ell+k+r)+(q-1)*Y-q**3*W*Bt
    A0=Z*Z-M*M*(ell*(ell+k)+1)
    R=((q-1)*(q-F)+al)*(q*q-1)+(MC+q*MF)*J
    U=q*q*Y;Ds=U*(X+a*c)+H*(U*ga+q*E-(k-R-1))
    A1=Ds*Ds-U*U*(1+Delta*c*c)
    f=v['f']if kind==13 else v['t']+1;rho=f*f-1;Q=Delta*rho;V=f*f*(c*v['T']-R)-c
    if kind==13:
        Aa=(V+v['u'])**2-Q*v['u']*(2*V+v['u'])-1
        As=f*f-Delta*(v['i']*c*c)**2-1
        return {'A0':A0,'A1':A1,'Aa':Aa,'As':As,'output':(A0+1)*(A1+1)*(Aa+1)*(As+1)-1}
    n=v['n'];d=Delta*c**4;h=(1-Q)*n*n+2*(1-Q)*V*n+V*V-1;bn=2*(1-Q)*(n+V)
    N=(d*h+(1-Q)*rho)**2-d*bn*bn*rho
    return {'A0':A0,'A1':A1,'N':N,'output':(1+A0)*(1+A1)*(1+N)-1}

p13=json.loads((ROOT/'p13_product_degree55.json').read_text())
p12=json.loads((ROOT/'p12_adaptive_degree78.json').read_text())
ref=json.loads((ROOT/'p13_sos_reference.json').read_text())
require([p13['operations'],p12['operations'],ref['operations']]==[90,101,92],'claimed counts')
receipt={'topology':{'p13':topology(p13),'p12':topology(p12),'reference13':topology(ref)}}

# Exhaust all relevant square-residue classes. The ordinary proof in the
# note explains why this suffices to exclude the negative integer unit.
count=0
for q,Z,rad in itertools.product(range(4),repeat=3):
    M=q**3*(q-1);require((1+Z*Z-M*M*rad)%4!=3,'first factor negative unit');count+=1
for a,c,D,U in itertools.product(range(4),repeat=4):
    delta=a*a+4*a+3;rad=1+delta*c*c
    require((1+D*D-U*U*rad)%4!=3,'main factor negative unit');count+=1
for a,f,V,y in itertools.product(range(4),repeat=4):
    Q=(a*a+4*a+3)*(f*f-1)
    require((Q*V*V+(1-Q)*y*y)%4!=3,'aux factor negative unit');count+=1
for a,f,I in itertools.product(range(4),repeat=3):
    require((f*f-(a*a+4*a+3)*I*I)%4!=3,'strong factor negative unit');count+=1
for AN,d,rho,bn in itertools.product(range(4),range(4),range(4),[0,2]):
    require((1+AN*AN-d*bn*bn*rho)%4!=3,'merged factor negative unit');count+=1
receipt['unit_residue_cases']=count

# Independent exact identities at free algebraic cuts.
ell,M,k,e=S.symbols('ell M k e')
eq((M*ell+e)**2-M*M*(ell*(ell+k)+1),e*e+M*ell*(2*e-M*k)-M*M,'first carrier cancellation')
U,a,c,X,H,z=S.symbols('U a c X H z')
eq((U*(X+a*c)+H*z)**2-U*U*(1+(a*a+H)*c*c),
   U*U*(2*a*c*X+X*X-H*c*c-1)+2*U*(a*c+X)*H*z+H*H*z*z,'main carrier cancellation')
d,rho,Q,V,n,i=S.symbols('d rho Q V n i')
h=lambda x:(1-Q)*x*x+2*(1-Q)*V*x+V*V-1
AN=d*h(n)+(1-Q)*rho;bn=2*(1-Q)*(n+V);N=AN*AN-d*bn*bn*rho
factored=d*d*h(n-i)*h(n+i)
eq(N.subs(rho,d*i*i),factored,'exact rational norm merger')
y=S.symbols('y');eq(h(y-V),Q*V*V-(Q-1)*y*y-1,'adjacent-coefficient Pell norm')
u=S.symbols('u');eq((V+u)**2-Q*((V+u)**2-V**2),
                   (V+u)**2-Q*u*(2*V+u),'auxiliary factor equals source residual plus one')

# Authenticate exact carrier compatibility with source73, including j_old=2j.
syms={x:S.Symbol(x)for x in p12['witnesses']+p12['fixed_numerals']}
source73=json.loads((BASE/'73-guard-reanchoring/positive/p13_degree30.json').read_text())
oldvals={x:syms.get(x,S.Symbol(x))for x in source73['witnesses']+source73['fixed_numerals']}
oldvals['j']=2*syms['j']
new=evaluate(p12,syms,targets=['A0','A1']);old=evaluate(source73,oldvals,targets=['A0','A1'])
require(new['A0']==old['A0'] and new['A1']==old['A1'],'literal carrier equality under j_old=2j')

# Degree proof via exact independent highest homogeneous forms. The note
# gives upper envelopes from the cancellation identities checked above.
j,F,alpha,X,Y,eta,zeta,ga,f,ii,u,t,nn,beta,K=S.symbols('j F alpha X Y eta zeta gamma f i u t n beta K0')
k0=eta+zeta;delta0=X*X*Y*Y;c0=k0*Y
leaders={}
for m in [3,6]:
    q0=m*beta*j;R0=q0**3*(q0-F);Bt0=(K*q0+X)*(q0-F-alpha)-q0*F
    L0=-2*q0**8*k0**2*X*Y**2*Bt0
    L1=8*q0**2*k0*X**2*Y**4*(q0*q0*Y*ga+R0)
    if m==3:
        La=2*delta0*f**4*u*R0;Ls=-delta0*ii**2*c0**4;LP=S.expand(L0*L1*La*Ls)
        variables=[j,F,alpha,X,Y,eta,zeta,ga,f,ii,u]
        target={j:15,eta:7,X:8,Y:15,f:4,ii:2,u:1,ga:1,F:1,alpha:1}
        expected=32*(3*beta)**15;degree=55
    else:
        LN=4*delta0**4*c0**8*t**8*R0**2*nn**2;LP=S.expand(L0*L1*LN)
        variables=[j,F,alpha,X,Y,eta,zeta,ga,t,nn]
        target={j:18,eta:11,X:12,Y:23,t:8,nn:2,ga:1,F:2,alpha:1}
        expected=64*(6*beta)**18;degree=78
    poly=S.Poly(LP,*variables);require(poly.total_degree()==degree,'leader degree')
    mon=S.prod(v**target.get(v,0)for v in variables)
    require(S.expand(poly.coeff_monomial(mon)-expected)==0,'fixed-port-independent leading coefficient')
    leaders[str(len(p13['witnesses'])if m==3 else len(p12['witnesses']))]={
      'degree':degree,'selected_monomial':str(mon),'selected_coefficient':str(expected),
      'nonvanishing':'beta>0, independently of K0, MC, MF'}
receipt['leading_certificates']=leaders

# Full-circuit univariate scaling independently catches missed higher terms.
Tscale=S.Symbol('lambda')
scaling={}
for p in [p13,p12]:
    vals={x:S.Poly(Tscale,Tscale)for x in p['witnesses']};vals.update(beta=1,K0=2,MC=3,MF=4)
    out=evaluate(p,vals)[p['output']]
    deg=out.degree();require(deg==p['exact_degree'],'full circuit scaled degree')
    scaling[str(len(p['witnesses']))]=deg
receipt['whole_circuit_scaled_degrees']=scaling

# Independent scalar specifications versus literal packets at varied ports.
rng=random.Random(132378);trials=0
for p,m,kind in [(p13,3,13),(p12,6,12)]:
    for trial in range(120):
        vals={x:rng.randrange(1,12)for x in p['witnesses']+p['fixed_numerals']}
        modulus=1000000007 if trial%2 else 1000000009
        result=evaluate(p,vals,modulus);spec=independent_spec(vals,m,kind)
        for name in p['residuals']:
            # P13 product intentionally prunes the shifted Aa/As registers.
            if name in result:require(result[name]==spec[name]%modulus,'residual transcription')
        require(result[p['output']]==spec['output']%modulus,'whole literal transcription');trials+=1
receipt['scalar_spec_trials']=trials

# Compare all four native coefficient raw hashes across inherited evidence.
bind=json.loads((BASE/'69-cones-pell/positive/native/ACTIVE_BINDING.json').read_text())
ver=json.loads((BASE/'74-centered-pell-gaps/VERIFICATION.json').read_text())
text=json.dumps(ver)
require(all(info['sha256_raw']in text for info in bind['ports'].values()),'whole tuple agreement')
receipt['whole_compact44_raw_hashes']={k:v['sha256_raw']for k,v in bind['ports'].items()}
pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
require(all(sha256((BASE/name).read_bytes()).hexdigest()==digest for name,digest in pins.items()),'pinned source bytes')
receipt['pinned_sources']=len(pins)
receipt.update(status='PASS',sympy=S.__version__,scope='Finite algebra, residue classes, circuit counts/topology/liveness and degree certificates; ordinary proof in note supplies universal equivalences; inherited native calibration remains unformalized.')
receipt['candidate_sha256']={n:sha256((ROOT/n).read_bytes()).hexdigest()for n in ['p13_product_degree55.json','p12_adaptive_degree78.json']}
(ROOT/'CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
