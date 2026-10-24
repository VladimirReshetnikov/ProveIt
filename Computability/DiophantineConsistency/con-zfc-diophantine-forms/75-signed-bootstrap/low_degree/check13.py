#!/usr/bin/env python3
"""Standard-library exact sparse algebra for the new thirteen-variable form.

No bounded search can establish Con(ZFC); this checks finite algebra only.
Coefficient ports are symbolic indeterminates with witness degree zero.
"""
import json,hashlib
from pathlib import Path
from collections import Counter

ROOT=Path(__file__).resolve().parent
packet=json.loads((ROOT/'p13_degree30.json').read_text())
names=packet['witnesses']; ports=packet['fixed_numerals']; allnames=names+ports
N=len(allnames); ZERO=(0,)*N

class Poly:
    def __init__(self,data=0):
        self.d=dict(data) if isinstance(data,dict) else ({ZERO:data} if data else {})
    @staticmethod
    def var(name):
        e=[0]*N; e[allnames.index(name)]=1; return Poly({tuple(e):1})
    def __add__(self,other):
        if not isinstance(other,Poly): other=Poly(other)
        z=dict(self.d)
        for e,c in other.d.items():
            z[e]=z.get(e,0)+c
            if not z[e]: del z[e]
        return Poly(z)
    __radd__=__add__
    def __neg__(self): return Poly({e:-c for e,c in self.d.items()})
    def __sub__(self,other): return self+-other if isinstance(other,Poly) else self+(-other)
    def __rsub__(self,other): return -self+other
    def __mul__(self,other):
        if not isinstance(other,Poly): other=Poly(other)
        z={}
        for e,c in self.d.items():
            for f,d in other.d.items():
                g=tuple(a+b for a,b in zip(e,f)); z[g]=z.get(g,0)+c*d
        return Poly({e:c for e,c in z.items() if c})
    __rmul__=__mul__
    def __pow__(self,n):
        a=self; b=Poly(1)
        while n:
            if n%2: b=b*a
            n//=2
            if n: a=a*a
        return b
    def degree(self): return max((sum(e[:len(names)]) for e in self.d),default=-1)
    def lead(self):
        d=self.degree(); return Poly({e:c for e,c in self.d.items() if sum(e[:len(names)])==d})
    def terms(self):
        return [{'coefficient':c,'powers':{n:p for n,p in zip(allnames,e) if p}} for e,c in sorted(self.d.items())]

env={n:Poly.var(n) for n in allnames}
j,F,alpha,f,i,T,X,Y,r,eta,zeta,u,gamma=(env[n] for n in names)
beta,K0,MC,MF=(env[n] for n in ports)
J=3*j+1; q=beta*J+1; C=q-F-alpha
E=X*Y; k=eta+zeta; c=k*Y+eta; a=E+Y; H=4*a+3; Delta=a*a+H
ell=E*k*Y; b0=X+a*c; I=i*c*c
R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
r0=k-R-1; Kidx=4*q*Y; U=q*Kidx; Dstar=U*b0+H*(U*gamma+Kidx*X-r0)
Kaux=Delta*(f*f-1); V=f*f*(c*T-R)-c
W=(q-1)*k+1; M=q**3*(q-1)
T1=(q*K0+X)*C+q*(q-F-1)
Z0=M*(ell+k+q*W+r)+(q-1)*Y-q**3*W*T1
forms=[Z0**2-M**2*(ell*(ell+k)+1),
       Dstar**2-U**2*(1+Delta*c*c),
       (V+u)**2-Kaux*u*(2*V+u)-1,
       f*f-Delta*I*I-1]
need=set(packet['residuals'])
for n,op,x,y in reversed(packet['source']):
    if n in need: need.update((x,y))
for n,op,x,y in packet['source']:
    if n not in need: continue
    a0=env[x] if isinstance(x,str) else Poly(x)
    b0_=env[y] if isinstance(y,str) else Poly(y)
    env[n]={'+':lambda:a0+b0_,'-':lambda:a0-b0_,'*':lambda:a0*b0_}[op]()
checks=[]
for rid,formula,expected_degree in zip(packet['residuals'],forms,packet['residual_degrees']):
    if (env[rid]-formula).d: raise RuntimeError('Formula mismatch '+rid)
    deg=formula.degree()
    if deg!=expected_degree: raise RuntimeError(('degree',rid,deg))
    checks.append({'residual':rid,'degree':deg,'monomials':len(formula.d),'leading_terms':formula.lead().terms()})

# Verify each actual finalizer over four independent indeterminates.
# Choosing four distinct symbols in this ring is an injective cut embedding.
for pp,label in [(packet,'combined')]:
    cut={rid:Poly.var(names[ii]) for ii,rid in enumerate(pp['residuals'])}
    finalstart=1+max(ii for ii,row in enumerate(pp['source']) if row[0] in pp['residuals'])
    for nn,oo,xx,yy in pp['source'][finalstart:]:
        aa=cut[xx] if isinstance(xx,str) else Poly(xx)
        bb=cut[yy] if isinstance(yy,str) else Poly(yy)
        cut[nn]={'+':lambda:aa+bb,'-':lambda:aa-bb,'*':lambda:aa*bb}[oo]()
    expected=sum((cut[rid]**2 for rid in pp['residuals']),Poly(0))
    if (cut[pp['output']]-expected).d: raise RuntimeError(label+' finalizer')

outdeg=max(2*x['degree'] for x in checks)
if outdeg!=30: raise RuntimeError('Output degree')

needed={packet['output']}
for name,op,x,y in reversed(packet['source']):
    if name in needed: needed.update((x,y))
if any(row[0] not in needed for row in packet['source']): raise RuntimeError('Dead gate')
if not set(names+ports)<=needed: raise RuntimeError('Dead input')
if len(packet['source'])!=94: raise RuntimeError('Gate count')

Z=U*gamma+Kidx*X-r0
expanded=U**2*(2*a*c*X+X**2-H*c*c-1)+2*U*(a*c+X)*H*Z+H**2*Z**2
if (forms[1]-expanded).d: raise RuntimeError('Carrier expansion')

def pell(A,n):
    x,y=1,0
    for _ in range(n): x,y=A*x+(A*A-1)*y,x+A*y
    return x,y
example=[]
for q0,w,s,n in [(2,1,1,2),(2,2,1,3),(5,1,1,2),(5,2,1,3)]:
    x0=w*q0; y0=s*q0**3; P0=2*x0*y0*y0+1
    tau,psi=pell(P0,n); k0=2*psi; rr=2*n-1; rem=k0-rr-1
    if rem%(q0**5)!=0: raise RuntimeError('Index divisibility')
    W0=(q0-1)*k0+1
    rnew=W0*q0+tau-x0*y0*y0*k0-k0-s
    if rnew<=0: raise RuntimeError('Transport carrier gap')
    example.append({'q':q0,'w':w,'s':s,'n':n,'index_divisibility':True,'transport_gap_positive':True})

receipt={'status':'passed','scope':'Exact local polynomial identities, degrees, liveness and gates; not a semantic or consistency test.','variables':13,'operations':len(packet['source']),'exact_total_degree':outdeg,'residual_checks':checks,'circuit_sha256':hashlib.sha256((ROOT/'p13_degree30.json').read_bytes()).hexdigest()}
(ROOT/'CHECK13.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='residual_checks'},indent=2))
