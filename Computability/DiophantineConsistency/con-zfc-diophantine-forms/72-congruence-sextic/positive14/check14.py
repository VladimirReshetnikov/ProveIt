#!/usr/bin/env python3
"""Independent exact polynomial audit; reads inert circuit, never its builder.

Uses only the Python standard library. This certifies finite
polynomial/circuit properties only.
"""
import hashlib,json
from collections import Counter
from pathlib import Path

ROOT=Path(__file__).resolve().parent
p=json.loads((ROOT/'p14_degree24.json').read_text())
names=p['witnesses']+p['fixed_ports']
BITS=6
# Independently certify that packed monomial arithmetic cannot overflow a
# six-bit exponent field, even using uncancelled gatewise degree bounds.
bounds={n:tuple(int(j==k) for j in range(len(names))) for k,n in enumerate(names)}
zeros=(0,)*len(names)
def fixed_bound(expr):
    if isinstance(expr,int): return zeros
    if isinstance(expr,str): return bounds[expr]
    op,x,y=expr; aa,bb=fixed_bound(x),fixed_bound(y)
    if op not in ('+','-','*'): raise RuntimeError('Invalid fixed operator')
    return tuple(a+b if op=='*' else max(a,b) for a,b in zip(aa,bb))
for n,expr in p['derived_fixed_leaves'].items(): bounds[n]=fixed_bound(expr)
for n,op,x,y in p['source']:
    if op not in ('+','-','*'): raise RuntimeError('Invalid circuit operator')
    if n in bounds: raise RuntimeError('Duplicate circuit identifier')
    aa,bb=fixed_bound(x),fixed_bound(y)
    bounds[n]=tuple(a+b if op=='*' else max(a,b) for a,b in zip(aa,bb))
if max(max(v) for v in bounds.values())>=64:
    raise RuntimeError('Packed exponent width is insufficient')

class Poly(dict):
    """Sparse ring, six bits per exponent (all checked degrees stay below64)."""
    def __add__(self,other):
        if isinstance(other,int): other=Poly({0:other}) if other else Poly()
        result=Poly(self)
        for m,c in other.items():
            value=result.get(m,0)+c
            if value: result[m]=value
            else: result.pop(m,None)
        return result
    __radd__=__add__
    def __neg__(self): return Poly({m:-c for m,c in self.items()})
    def __sub__(self,other): return self+(-other)
    def __rsub__(self,other): return (-self)+other
    def __mul__(self,other):
        if isinstance(other,int): return Poly({m:c*other for m,c in self.items()}) if other else Poly()
        result={}
        for m,c in self.items():
            for n,d in other.items():
                key=m+n; result[key]=result.get(key,0)+c*d
        return Poly({m:c for m,c in result.items() if c})
    __rmul__=__mul__
    def __pow__(self,power):
        result=Poly({0:1}); base=self
        while power:
            if power&1: result=result*base
            power//=2
            if power: base=base*base
        return result
class Ring:
    one=Poly({0:1})
    zero=Poly()
    @staticmethod
    def from_dict(data): return Poly(data)
R=Ring()
generators=[Poly({1<<(BITS*j):1}) for j in range(len(names))]
env=dict(zip(names,generators)); one=R.one

def fixed(expr):
    if isinstance(expr,int): return expr*one
    if isinstance(expr,str): return env[expr]
    op,x,y=expr
    a,b=fixed(x),fixed(y)
    return {'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]()

for n,e in p['derived_fixed_leaves'].items(): env[n]=fixed(e)
F,alpha,C,f0,i,T,X,Y,r,eta,zeta,u,gamma,E=[env[n] for n in p['witnesses']]
beta,K0,MC,MF=[env[n] for n in p['fixed_ports']]
b=3*beta; b2=b*b; L=beta*b2
q=F+alpha+C; k=eta+zeta; c=k*Y+eta
a=E+Y; H=4*a+3; Delta=a*a+H; ell=E*k*Y
Nf=b*f0+q-beta-1; I=i*c*c
Rhat=beta*((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*(q-1)
M0=q**3*(q-1); Bt=(q*K0+X)*C-q*F
Ztail=M0*r+(q-1)*Y-q**3*Bt
A0=2*M0*ell*Ztail+Ztail**2-M0**2*(ell*k+1)
Mb=4*beta*q*q*Y; Sb=4*beta*q*Y
shift=Mb*gamma+Sb*X-beta*(k-1)+Rhat
A1=Mb**2*(2*a*c*X+X*X-H*c*c-1)+2*Mb*(a*c+X)*H*shift+H*H*shift**2
Vh=Nf**2*(beta*c*T-Rhat)-L*c
Aa=b2*(Vh+L*u)**2-Delta*(Nf*Nf-b2)*L*u*(2*Vh+L*u)-b2*L*L
As=Nf*Nf-b2*(1+Delta*I*I)
AE=E-X*Y
direct=[A0,A1,Aa,As,AE]

need=set(p['residuals'])
for n,op,x,y in reversed(p['source']):
    if n in need: need.update((x,y))
for n,op,x,y in p['source']:
    if n not in need: continue
    aa=env[x] if isinstance(x,str) else x*one
    bb=env[y] if isinstance(y,str) else y*one
    env[n]={'+':lambda:aa+bb,'-':lambda:aa-bb,'*':lambda:aa*bb}[op]()

def witness_degree(m): return sum((m>>(BITS*j))&63 for j in range(14))
def degree(poly):
    return max((witness_degree(m) for m in poly),default=-1)
def leader(poly):
    d=degree(poly); return R.from_dict({m:v for m,v in poly.items() if witness_degree(m)==d})
checks=[]
for name,formula,deg in zip(p['residuals'],direct,[12,11,12,12,2]):
    if formula!=env[name]: raise RuntimeError('Independent formula mismatch: '+name)
    if degree(formula)!=deg: raise RuntimeError('Degree mismatch: '+name)
    checks.append({'residual':name,'degree':deg,'symbolic_terms':len(formula)})
expected=-9*beta**2*i**2*(eta+zeta)**4*Y**4*(E+Y)**2
if leader(As)!=expected: raise RuntimeError('Strong leading form mismatch')

A0lead=q**7*E*k*Y*(2*q*r-2*Bt-q*k)
Aalead=9*beta**4*(b*f0+q)**4*q**6*(q-F)**2
if leader(A0)!=A0lead: raise RuntimeError('First leading form mismatch')
if leader(Aa)!=Aalead: raise RuntimeError('Auxiliary leading form mismatch')
# Only As contains i, so i^4 eta^8 E^4 Y^8 has coefficient81 beta^4.
# Verify the output as a polynomial over five independent residual indeterminates.
cut={name:env[p['witnesses'][j]] for j,name in enumerate(p['residuals'])}
last=max(j for j,row in enumerate(p['source']) if row[0] in p['residuals'])
for n,op,x,y in p['source'][last+1:]:
    aa=cut[x] if isinstance(x,str) else x*one
    bb=cut[y] if isinstance(y,str) else y*one
    cut[n]={'+':lambda:aa+bb,'-':lambda:aa-bb,'*':lambda:aa*bb}[op]()
if cut[p['output']]!=sum((cut[n]**2 for n in p['residuals']),R.zero):
    raise RuntimeError('Final sum-of-squares mismatch')

needed={p['output']}
for n,op,x,y in reversed(p['source']):
    if n in needed: needed.update((x,y))
if any(n not in needed for n,_,_,_ in p['source']): raise RuntimeError('Dead circuit gate')
if not set(names)<=needed: raise RuntimeError('Dead witness/native port')
if len(p['source'])!=101: raise RuntimeError('Operation count')

receipt={'status':'PASS','scope':'Exact symbolic circuit identities, exact witness degrees, leading form, finalizer and liveness. Not a test or formal certificate of unbounded consistency equivalence.',
 'unknowns':14,'domain':'strictly positive integers','operations':len(p['source']),
 'operation_breakdown':dict(Counter(row[1] for row in p['source'])),
 'residuals':checks,'exact_total_degree':24,
 'degree24_output_leading_form':'leader(A0)^2+leader(Aa)^2+leader(As)^2',
 'maximal_residual_leading_forms':{'A0':'q^7 E k Y (2 q r - 2 Bt - q k)','Aa':'9 beta^4 (3 beta f0+q)^4 q^6 (q-F)^2','As':'-9 beta^2 i^2 k^4 Y^4 (E+Y)^2'},
 'nonzero_selected_coefficient':'81 beta^4',
 'selected_monomial':'i^4 eta^8 E^4 Y^8',
 'circuit_sha256':hashlib.sha256((ROOT/'p14_degree24.json').read_bytes()).hexdigest()}
(ROOT/'CHECK14.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
