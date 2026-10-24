#!/usr/bin/env python3
"""Independent literal algebra audit; only the Python standard library.

Laurent polynomials allow the proof-only division by beta and 3 beta.
No candidate generator or verifier is imported.
"""
import collections
from fractions import Fraction
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent / 'p13_degree28.json'
p = json.loads(PACKET.read_text())
NAMES = ['F','alpha','C','f0','i','T','X','Y','r','eta','zeta','u','gamma',
         'beta','K0','MC','MF']
N = len(NAMES)
ZERO = (0,)*N

class Poly:
    def __init__(self, terms):
        self.t = {m:Fraction(c) for m,c in terms.items() if c}
    @staticmethod
    def of(x):
        return x if isinstance(x,Poly) else Poly({ZERO:Fraction(x)})
    def __add__(self, other):
        out=self.t.copy()
        for m,c in Poly.of(other).t.items(): out[m]=out.get(m,0)+c
        return Poly(out)
    __radd__=__add__
    def __neg__(self): return Poly({m:-c for m,c in self.t.items()})
    def __sub__(self,other): return self+-Poly.of(other)
    def __rsub__(self,other): return Poly.of(other)+-self
    def __mul__(self,other):
        other=Poly.of(other); out=collections.defaultdict(Fraction)
        for m,c in self.t.items():
            for n,d in other.t.items():
                out[tuple(a+b for a,b in zip(m,n))] += c*d
        return Poly(out)
    __rmul__=__mul__
    def __truediv__(self,other):
        other=Poly.of(other)
        if len(other.t)!=1: raise ValueError('Only monomial division supported')
        mon,coeff=next(iter(other.t.items()))
        return Poly({tuple(a-b for a,b in zip(m,mon)):c/coeff for m,c in self.t.items()})
    def __pow__(self,n):
        if n<0: raise ValueError(n)
        ans=Poly.of(1)
        while n:
            if n&1: ans=ans*self
            n//=2
            if n:self=self*self
        return ans
    def __eq__(self,other): return self.t==Poly.of(other).t
    def degree(self): return max(sum(m[:13]) for m in self.t)
    def leading(self):
        degree=self.degree()
        return Poly({m:c for m,c in self.t.items() if sum(m[:13])==degree})

symbols = {}
for j,name in enumerate(NAMES):
    m=list(ZERO); m[j]=1; symbols[name]=Poly({tuple(m):1})
env=symbols.copy()
F,alpha,C,f0,i,T,X,Y,r,eta,zeta,u,gamma,beta,K0,MC,MF=[symbols[n] for n in NAMES]

def calc(expr):
    if isinstance(expr,int): return Poly.of(expr)
    if isinstance(expr,str): return env[expr]
    op,x,y=expr; aa,bb=calc(x),calc(y)
    return {'+':lambda:aa+bb,'-':lambda:aa-bb,'*':lambda:aa*bb}[op]()

for name,expr in p['derived_fixed_leaves'].items(): env[name]=calc(expr)
found=set()
for name,op,x,y in p['source']:
    if name in env: raise ValueError('Repeated register: '+name)
    env[name]=calc([op,x,y])
    if name in p['residuals']: found.add(name)
    if len(found)==4: break

# Independent normalized mathematical definitions. Divisions exist only here.
q=F+alpha+C; b=3*beta; f=f0+(q-beta-1)/b; J=(q-1)/beta
k=eta+zeta; c=k*Y+eta; E=X*Y; ell=X*Y**2*k
a=(X+1)*Y; H=4*a+3; Delta=(a+2)**2-1; I=i*c**2
R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
S=4*q*Y; M=q*S; v=k-R-1
Dstar=M*(X+a*c)+H*(M*gamma+S*X-v)
M0=q**3*(q-1); Bt=(q*K0+X)*C-q*F
Z=M0*(ell+r)+(q-1)*Y-q**3*Bt
V=f*f*(c*T-R)-c; L=beta*b*b
expected=[Z*Z-M0*M0*(ell*(ell+k)+1),
          beta**2*(Dstar*Dstar-M*M*(1+Delta*c*c)),
          b*b*L*L*((V+u)**2-Delta*(f*f-1)*u*(2*V+u)-1),
          b*b*(f*f-1-Delta*I*I)]
degrees=[]; monomials=[]
for name,formula in zip(p['residuals'],expected):
    if env[name]!=formula: raise ValueError('Residual mismatch: '+name)
    if any(min(m)<0 or c.denominator!=1 for m,c in formula.t.items()):
        raise ValueError('Uncancelled rational or Laurent term: '+name)
    degrees.append(formula.degree()); monomials.append(len(formula.t))

want=-9*beta**2*i**2*(eta+zeta)**4*X**2*Y**6
if env['As'].leading()!=want: raise ValueError('Wrong strong leading form')
if degrees!=[13,13,13,14]: raise ValueError('Wrong degrees: '+str(degrees))

# Independent abstract symbols for suffix verification, avoiding a large square.
small=dict(zip(p['residuals'],[symbols[n] for n in NAMES[:4]]))
for name,op,x,y in p['source']:
    if name in small: continue
    if x in small and y in small:
        aa,bb=small[x],small[y]
        small[name]={'+':lambda:aa+bb,'-':lambda:aa-bb,'*':lambda:aa*bb}[op]()
if small[p['output']]!=sum(symbols[n]**2 for n in NAMES[:4]):
    raise ValueError('Wrong sum-of-squares suffix')

needed={p['output']}
for name,op,x,y in reversed(p['source']):
    if name not in needed: raise ValueError('Dead operation: '+name)
    needed.update((x,y))
if not set(p['witnesses'])<=needed: raise ValueError('Dead witness')
counts=dict(collections.Counter(row[1] for row in p['source']))
result={
    'packet_sha256':hashlib.sha256(PACKET.read_bytes()).hexdigest(),
    'identity_checks':'all four exact residuals match independent rational-normalized formulas',
    'residual_degrees':degrees,
    'residual_monomials_with_symbolic_coefficient_ports':monomials,
    'single_polynomial_exact_degree':28,
    'strong_leading_form':'-9 beta^2 i^2 (eta+zeta)^4 X^2 Y^6',
    'polynomial_leading_form':'81 beta^4 i^4 (eta+zeta)^8 X^4 Y^12',
    'operations':len(p['source']),
    'operation_breakdown':counts,
    'all_witnesses_live':True,
    'sum_of_squares_suffix':'exact',
    'scope':'finite exact algebra only; universal mathematics reviewed separately',
    'dependencies':'Python standard library only',
}
(HERE/'independent_algebra.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
