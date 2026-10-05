"""Exact replay of formal recurrence and independent endpoint-ratio conversion."""
import sys,json,sympy as S
from pathlib import Path
BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(BASE))
import derive_tree as d
x,k,t=d.x,d.k,d.t
a=S.symbols('a');M=9
d.M=M
source=json.load(open(BASE/'formal_9.json'))
endpoint=json.load(open(BASE/'endpoint_9.json'))
def req(condition,label):
 if not condition:raise RuntimeError(label)
def zero(expr):return S.expand(expr)==0
def series(expr,n=M):return S.series(expr,t,0,n+1).removeO().expand()
fs=[[S.sympify(v) for v in p] for p in source['f']];sig=[S.sympify(v) for v in source['sigma']]
for j,fp in enumerate(fs):
 req(zero(fp[1].subs(x,0)),f'boundary f{j}')
 if j:req(zero((fp[0]+S.diff(fp[1],x)).subs(x,0)),f'gauge f{j}')
u=d.ratseries((3+x*t*t+t**3)/(3+3*x*t*t-3*t**3),M)
v=d.ratseries((3+x*t*t+t**3)/(3+x*t*t-t**3),M)
minus=d.fullshift(fs,1,-1,M);plus=d.fullshift(fs,1,1,M)
rhs=[d.sumseries(d.mul(u,c,M),d.mul(v,b,M)) for c,b in zip(minus,plus)]
for comp in range(2):
 for z in range(M+1):
  lhs=sum(sig[z-j]*fs[j][comp] for j in range(len(fs)) if 0<=z-j<len(sig))
  req(zero(rhs[comp][z]-lhs),f'recurrence coefficient {comp},{z}')
print('PASS exact boundary, derivative gauge, and every polynomial-pair recurrence coefficient through t^9',flush=True)
# Rebuild endpoint series directly from derivative pairs at x=0.
E=0
for j,fp0 in enumerate(fs):
 fp=fp0
 for p in range(M-1-j):
  E+=fp[1].subs(x,0)*t**(j+p-1)/S.factorial(p)
  fp=d.D(fp)
E=series(E,M-3)
req(zero(E-S.sympify(endpoint['E'])),'endpoint Taylor formula')
st=sum(sig[j]*t**j for j in range(len(sig)))
st1=series(sum(sig[j]*t**j*(1-t**3)**(-S.Rational(j,3)) for j in range(len(sig))))
t2=t*(1-2*t**3)**(-S.Rational(1,3))
Et2=series(E.subs(t,t2))
qr=series(st*st1/4*(1-2*t**3)**S.Rational(1,3)*E/Et2*(3-4*t**3)/(3+2*t**3))
for z,w in enumerate(endpoint['ratio']):
 actual=S.simplify(qr.coeff(t,z).subs(k,S.Rational(2,3)**S.Rational(2,3)*a)*2**(-S.Rational(z,3)))
 req(S.simplify(actual-S.sympify(w))==0,f'direct endpoint ratio coefficient {z}')
print('PASS direct two-step endpoint-ratio conversion including exact (3n-2)/(3n+1) factor through n^(-3)',flush=True)
print('These are exact finite algebra certificates; all-depth analytic validity requires the separate proof and audit.')
