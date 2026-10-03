#!/usr/bin/env python3
"""Exact fixed-order algorithm in article.tex, Section 6. Requires SymPy."""
import argparse, json, sys
from pathlib import Path
import sympy as s
from sympy.functions.combinatorial.numbers import stirling

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('order',type=int,nargs='?',default=4)
parser.add_argument('--output-dir',type=Path,default=Path('replay-output'))
args=parser.parse_args()
M=args.order
if M<0: parser.error('order must be nonnegative')
OUT=args.output_dir.resolve();OUT.mkdir(parents=True,exist_ok=True)
r,c,j,k,z=s.symbols('r c j k z')
ROOT=Path(__file__).resolve().parent

def ff(x,n): return s.prod(x-i for i in range(n))
def mul(a,b):
    return [s.expand(sum(a[i]*b[n-i] for i in range(n+1))) for n in range(M+1)]
def expser(a):
    out=[s.Integer(1)]
    for n in range(1,M+1): out.append(s.expand(sum(i*a[i]*out[n-i] for i in range(1,n+1))/n))
    return out
def Spow(m,p):
    # sum i^p for i=0,...,m-1
    return s.expand((s.bernoulli(p+1,m)-s.bernoulli(p+1))/(p+1))
def fact_ratio(a,b):
    return expser([0]+[-(Spow(a,h)-2*Spow(b,h))/h for h in range(1,M+1)])
def power_coefs(base,p,N):
    # Polynomial exponent p; formal base[0]=1.
    u=sum(base[q]*z**q for q in range(1,N+1))
    out=[]
    for q in range(N+1):
        out.append(s.expand(sum(ff(p,l)/s.factorial(l)*s.expand(u**l).coeff(z,q) for l in range(q+1))))
    return out

Abase=[s.Integer(1)]+[s.bernoulli(q)*r**q/s.factorial(q) for q in range(1,M+1)]
if M: Abase[1]=r/2
a=power_coefs(Abase,j+1,M)

def Hj(shift):
    out=[s.Integer(0)]*(M+1)
    for q in range(M+1):
        e=expser([0]+[sum((shift+i)**h for i in range(q))/h for h in range(1,M+1)])
        for m in range(q,M+1): out[m]+=a[q]*ff(j,q)*e[m-q]
    return [s.expand(x) for x in out]

def binmom(expr):
    p=s.Poly(s.expand(expr),j)
    return s.expand(sum(co*sum(stirling(deg[0],b,kind=2)*ff(c,b)/2**b for b in range(deg[0]+1)) for deg,co in p.terms()))
def poismom(expr,var,mu):
    p=s.Poly(s.expand(expr),var)
    return s.expand(sum(co*sum(stirling(deg[0],b,kind=2)*mu**b for b in range(deg[0]+1)) for deg,co in p.terms()))

Jbase=[2/s.factorial(q+2) if q%2==0 else s.Integer(0) for q in range(M+1)]
Cd=power_coefs(Jbase,c,M)
D=[s.Integer(0)]*(M+1)
for d in range(0,M+1,2):
    print('inner defect',d,flush=True)
    h=Hj(c+d)
    hh=mul(h,[x.subs(j,c-j) for x in h])
    prod=mul(fact_ratio(2*c+d,c+d),hh)
    for m in range(d,M+1):
        D[m]+=poismom(s.expand(Cd[d]*r**(2*d)*binmom(prod[m-d])),c,-r*r)
D=[s.factor(x) for x in D]

def configs(a,l=3):
    if a==0:
        yield {}
    elif l-2<=a:
        for mult in range(a//(l-2)+1):
            for rest in configs(a-mult*(l-2),l+1):
                yield ({l:mult} if mult else {}) | rest

U=[s.Integer(0)]*(M+1)
for excess in range(M+1):
    for cfg in configs(excess):
        L=sum((l-1)*v for l,v in cfg.items())
        weight=s.Integer(2)**L*ff(k,L)/s.prod(l**v*s.factorial(v) for l,v in cfg.items())
        fr=fact_ratio(2*k-excess,k)
        for m in range(excess,M+1): U[m]+=weight*fr[m-excess]
U=[s.factor(x) for x in U]
Qshift=[]
for m in range(M+1):
    Qshift.append(s.expand(sum(D[i]*(s.binomial(m-1,m-i)*k**(m-i) if i else (1 if m==0 else 0)) for i in range(m+1))))
raw=mul(U,Qshift)
B=[s.factor(poismom(x,k,r*r/2)) for x in raw]
out={'order':M,'D':[str(x) for x in D],'U':[str(x) for x in U],'B':[str(x) for x in B],
     'B_numeric':[str(s.N(x.subs(r,s.log(2)),60)) for x in B]}
(OUT/f'coefficients-order{M}.json').write_text(json.dumps(out,indent=2)+'\n')
for label,arr in [('D',D),('U',U),('B',B)]:
    for i,x in enumerate(arr): print(f'{label}_{i} = {x}',flush=True)
