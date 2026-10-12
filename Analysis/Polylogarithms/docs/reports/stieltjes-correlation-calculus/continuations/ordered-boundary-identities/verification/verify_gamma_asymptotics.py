#!/usr/bin/env python3
"""Optional Gamma-determinant asymptotic diagnostics at 60 digits.

Requirements: Python 3.10+, mpmath, and SymPy.
Run this script from any directory. It writes gamma_asymptotic_results.json
beside itself. Gamma normalization is computed by quadrature; canonical
recurrence determinants are computed over the exact rationals. Numerical
ratios are diagnostics, not interval certificates.

Precision correction: the power (2*b)^(-D_m) is evaluated as an mpmath
number, avoiding an intermediate Python binary float used during early
exploration. The distributed results were regenerated with this correction.
"""
from pathlib import Path
import json
import mpmath as mp
import sympy as s
from math import factorial
mp.mp.dps=60
out=[]
for m in (1,2,3):
    W=lambda x: abs(mp.gamma(mp.mpf(1)/4+mp.j*x/2))**(4*m)
    funcs=[lambda x,k=k:mp.sinh(mp.pi*k*x) for k in range(m-1,0,-1)]+[lambda x:mp.tanh(mp.pi*x)]
    T=mp.matrix(m,m)
    for n in range(1,m+1):
      for j,P in enumerate(funcs):
        T[n-1,j]=4*mp.quad(lambda x:mp.im((x+mp.j/2)**(2*n))*P(x)*W(x),[0,mp.mpf('.5'),1,2,4,8,mp.inf])/mp.factorial(2*n)
    K=abs(mp.det(T))
    xs=[(mp.pi*j)**(-2) for j in range(1,m+1)]
    A0=2**m*(2*mp.pi)**(2*m)
    L=[]
    for j in range(1,m+1):
      aa=A0 if j==m else A0/2
      rr=mp.pi*j
      L.append(4*aa*rr**(m-1) if j%2 else 2*m*aa*rr**m)
    const=mp.fprod(L)*mp.fprod(xs)*mp.fprod(xs[i]-xs[j] for i in range(m) for j in range(i+1,m))/K
    power=m*m+m//2
    sig=(-1)**(m*m//4)
    base=mp.pi**(2*m)*mp.factorial(m)**2
    stop=120
    beta=[0]+[2*abs(s.bernoulli(2*k))/factorial(2*k) for k in range(1,stop+m+1)]
    aa=lambda n:s.Rational(factorial(2*n),factorial(2*n-2*m)) if n>m else 0
    bb=lambda n:s.Rational(factorial(2*n-1),factorial(2*n-2*m-1))
    C={n:[s.Integer(n==j) for j in range(1,m+1)] for n in range(1,m+1)}
    records=[]
    for n in range(m+1,stop+m+1):
      C[n]=[sum(beta[n-r]*(aa(r)+bb(n))*C[r][j] for r in range(1,n))/(2*(aa(n)+bb(n))) for j in range(m)]
      b=n-m
      if b in (20,40,80,120):
        det=s.Matrix([C[k] for k in range(b+1,b+m+1)]).det()
        detmp=mp.mpf(str(det.p))/mp.mpf(str(det.q))
        approx=sig*const*mp.mpf(2*b)**(-power)*base**(-b)
        ratio=detmp/approx
        print(m,b,mp.nstr(ratio,20),flush=True)
        records.append({'b':b,'ratio':mp.nstr(ratio,40)})
    out.append({'m':m,'decimal_precision':60,'diagnostic_status':'floating-point comparison; not an interval certificate','precision_correction':'(2*b)^(-D_m) evaluated in mpmath; results regenerated after removing an intermediate binary float','initial_matrix':[[mp.nstr(T[i,j],50) for j in range(m)] for i in range(m)],'positive_initial_determinant':mp.nstr(K,50),'asymptotic_constant':mp.nstr(const,50),'records':records})
Path(__file__).with_name('gamma_asymptotic_results.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
