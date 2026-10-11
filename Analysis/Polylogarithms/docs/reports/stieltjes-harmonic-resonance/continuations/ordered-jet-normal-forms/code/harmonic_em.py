"""Numerical harmonic cutoff constants via a recursive Euler--Maclaurin expansion.

This is a floating-point diagnostic, NOT interval arithmetic or a proof engine.
A word is a tuple of (positive power, nonnegative logarithmic power) letters.
The expansion is in x=N+a, and its polynomial constant is normalized at log x=0.
"""
from __future__ import annotations
from functools import lru_cache
from math import factorial
from typing import Dict, Tuple
import mpmath as mp

Letter = Tuple[int,int]
Word = Tuple[Letter,...]
Expansion = Dict[Tuple[int,int],mp.mpf] # x^(-p) log(x)^q

def add(A: Expansion, B: Expansion, factor=1) -> Expansion:
    C=dict(A)
    for k,v in B.items():
        C[k]=C.get(k,mp.mpf(0))+factor*v
        if not C[k]: del C[k]
    return C

def shift(A: Expansion,p: int=0,q: int=0,M: int=100) -> Expansion:
    return {(i+p,j+q):v for (i,j),v in A.items() if i+p<=M}

def derivative(A: Expansion,M: int) -> Expansion:
    B={}
    for (p,q),v in A.items():
        if p+1>M: continue
        if p:B[(p+1,q)]=B.get((p+1,q),mp.mpf(0))-p*v
        if q:B[(p+1,q-1)]=B.get((p+1,q-1),mp.mpf(0))+q*v
    return {k:v for k,v in B.items() if v}

def integral(A: Expansion,M: int) -> Expansion:
    B={}
    for (p,q),v in A.items():
        if p==1:
            B[(0,q+1)]=B.get((0,q+1),mp.mpf(0))+v/(q+1)
        elif p>1 and p-1<=M:
            for j in range(q+1):
                c=v*((-1)**j)*factorial(q)/factorial(q-j)/mp.mpf(1-p)**(j+1)
                k=(p-1,q-j);B[k]=B.get(k,mp.mpf(0))+c
        else:
            raise ValueError('The summation integrand must have p>=1.')
    return {k:v for k,v in B.items() if v}

def evaluate(A: Expansion,x) -> mp.mpf:
    x=mp.mpf(x);L=mp.log(x)
    return mp.fsum(v*x**(-p)*L**q for (p,q),v in A.items())

def multiply(A: Expansion,B: Expansion,M: int) -> Expansion:
    C={}
    for (p,q),u in A.items():
        for (r,s),v in B.items():
            if p+r<=M:
                k=(p+r,q+s);C[k]=C.get(k,mp.mpf(0))+u*v
    return {k:v for k,v in C.items() if v}

def euler_primitive(f: Expansion,M: int) -> Expansion:
    """Integral f - f/2 + sum B_(2r) f^(2r-1)/(2r)!; zero constant."""
    out=add(integral(f,M),{k:v for k,v in f.items() if k[0]<=M},-mp.mpf('0.5'))
    df=derivative(f,M)
    r=1
    while df:
        out=add(out,df,mp.bernoulli(2*r)/mp.factorial(2*r))
        df=derivative(derivative(df,M),M);r+=1
    return out

class HarmonicEM:
    def __init__(self,a=1,N: int=64,M: int=40):
        self.a=mp.mpf(a);self.N=N;self.M=M
        if self.a<=0 or N<2 or M<2:raise ValueError('Require a>0, N>=2, M>=2.')

    @lru_cache(None)
    def finite_values(self,w: Word):
        if not w:return tuple(mp.mpf(1) for _ in range(self.N+1))
        k,m=w[0]
        if k<1 or m<0:raise ValueError('Invalid letter.')
        tail=self.finite_values(w[1:]);vals=[mp.mpf(0)]
        for n in range(self.N):
            x=self.a+n
            vals.append(vals[-1]+mp.log(x)**m/x**k*tail[n])
        return tuple(vals)

    @lru_cache(None)
    def result(self,w: Word):
        if not w:return mp.mpf(1),{(0,0):mp.mpf(1)}
        _,tail=self.result(w[1:]);k,m=w[0]
        f=shift(tail,k,m,self.M+1)
        asym=euler_primitive(f,self.M)
        value=self.finite_values(w)[-1]-evaluate(asym,self.N+self.a)
        full=add(asym,{(0,0):value})
        return value,full

    def R(self,w: Word):return self.result(w)[0]

    def summable_from_asym(self,finite_terms,asym: Expansion):
        """Sum finite n<N terms plus the EM tail of an integrable asymptotic."""
        if any(p<=1 for p,q in asym):raise ValueError('Use only summable asymptotics.')
        primitive=euler_primitive(asym,self.M)
        return mp.fsum(finite_terms)-evaluate(primitive,self.N+self.a)

    def commutator_series(self,p: int,q: int):
        if p<0 or q<0:raise ValueError('Nonnegative indices required.')
        g={m:self.R(((1,m),)) for m in {p,q,p+q+1}}
        vals={m:self.finite_values(((1,m),)) for m in {p,q}}
        kappa=mp.mpf(1)/(q+1)-mp.mpf(1)/(p+1)
        terms=[]
        for n in range(self.N):
            x=self.a+n;L=mp.log(x)
            terms.append((L**q*(g[p]-vals[p][n])-L**p*(g[q]-vals[q][n])-kappa*L**(p+q+1))/x)
        # gamma_m(x)=gamma_m(a)-finite harmonic moment through n<N.
        gp=add({(0,0):g[p]},self.result(((1,p),))[1],-1)
        gq=add({(0,0):g[q]},self.result(((1,q),))[1],-1)
        asym=add(shift(gp,1,q,self.M+1),shift(gq,1,p,self.M+1),-1)
        asym=add(asym,{(1,p+q+1):-kappa})
        # Drop numerically tiny residues of exact polynomial cancellations.
        asym={k:v for k,v in asym.items() if k[0]>1}
        return kappa*g[p+q+1]+self.summable_from_asym(terms,asym)

    def xi_series(self):
        g0=self.R(((1,0),));g1=self.R(((1,1),))
        hvals=self.finite_values(((1,0),));jvals=self.finite_values(((1,1),))
        terms=[]
        for n in range(self.N):
            x=self.a+n;L=mp.log(x);H=hvals[n];J=jvals[n]
            b0=g0-H-1/x+L
            b1=-(g1-J)+L/x-L**2/2
            terms.append(((-b1-2*L*b0)*H+b0*J)/x)
        H=self.result(((1,0),))[1];J=self.result(((1,1),))[1]
        b0=add(add({(0,0):g0,(1,0):-mp.mpf(1),(0,1):mp.mpf(1)},H,-1),{})
        b1=add(J,{(0,0):-g1,(1,1):mp.mpf(1),(0,2):-mp.mpf('0.5')})
        b0={k:v for k,v in b0.items() if k[0]>=1}
        b1={k:v for k,v in b1.items() if k[0]>=1}
        first=add({k:-v for k,v in b1.items()},shift(b0,0,1,self.M),-2)
        asym=shift(add(multiply(first,H,self.M),multiply(b0,J,self.M)),1,0,self.M+1)
        return self.summable_from_asym(terms,asym)

if __name__=='__main__':
    mp.mp.dps=70
    eng=HarmonicEM()
    for m in range(4):
        got=eng.R(((1,m),));expected=mp.stieltjes(m)
        print('gamma',m,mp.nstr(got,55),'error',mp.nstr(got-expected,5))
    X=(1,0);Y=(1,1);Z=(1,2)
    for p,q in [(0,1),(0,2),(0,3),(1,2)]:
        direct=eng.R(((1,p),(1,q)))-eng.R(((1,q),(1,p)))
        series=eng.commutator_series(p,q)
        print('C',p,q,mp.nstr(direct,50),'difference',mp.nstr(direct-series,5))
    theta=eng.R((Y,X,X))-2*eng.R((X,Y,X))+eng.R((X,X,Y))
    om2=eng.R((X,Z))-eng.R((Z,X))
    rhs=eng.xi_series()+mp.mpf('1.5')*eng.R((Z,X))-eng.R((Y,Y))
    # h20=R(ZX)/2, hence correction 3/2 R(ZX)-R(YY).
    print('theta',mp.nstr(theta,50),'xi difference',mp.nstr(theta-rhs,5))
