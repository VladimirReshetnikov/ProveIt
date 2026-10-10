"""Rigorous rational-rectangle certificates for the midpoint moment evaluator.

Uses only Python integer/rational arithmetic for enclosures. Zeta values are
bounded by a proved Euler-transform tail; sqrt(3) by integer square roots.
The analytic tail is bounded separately. No floating-point decision is used.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from math import lcm, isqrt
from pathlib import Path
from functools import lru_cache
import json
from gap_reduce import centered_moments

ROOT=Path(__file__).resolve().parents[1]

@dataclass(frozen=True)
class Interval:
    lo: F
    hi: F
    def __post_init__(self):
        if self.lo>self.hi: raise ValueError('reversed interval')
    def __add__(self, other):
        if not isinstance(other,Interval): other=Interval(F(other),F(other))
        return Interval(self.lo+other.lo,self.hi+other.hi)
    __radd__=__add__
    def scale(self,x:F):
        return Interval(self.lo*x,self.hi*x) if x>=0 else Interval(self.hi*x,self.lo*x)
    def mul(self,other):
        e=[self.lo*other.lo,self.lo*other.hi,self.hi*other.lo,self.hi*other.hi]
        return Interval(min(e),max(e))
    def widen(self,e:F): return Interval(self.lo-e,self.hi+e)

@dataclass(frozen=True)
class Quad:
    """An exact element a+b sqrt(d) of Q(sqrt(d)), d=-1 or -3."""
    a:F
    b:F
    d:int
    def __add__(self, other):
        if not isinstance(other,Quad): other=Quad(F(other),F(0),self.d)
        if self.d!=other.d: raise ValueError('different fields')
        return Quad(self.a+other.a,self.b+other.b,self.d)
    __radd__=__add__
    def __mul__(self, other):
        if not isinstance(other,Quad): other=Quad(F(other),F(0),self.d)
        if self.d!=other.d: raise ValueError('different fields')
        return Quad(self.a*other.a+self.d*self.b*other.b,
                    self.a*other.b+self.b*other.a,self.d)
    __rmul__=__mul__
    def inverse(self):
        n=self.a*self.a-self.d*self.b*self.b
        if not n: raise ZeroDivisionError()
        return Quad(self.a/n,-self.b/n,self.d)

@lru_cache(maxsize=None)
def zeta_interval(s:int, terms:int)->Interval:
    if s<2 or terms<1: raise ValueError('s>=2, terms>=1 required')
    common=1
    for n in range(1,terms+1): common=lcm(common,n)
    den=common**s
    row=[den//n**s for n in range(1,terms+1)]
    acc=0
    for _ in range(terms):
        assert 0<=row[0]<=den
        acc=2*acc+row[0]
        row=[row[j]-row[j+1] for j in range(len(row)-1)]
    eta=F(acc,den*2**terms)
    factor=1-F(1,2**(s-1))
    return Interval(eta/factor,(eta+F(1,2**terms))/factor)


def root_data(root:str):
    if root=='i': return Quad(F(0),F(1),-1),F(1,2),F(1)
    if root=='rho_bar': return Quad(F(-1,2),F(-1,2),-3),F(2,5),F(4,5)
    raise ValueError(root)


def coefficient_vector(a:int,b:int,root:str,terms:int):
    z,_,_=root_data(root)
    alpha=z*(Quad(F(1)-z.a/2,-z.b/2,z.d).inverse())
    vectors=centered_moments(a,b,terms)
    keys=sorted({j for v in vectors for j in v})
    out={j:Quad(F(0),F(0),z.d) for j in keys}
    for vec in reversed(vectors):
        for j in keys: out[j]=out[j]*alpha+vec.get(j,F(0))
    return {j:x*alpha for j,x in out.items()}


def decimal_outward(x:F,digits:int,upper:bool=False)->str:
    scale=10**digits
    n=(-((-x.numerator*scale)//x.denominator) if upper else (x.numerator*scale)//x.denominator)
    # ceil(x)= -floor(-x), expressed with exact signed integer division.
    sign='-' if n<0 else ''
    n=abs(n)
    return f'{sign}{n//scale}.{n%scale:0{digits}d}'


def pack_interval(x:Interval)->dict:
    return {'lo':[str(x.lo.numerator),str(x.lo.denominator)],
            'hi':[str(x.hi.numerator),str(x.hi.denominator)],
            'decimal_lower':decimal_outward(x.lo,100),
            'decimal_upper':decimal_outward(x.hi,100,True),
            'width_upper_100dp':decimal_outward(x.hi-x.lo,100,True)}


def make_certificate(a:int,b:int,root:str,terms:int=240,zeta_terms:int=700)->dict:
    z,q,amajor=root_data(root)
    coeff=coefficient_vector(a,b,root,terms)
    zz={j:zeta_interval(j,zeta_terms) for j in coeff if j}
    re=Interval(F(0),F(0)); im=Interval(F(0),F(0))
    for j,c in coeff.items():
        value=zz[j] if j else Interval(F(1),F(1))
        re=re+value.scale(c.a)
        im=im+value.scale(c.b)
    if z.d==-3:
        scale=10**240; n=isqrt(3*scale*scale)
        sq=Interval(F(n,scale),F(n+1,scale))
        assert sq.lo**2<=3<=sq.hi**2
        im=im.mul(sq)
    # mu([0,1])=K_ab(1)<=K_11(1)=1.
    error=amajor*q**terms/(1-q)
    re=re.widen(error); im=im.widen(error)
    assert re.hi-re.lo<F(1,10**70) and im.hi-im.lo<F(1,10**70)
    return {'a':a,'b':b,'root':root,'midpoint_terms':terms,
            'zeta_euler_terms':zeta_terms,'tail_bound':[str(error.numerator),str(error.denominator)],
            'real':pack_interval(re),'imag':pack_interval(im),
            'coefficients':{str(j):{'a':[str(c.a.numerator),str(c.a.denominator)],
                                   'b':[str(c.b.numerator),str(c.b.denominator)]} for j,c in coeff.items()}}


def main():
    out=[]
    for a,b,root in [(1,1,'i'),(4,1,'i'),(5,1,'i'),(1,1,'rho_bar'),(4,1,'rho_bar'),(5,1,'rho_bar')]:
        cert=make_certificate(a,b,root)
        out.append(cert)
        print(a,b,root,'Re',cert['real']['decimal_lower'][:64],
              'Im',cert['imag']['decimal_lower'][:64],flush=True)
    (ROOT/'verification'/'rational_certificates.json').write_text(json.dumps({
        'method':'exact rational midpoint moments; Euler-transformed zeta bounds; analytic geometric tail',
        'certificates':out},indent=2)+'\n')

if __name__=='__main__': main()
