#!/usr/bin/env python3
"""Read-only exact certificates for Report295 (Python 3.10+, standard library).

The analytic theorems are proved in the paper. This program checks complete
formal polynomial identities, exact rational radical enclosures, and labeled
finite examples. It is not an arbitrary-gamma quintic norm solver.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
import argparse
from collections import defaultdict
from fractions import Fraction
from hashlib import sha256
from itertools import product
import json
from math import isqrt, comb
from pathlib import Path
from types import MappingProxyType

MAX_BITS = 16384
MAX_TERMS = 12000
MAX_PAIRS = 2000000


def require(condition, message):
    if type(condition) is not bool or type(message) is not str:
        raise ValueError('require needs bool and str')
    if not condition:
        raise RuntimeError(message)


def integer(value, name='integer'):
    if type(value) is not int or value.bit_length() > MAX_BITS:
        raise ValueError(name + ' must be a bounded integer, not bool')
    return value


def rational(value):
    if type(value) not in (int, Fraction):
        raise ValueError('an exact integer or Fraction is required')
    if max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > MAX_BITS:
        raise ValueError('rational exceeds 16384-bit numerator/denominator bound')
    return Fraction(value)


class Polynomial:
    """Bounded sparse Q-polynomials. Adapted from the Report294 exact companion.

    Every monomial coefficient is compared; no interpolation or sampling.
    The public coefficient mapping is immutable. All interfaces reject floats.
    """
    __slots__ = ('_terms',)

    def __init__(self, terms=None):
        if terms is None:
            terms = {}
        if type(terms) is not dict or len(terms) > MAX_TERMS:
            raise ValueError('polynomial needs a dictionary of at most 12000 terms')
        clean = {}
        for monomial, coefficient in terms.items():
            if (type(monomial) is not tuple or len(monomial) > 32
                    or any(type(v) is not str or not v.isidentifier() or len(v) > 24 for v in monomial)
                    or tuple(sorted(monomial)) != monomial):
                raise ValueError('sorted variable-name tuples of degree at most 32 required')
            c = rational(coefficient)
            if c:
                clean[monomial] = c
        if len({v for mon in clean for v in mon}) > 32:
            raise ValueError('at most 32 variables are supported')
        self._terms = MappingProxyType(clean)

    @property
    def terms(self):
        return self._terms

    @classmethod
    def variable(cls, name):
        return cls({(name,): 1})

    @classmethod
    def constant(cls, value):
        return cls({(): value})

    @staticmethod
    def coerce(value):
        if type(value) is Polynomial:
            return value
        return Polynomial.constant(rational(value))

    def __add__(self, other):
        other = self.coerce(other)
        terms = dict(self.terms)
        for mon, value in other.terms.items():
            terms[mon] = terms.get(mon, 0) + value
        return Polynomial(terms)
    __radd__ = __add__

    def __neg__(self):
        return Polynomial({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) + (-self)

    def __mul__(self, other):
        other = self.coerce(other)
        if len(self.terms)*len(other.terms) > MAX_PAIRS:
            raise ValueError('polynomial multiplication exceeds pair budget')
        if self.terms and other.terms and max(map(len, self.terms))+max(map(len, other.terms)) > 32:
            raise ValueError('polynomial product degree exceeds 32')
        terms = defaultdict(Fraction)
        for m, a in self.terms.items():
            for n, b in other.terms.items():
                terms[tuple(sorted(m+n))] += a*b
        return Polynomial(dict(terms))
    __rmul__ = __mul__

    def __truediv__(self, other):
        other = rational(other)
        if not other:
            raise ValueError('division requires a nonzero rational scalar')
        return self*(1/other)

    def __pow__(self, exponent):
        integer(exponent)
        if not 0 <= exponent <= 32:
            raise ValueError('exponent must be 0..32')
        out = Polynomial.constant(1)
        for _ in range(exponent):
            out *= self
        return out

    def __eq__(self, other):
        if type(other) in (int, Fraction):
            other = self.constant(other)
        return type(other) is Polynomial and self.terms == other.terms

    def derivative(self, variable):
        Polynomial.variable(variable)
        terms = {}
        for mon, c in self.terms.items():
            n = mon.count(variable)
            if n:
                shorter = list(mon)
                shorter.remove(variable)
                terms[tuple(shorter)] = n*c
        return Polynomial(terms)

    def evaluate(self, values):
        variables = {v for mon in self.terms for v in mon}
        if type(values) is not dict or set(values) != variables:
            raise ValueError('evaluation needs exactly the polynomial variables')
        values = {k: rational(v) for k, v in values.items()}
        total = Fraction(0)
        for mon, c in self.terms.items():
            for v in mon:
                c *= values[v]
            total += c
        return rational(total)


P = Polynomial.variable


def substitute(poly, variable, value):
    """Exact formal substitution, without evaluation or interpolation."""
    poly = Polynomial.coerce(poly)
    Polynomial.variable(variable)
    value = Polynomial.coerce(value)
    out = Polynomial.constant(0)
    for mon, coefficient in poly.terms.items():
        rest = tuple(v for v in mon if v != variable)
        out += Polynomial({rest: coefficient}) * value**mon.count(variable)
    return out


def coefficient(poly, variable, power):
    integer(power)
    Polynomial.variable(variable)
    if power < 0:
        raise ValueError('negative coefficient power')
    return Polynomial({tuple(v for v in mon if v != variable): c
                       for mon, c in poly.terms.items() if mon.count(variable) == power})


def verify_identity(label, lhs, rhs=0):
    if type(label) is not str or not label:
        raise ValueError('a nonempty identity label is required')
    require(Polynomial.coerce(lhs) == Polynomial.coerce(rhs), 'false polynomial identity: '+label)
    return label


def polynomial_checks():
    checked = []
    def check(label, lhs, rhs=0):
        checked.append(verify_identity(label, lhs, rhs))
    C, g, mu, x, r, h, d, K = map(P, ('C', 'g', 'mu', 'x', 'r', 'h', 'd', 'K'))
    f = (C-1)*x**4+4*g*mu*x**3-6*g**2*mu**2*x**2+4*g**3*mu**3*x
    check('fixed-mean quartic expansion', C*x**4-(x-g*mu)**4, f-g**4*mu**4)
    fp = f.derivative('x')
    check('stationary cubic', fp, 4*(C-1)*x**3+12*g*mu*x**2-12*g**2*mu**2*x+4*g**3*mu**3)
    check('Vieta numerator', coefficient(fp, 'x', 2), 12*g*mu)
    check('Vieta denominator', coefficient(fp, 'x', 3), 4*(C-1))
    # n=3: root sum=3mu implies 3mu(C-1+g)=0; the paper uses mu!=0,C>1,g>0.
    check('three-singleton contradiction factor', 3*mu*(C-1)+3*g*mu, 3*mu*(C-1+g))
    U,V,j,l,a = map(P, ('U','V','j','l','a'))
    rootpoly = 4*a*x*(x-U)*(x-U-V)
    deriv = rootpoly.derivative('x')
    curvatures = [substitute(deriv,'x',rr) for rr in (0,U,U+V)]
    for idx, expected in enumerate((4*a*U*(U+V), -4*a*U*V, 4*a*V*(U+V))):
        check('root curvature '+str(idx+1), curvatures[idx], expected)
    check('sum-zero Hessian tangent', -V+(U+V)-U)
    # Multiply by jl to avoid division by formal multiplicities.
    lhs = l*curvatures[0]*V**2 + j*l*curvatures[1]*(U+V)**2 + j*curvatures[2]*U**2
    rhs = 4*a*U*V*(U+V)*(l*V-j*l*(U+V)+j*U)
    check('Hessian contradiction cleared identity', lhs, rhs)
    check('Hessian sign decomposition', l*V-j*l*(U+V)+j*U, -l*V*(j-1)-j*U*(l-1))
    num=2*(1+(1-g)*mu)**4+(-2+(1-g)*mu)**4
    den=2*(1+mu)**4+(-2+mu)**4
    check('strict-norm directional derivative', substitute(num.derivative('mu')*den-num*den.derivative('mu'),'mu',0), 432*g)
    # Actual integer centered coordinates v=(n-k,-k). Divide by variance only after clearing.
    n,k,t,s = map(P, ('n','k','t','s'))
    q=k*(n-k); M=n*n-3*n*k+3*k*k
    moments = [n, 0, n*q, n*q*(n-2*k), n*q*M]
    for power in range(5):
        check('integer two-point moment '+str(power), k*(n-k)**power+(n-k)*(-k)**power, moments[power])
    check('normalized fourth moment relation', M, q+(n-2*k)**2)
    D=r**4+6*r*r+4*d*r+K
    N=h**4*r**4+6*h*h*r*r+4*h*d*r+K
    G=(3*h*h*(h+1)*r**5+3*d*h*(h*h+h+1)*r**4+K*(h+1)*(h*h+1)*r**3
       +6*d*h*r*r+3*K*(h+1)*r+K*d)
    # Build both fourth moments by an independent binomial moment functional.
    em=(1,0,1,d,K)
    for name,scale,target in (('denominator',1,D),('numerator',h,N)):
        check('moment-generated '+name, sum((comb(4,i)*(scale*r)**(4-i)*em[i] for i in range(5)),Polynomial.constant(0)), target)
    check('stationary quintic identity', N.derivative('r')*D-N*D.derivative('r'), 4*(h-1)*G)
    check('centering cubic', substitute(G,'h',0), K*(r**3+3*r+d))
    check('reflection quartic', substitute(G,'h',-1), d*(K-6*r*r-3*r**4))
    check('balanced reflection degeneracy', substitute(substitute(G,'h',-1),'d',0))
    check('degeneracy linear coefficient', coefficient(G,'r',1), 3*K*(h+1))
    check('degeneracy constant coefficient', coefficient(G,'r',0), K*d)
    check('all balanced stationary branches', substitute(substitute(G,'d',0),'K',1), (h+1)*r*(3*h*h*r**4+(h*h+1)*r*r+3))
    # The mean-one gap and transition discriminant, entirely polynomial.
    mean_gap=C*(1+6*t*t+4*d*t**3+K*t**4)-(h**4+6*h*h*t*t+4*h*d*t**3+K*t**4)
    check('normalized mean-one gap',mean_gap,(C-1)*K*t**4+4*d*(C-h)*t**3+6*(C-h*h)*t*t+C-h**4)
    W=k*(1+t*(n-k))**4+(n-k)*(1-t*k)**4
    TW=k*(-s+t*(n-k))**4+(n-k)*(-s-t*k)**4
    A=q*M*(s**4-1); B=4*q*(n-2*k)*(s**4+s); E=6*q*s*s*(s*s-1)
    check('constant gap in integer coordinates',s**4*W-TW,n*t*t*(A*t*t+B*t+E))
    disc=B*B-4*A*E
    L=s*s-s+1
    # (s^4+s)=s(s+1)L, eliminating all formal denominators.
    check('transition factor cancellation',s**4+s,s*(s+1)*L)
    check('discriminant beta-minus-F',disc,8*q*q*s*s*(s+1)**2*(2*(n-2*k)**2*L**2-3*M*(s-1)**2*(s*s+1)))
    M1=n*n-3*n+3
    check('strict split maximum', (n-2)**2*M-(n-2*k)**2*M1,n*n*(k-1)*(n-1-k))
    check('reciprocal symmetric threshold', (s-1)**2*(s*s+1),L**2-s*s)
    FN=Fraction(3,2)*(s-1)**2*(s*s+1); FD=L**2
    check('strict threshold derivative',FN.derivative('s')*FD-FN*FD.derivative('s'),3*s*(s-1)*(s+1)*L)
    threshold=(n*n-n+1)*L**2-3*M1*s*s
    check('threshold polynomial',3*M1*(s-1)**2*(s*s+1)-2*(n-2)**2*L**2,threshold)
    check('extremal discriminant',substitute(disc,'k',1),-8*s*s*(n-1)**2*(s+1)**2*threshold)
    check('threshold below n',substitute(threshold,'s',n-1), n*n*(n-2)**2*M1)
    check('radical parameter simplification',3*M1-2*(n-2)**2,n*n-n+1)
    aa,bb,ee=map(P,('aa','bb','ee'))
    check('quadratic equality square',4*aa*(aa*t*t+bb*t+ee),(2*aa*t+bb)**2-(bb*bb-4*aa*ee))
    tt=P('tt')
    check('transition vertex numerator',2*(s**4-1)*K*tt+4*d*(s**4+s),2*((s**4-1)*K*tt+2*d*(s**4+s)))
    u,z=map(P,('u','z'))
    # 4[(u+z)/2]^2-4u[(u+z)/2]+4=z²-u²+4.
    check('outer radical quadratic identity',(u+z)**2-2*u*(u+z)+4,z*z-u*u+4)
    y=P('y')
    scalar_den=r**4+6*r*r+1+d*d
    check('reflection scalar derivative',scalar_den-r*scalar_den.derivative('r'),1+d*d-6*r*r-3*r**4)
    check('reflection critical denominator',y*y+6*y+(6*y+3*y*y),4*y*(y+3))
    GN=3*y*y+6*y-1; GD=y*(y+3)**2
    check('reflection G derivative',GN.derivative('y')*GD-GN*GD.derivative('y'),-3*(y-1)*(y+1)**2*(y+3))
    check('reflection moment simplification',4*k*(n-k)+(n-2*k)**2,n*n)
    check('continuous scalar maximum',2*GN-GD,-(y-1)**2*(y+2))
    check('spike beta algebra', (1-d)*(1+d)+(1+d)**2,2*(1+d))
    # Exact Laurent constant: (z e^{it}+zb e^{-it})^4/16 has only i=2 constant.
    zz,zb=map(P,('zz','zb'))
    check('complex phase-average coefficient',Fraction(comb(4,2),16)*zz**2*zb**2,Fraction(3,8)*(zz*zb)**2)
    # Q[sqrt(6)] identity, remainder of multiplication modulo z²-6.
    product6=(6*z-8)*(3*z+8)
    check('nine-point radical simplification',product6-18*(z*z-6),44+24*z)
    return checked


SQRT_DIGITS=65
DISPLAY_DIGITS=40
MAX_N=1000000


def sqrt_bounds(value, digits=SQRT_DIGITS):
    """Rational endpoints, certified by integer squaring; no approximate sqrt."""
    value=rational(value)
    integer(digits,'sqrt digits')
    if value<0 or not 1 <= digits <= 100:
        raise ValueError('sqrt requires nonnegative rational and 1..100 digits')
    scale=10**digits
    numerator=value.numerator*scale*scale
    denominator=value.denominator
    t=isqrt(numerator//denominator)
    require(t*t*denominator<=numerator<(t+1)*(t+1)*denominator,'integer sqrt certificate failed')
    lo=Fraction(t,scale)
    hi=lo if t*t*denominator==numerator else Fraction(t+1,scale)
    return lo,hi


class Interval:
    """Immutable exact rational interval, with explicit zero/polarity guards."""
    __slots__=('_lo','_hi')
    def __init__(self,lo,hi=None):
        lo=rational(lo); hi=lo if hi is None else rational(hi)
        if lo>hi:
            raise ValueError('interval endpoints reversed')
        object.__setattr__(self,'_lo',lo); object.__setattr__(self,'_hi',hi)
    def __setattr__(self,name,value):
        raise AttributeError('intervals are immutable')
    @property
    def lo(self): return self._lo
    @property
    def hi(self): return self._hi
    @staticmethod
    def coerce(value):
        return value if type(value) is Interval else Interval(value)
    def __add__(self,other):
        other=self.coerce(other); return Interval(self.lo+other.lo,self.hi+other.hi)
    __radd__=__add__
    def __neg__(self): return Interval(-self.hi,-self.lo)
    def __sub__(self,other): return self+-self.coerce(other)
    def __rsub__(self,other): return self.coerce(other)+-self
    def __mul__(self,other):
        other=self.coerce(other)
        values=[a*b for a in (self.lo,self.hi) for b in (other.lo,other.hi)]
        return Interval(min(values),max(values))
    __rmul__=__mul__
    def reciprocal(self):
        if self.lo<=0<=self.hi:
            raise ValueError('interval denominator contains zero')
        return Interval(1/self.hi,1/self.lo)
    def __truediv__(self,other): return self*self.coerce(other).reciprocal()
    def __rtruediv__(self,other): return self.coerce(other)*self.reciprocal()
    def sqrt(self,digits=SQRT_DIGITS):
        if self.lo<0:
            raise ValueError('sqrt interval crosses negative axis')
        return Interval(sqrt_bounds(self.lo,digits)[0],sqrt_bounds(self.hi,digits)[1])
    def bounds(self): return (self.lo,self.hi)


def decimal_bound(q,digits=DISPLAY_DIGITS,upper=False):
    q=rational(q); integer(digits)
    if not 0 <= digits <= 100 or type(upper) is not bool:
        raise ValueError('decimal formatting needs 0..100 digits and boolean direction')
    scale=10**digits
    z=q*scale
    t=-((-z.numerator)//z.denominator) if upper else z.numerator//z.denominator
    sign='-' if t<0 else ''; t=abs(t)
    return sign+str(t//scale)+(('.'+str(t%scale).zfill(digits)) if digits else '')


def interval_record(value):
    value=Interval.coerce(value)
    out=[decimal_bound(value.lo),decimal_bound(value.hi,upper=True)]
    require(Fraction(out[0])<=value.lo<=value.hi<=Fraction(out[1]),'decimal enclosure failed')
    return out


def valid_order(n):
    integer(n,'n')
    if not 1 <= n <= MAX_N:
        raise ValueError('n must be 1..1000000')
    return n


def valid_split(n,m):
    valid_order(n); integer(m,'m')
    if n<3 or not 1<=m<=n//2:
        raise ValueError('split requires n>=3 and 1<=m<=floor(n/2)')


def candidate_multiplicities(n):
    valid_order(n)
    if n<3: return ()
    lo,hi=sqrt_bounds(Fraction(2,3))
    a=Fraction(n,2)*(1-hi); b=Fraction(n,2)*(1-lo)
    lower=a.numerator//a.denominator; upper=b.numerator//b.denominator
    require(lower==upper,'candidate floor unresolved; no rounding guess permitted')
    clip=lambda m:max(1,min(n//2,m))
    # n*pstar is irrational; hence ceil=floor+1.
    return tuple(sorted({clip(lower),clip(lower+1)}))


def reflection_values(n,m):
    valid_split(n,m)
    q=m*(n-m)
    y=Interval(Fraction(n*n,3*q)).sqrt()-1
    require(y.lo>0,'positive y not certified')
    skew2=Fraction((n-2*m)**2,q)
    # k²=skew²/[y(y+3)²]; denominator increasing for y>0.
    denominator=lambda z:z*(z+3)**2
    k2=Interval(skew2/denominator(y.hi),skew2/denominator(y.lo))
    k=k2.sqrt()
    require(0<=k.lo<=k.hi<1,'k must lie in [0,1)')
    fourth=(1+k)/(1-k)
    return {'y':y,'k_squared':k2,'k':k,'norm_fourth':fourth,
            'norm':fourth.sqrt().sqrt(),'beta':1/(1+k)}


def unique_winner(intervals):
    if type(intervals) is not dict or not intervals or len(intervals)>500:
        raise ValueError('comparison needs 1..500 labeled intervals')
    if any(type(k) is not int or type(v) is not Interval for k,v in intervals.items()):
        raise ValueError('comparison labels must be integers and values exact intervals')
    winner=max(intervals,key=lambda m:intervals[m].lo)
    if len(intervals)==1: return winner,None
    gap=min(intervals[winner].lo-v.hi for m,v in intervals.items() if m!=winner)
    require(gap>0,'candidate comparison unresolved or tied; no numerical decision made')
    return winner,gap


def reflection_norm(n):
    valid_order(n)
    if n<=2:
        return {'n':n,'candidate_m':[],'unique_winner':None,'norm_fourth':Interval(1),'norm':Interval(1)}
    ms=candidate_multiplicities(n)
    values={m:reflection_values(n,m) for m in ms}
    winner,gap=unique_winner({m:values[m]['k_squared'] for m in ms})
    return {'n':n,'candidate_m':list(ms),'unique_winner':winner,
            'winner_gap_k_squared_lower':gap,**values[winner]}


def constant_threshold(n):
    valid_order(n)
    if n<3: raise ValueError('threshold needs n>=3')
    beta=Fraction((n-2)**2,n*n-3*n+3)
    u=1+Interval(3/(3-2*beta)).sqrt()
    # u>2; endpointwise square avoids dependency widening.
    disc=Interval(u.lo*u.lo-4,u.hi*u.hi-4)
    return 1+(u+disc.sqrt())/2


def interval_certificate():
    rows=[]
    orders=(1,2,3,4,8,9,10,11,12,13,14,15,16,27,81)
    for n in orders:
        result=reflection_norm(n)
        row={key:value for key,value in result.items() if key in ('n','candidate_m','unique_winner')}
        row['values']={key:interval_record(value) for key,value in result.items() if type(value) is Interval}
        row['candidate_values']={str(m):{k:interval_record(v) for k,v in reflection_values(n,m).items()}
                                 for m in candidate_multiplicities(n)}
        rows.append(row)
    switches=[]
    for n in range(11,17):
        winner=1 if n<16 else 2; loser=3-winner
        gap=reflection_values(n,winner)['k']-reflection_values(n,loser)['k']
        require(gap.lo>0,'incorrect small-order multiplicity switch')
        switches.append({'n':n,'winner':winner,'winner_minus_loser_k':interval_record(gap)})
    r27=reflection_norm(27); r81=reflection_norm(81)
    require(r27['unique_winner']==3 and r81['unique_winner']==7,'wrong 27/81 winner')
    gap=r27['beta']-r81['beta']
    require(gap.lo>0,'81 beta must be strictly smaller than 27 beta')
    thresholds={str(n):interval_record(constant_threshold(n)) for n in (3,9,30)}
    return {'schema':'Report295 exact intervals v1','sqrt_grid_digits':SQRT_DIGITS,
            'display_decimal_digits':DISPLAY_DIGITS,'reflection_rows':rows,'switches':switches,
            'thresholds':thresholds,'beta27_minus_beta81':interval_record(gap)}


def supplemental_reflection_checks():
    rows=[]
    for n in range(3,101):
        winner,gap=unique_winner({m:reflection_values(n,m)['k_squared'] for m in range(1,n//2+1)})
        require(winner==reflection_norm(n)['unique_winner'],'finite exhaustive/candidate mismatch')
        rows.append([n,winner])
    for n,m,N,M in ((8,1,16,2),(9,1,27,3)):
        require(Fraction(m,n)==Fraction(M,N),'split fractions differ')
        require(Fraction((n-2*m)**2,m*(n-m))==Fraction((N-2*M)**2,M*(N-M)),'skewness identity failed')
        require(Fraction(n*n,3*m*(n-m))==Fraction(N*N,3*M*(N-M)),'y radical identity failed')
    require(Fraction(4,3)/(Fraction(1,3)*(Fraction(1,3)+3)**2)==Fraction(9,25),'n4 exact k² failed')
    return {'finite_exhaustive_range':[3,100],'maximizing_m':rows,
            'exact_repeated_split_identities':['C_16=C_8','C_27=C_9','beta_27=beta_9'],
            'n4_exact':{'k_squared':'9/25','norm_fourth':'4'},
            'scope':'Supplemental finite checks; the paper proves the all-n formula and candidate rule.'}


def finite_group(moduli):
    if type(moduli) is not tuple or not 1<=len(moduli)<=4:
        raise ValueError('finite example needs a tuple of 1..4 cyclic orders')
    size=1
    for modulus in moduli:
        integer(modulus)
        if modulus not in (3,9,27,81):
            raise ValueError('finite examples allow cyclic orders 3,9,27,81')
        size*=modulus
    if size>81:
        raise ValueError('finite example order exceeds 81')
    return tuple(product(*(range(m) for m in moduli)))


def add_point(x,y,moduli):
    return tuple((a+b)%m for a,b,m in zip(x,y,moduli))


def character_exponent(x,chi,moduli):
    conductor=max(moduli)
    return sum(a*b*(conductor//m) for a,b,m in zip(x,chi,moduli))%conductor


def character_sum(exponents,conductor):
    """Q[z]/(z^(2c/3)+z^(c/3)+1), c a positive power of three.

    A returned coefficient tuple is the complete exact reduced expression.
    This finite helper never approximates a complex root of unity.
    """
    integer(conductor)
    if conductor not in (3,9,27,81): raise ValueError('unsupported conductor')
    if type(exponents) not in (tuple,list) or len(exponents)>81:
        raise ValueError('at most 81 exact character exponents required')
    coefficients=[0]*conductor
    for exponent in exponents:
        integer(exponent)
        if not 0<=exponent<conductor: raise ValueError('character exponent out of range')
        coefficients[exponent]+=1
    third=conductor//3
    for exponent in range(conductor-1,2*third-1,-1):
        value=coefficients[exponent]
        coefficients[exponent]=0
        coefficients[exponent-third]-=value
        coefficients[exponent-2*third]-=value
    return tuple(coefficients[:2*third])


def energy_polynomial(moduli,weights,spike):
    """Exact ordered-pair convolution; spike values lie in C2."""
    points=finite_group(moduli)
    if type(weights) is not dict or set(weights)!=set(points): raise ValueError('one weight per group point required')
    if type(spike) is not set or not spike<=set(points): raise ValueError('spike must be a subset of the group')
    if any(type(w) is not Polynomial for w in weights.values()): raise ValueError('formal polynomial weights required')
    ordinary={x:Polynomial.constant(0) for x in points}
    parity={(x,e):Polynomial.constant(0) for x in points for e in (0,1)}
    for x in points:
        for y in points:
            z=add_point(x,y,moduli); term=weights[x]*weights[y]
            ordinary[z]+=term
            parity[(z,int(x in spike)^int(y in spike))]+=term
    E=sum((p*p for p in ordinary.values()),Polynomial.constant(0))
    Ea=sum((p*p for p in parity.values()),Polynomial.constant(0))
    signed={x:parity[(x,0)]-parity[(x,1)] for x in points}
    Es=sum((p*p for p in signed.values()),Polynomial.constant(0))
    require(2*Ea==E+Es,'finite parity energy identity failed')
    return Ea,E,Es


def spectral_algebra_checks():
    q,t=map(P,('q','t'))
    E=t**4+6*(q-1)*t*t+4*(q-1)*(q-2)*t+(q-1)*(q*q-3*q+3)
    Ea=t**4+6*(q-1)*t*t+(q-1)*(q*q-3*q+3)
    checks=[verify_identity('group-independent point-spike energy',q*E,(t+q-1)**4+(q-1)*(t-1)**4),
            verify_identity('formal point-spike parity',2*Ea,E+substitute(E,'t',-t)),
            verify_identity('spike scalar stationary numerator',Ea-t*Ea.derivative('t'),(q-1)*(q*q-3*q+3)-6*(q-1)*t*t-3*t**4)]
    v=P('v')
    # t_q²=q*v-(q-1), v²=(q-1)/3. Reduce the stationary polynomial.
    station=3*(q*v-(q-1))**2+6*(q-1)*(q*v-(q-1))-(q-1)*(q*q-3*q+3)
    checks.append(verify_identity('spike radical stationary relation',station,q*q*(3*v*v-(q-1))))
    checks.append(verify_identity('spike t positivity',4*(q*q-3*q+3),(2*q-3)**2+3))
    return checks


def finite_spectral_checks():
    """Supplemental examples only; no all-group conclusion from enumeration."""
    cases=[((27,),lambda x:x[0]%3==0),
           ((9,3),lambda x:x[1]==0),
           ((3,3,3),lambda x:x[2]==0),
           ((81,),lambda x:x[0]%9==0),
           ((27,3),lambda x:x[0]%3==0 and x[1]==0),
           ((9,3,3),lambda x:x[1]==0 and x[2]==0),
           ((9,9),lambda x:x[1]==0),
           ((3,3,3,3),lambda x:x[2]==0 and x[3]==0)]
    t=P('t'); E9=t**4+48*t*t+224*t+456; A9=t**4+48*t*t+456
    rows=[]
    for moduli,predicate in cases:
        points=finite_group(moduli); zero=tuple(0 for _ in moduli)
        L={x for x in points if predicate(x)}
        require(len(L)==9 and zero in L,'invalid nine-point subgroup example')
        require(all(add_point(x,y,moduli) in L for x in L for y in L),'example support not closed')
        S=tuple(chi for chi in points if all(character_exponent(x,chi,moduli)==0 for x in L))
        require(len(S)*len(L)==len(points),'annihilator cardinality mismatch')
        conductor=max(moduli)
        for x in points:
            val=character_sum([character_exponent(x,chi,moduli) for chi in S],conductor)
            expected=(len(S) if x in L else 0,)+(0,)*(2*conductor//3-1)
            require(val==expected,'finite subgroup character sum identity failed')
            # Coefficient identity behind the point-spike reflection: sum all characters=n delta_0.
            total=character_sum([character_exponent(x,chi,moduli) for chi in points],conductor)
            expected_total=(len(points) if x==zero else 0,)+(0,)*(2*conductor//3-1)
            require(total==expected_total,'finite character orthogonality failed')
        weights={x:t if x==zero else Polynomial.constant(int(x in L)) for x in points}
        Ea,E,Es=energy_polynomial(moduli,weights,{zero})
        require(E==E9 and Ea==A9 and Es==substitute(E9,'t',-t),'subgroup-supported energy polynomial mismatch')
        rows.append({'cyclic_factors':list(moduli),'order':len(points),'support_order':9,
                     'annihilator_order':len(S),'exact_energy_coefficients_low_to_high':[456,224,48,0,1],
                     'exact_retained_coefficients_low_to_high':[456,0,48,0,1]})
    # A nonsplit example: C27 -> C9 with kernel {0,9,18}; direct pair counting.
    points=finite_group((27,)); kernel={(0,),(9,),(18,)}
    lifted={x:t if x in kernel else Polynomial.constant(1) for x in points}
    Ea,E,Es=energy_polynomial((27,),lifted,kernel)
    require(E==27*E9 and Ea==27*A9,'nonsplit constant-fiber lift energy mismatch')
    # All 256 identity-containing subsets of the dual of C3^2.
    points9=finite_group((3,3)); zero9=(0,0); successes=0
    for mask in range(256):
        S=(zero9,)+tuple(points9[i+1] for i in range(8) if (mask>>i)&1)
        sums=[character_sum([character_exponent(x,chi,(3,3)) for chi in S],3) for x in points9]
        nonnegative=all(b==0 and a>=0 for a,b in sums)
        subgroup=all(add_point(a,b,(3,3)) in S for a in S for b in S)
        require(nonnegative==subgroup,'finite nonnegative-character-sum equivalence failed')
        successes+=int(nonnegative)
    require(successes==6,'C3^2 subgroup count mismatch')
    return {'point_spike_examples':rows,'nonnegative_character_sum_example':{'group':'C3^2','identity_containing_subsets':256,'nonnegative_sums':6},'nonsplit_lift' :{'source':'C27','quotient':'C9','kernel_order':3,'energy_multiplier':27},
            'scope':'Supplemental finite character and energy identities. General saturation and strictness require the paper proof; no exact order-81 spike minimum is computed.'}


def canonical_bytes(value):
    return (json.dumps(value,sort_keys=True,separators=(',',':'),ensure_ascii=True)+'\n').encode('ascii')


def _unique_keys(pairs):
    result={}
    for key,value in pairs:
        if key in result: raise ValueError('duplicate JSON key')
        result[key]=value
    return result


def _bad_number(value):
    raise ValueError('floating or nonfinite JSON number forbidden')


def _bounded_json_integer(value):
    if len(value)>12: raise ValueError('overlong certificate integer')
    return int(value)


def load_certificate(path):
    path=Path(path)
    with path.open('rb') as stream: raw=stream.read(100001)
    if len(raw)>100000: raise ValueError('certificate exceeds 100000 bytes')
    # Bound structure depth before parsing, honoring escaped quotes.
    depth=0; quoted=False; escape=False
    for byte in raw:
        if quoted:
            if escape: escape=False
            elif byte==92: escape=True
            elif byte==34: quoted=False
        elif byte==34: quoted=True
        elif byte in (91,123):
            depth+=1
            if depth>16: raise ValueError('certificate nesting exceeds 16')
        elif byte in (93,125): depth-=1
    try:
        value=json.loads(raw.decode('ascii'),object_pairs_hook=_unique_keys,parse_float=_bad_number,
                         parse_constant=_bad_number,parse_int=_bounded_json_integer)
    except (UnicodeError,json.JSONDecodeError) as exc:
        raise ValueError('invalid ASCII JSON certificate') from exc
    if canonical_bytes(value)!=raw: raise ValueError('certificate is not canonical JSON')
    return value,sha256(raw).hexdigest()


def validate_certificate(value,expected=None):
    if type(value) is not dict: raise ValueError('certificate must be an object')
    if expected is None: expected=interval_certificate()
    # Canonical byte equality also distinguishes True from 1 and rejects added keys.
    require(canonical_bytes(value)==canonical_bytes(expected),'interval certificate differs from independently regenerated exact enclosures')
    return True


def run_checks(certificate_path=None):
    identities=polynomial_checks()+spectral_algebra_checks()
    calculated=interval_certificate()
    path=Path(__file__).with_name('interval_certificate.json') if certificate_path is None else certificate_path
    certificate,digest=load_certificate(path)
    validate_certificate(certificate,calculated)
    return {'report':295,'status':'PASS','arithmetic':'Python standard-library integer/Fraction polynomial arithmetic and outward rational sqrt intervals',
            'formal_identity_count':len(identities),'formal_identities':identities,
            'interval_certificate_sha256':digest,'interval_certificate':calculated,
            'supplemental_reflections':supplemental_reflection_checks(),
            'supplemental_spectral_examples':finite_spectral_checks(),
            'scope':'The code certifies general polynomial formulas, finite exact comparisons, and labeled finite examples. The paper supplies all-n/all-group analytic proofs and the general-gamma finite real-root reduction. No arbitrary-gamma quintic norm solver or exact order-81 spike minimum is implemented.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    sys.stdout.buffer.write(canonical_bytes(run_checks()))


if __name__=='__main__':
    main()
