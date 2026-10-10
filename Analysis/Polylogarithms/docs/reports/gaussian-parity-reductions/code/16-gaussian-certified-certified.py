#!/usr/bin/env python3
"""Integer-only outward-rounded rectangles for level-3/4 double polylogarithms.

No floating-point functions, third-party ball package, or conjectural identity
is used in the certified evaluation path. All endpoints are integers / 10**D.
The infinite tails are bounded by the theorems in article.tex.
"""
from __future__ import annotations
from fractions import Fraction
from functools import lru_cache
from math import isqrt, comb


def ceildiv(a: int,b: int)->int:
    return -((-a)//b)

class Context:
    def __init__(self,digits: int):
        if digits<10:raise ValueError('at least ten guard digits required')
        self.digits=digits;self.scale=10**digits
    def real(self,x=0):
        if isinstance(x,Real):
            if x.ctx is not self:raise ValueError('mixed interval contexts')
            return x
        x=Fraction(x);q=self.scale
        return Real(self,x.numerator*q//x.denominator,ceildiv(x.numerator*q,x.denominator))
    def complex(self,x=0,y=0):
        if isinstance(x,Complex):
            if x.ctx is not self:raise ValueError('mixed interval contexts')
            return x
        return Complex(self.real(x),self.real(y))

class Real:
    def __init__(self,ctx:Context,lo:int,hi:int):
        if lo>hi:raise ValueError('reversed interval')
        self.ctx=ctx;self.lo=lo;self.hi=hi
    def __add__(self,o):
        o=self.ctx.real(o);return Real(self.ctx,self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return Real(self.ctx,-self.hi,-self.lo)
    def __sub__(self,o):return self+-self.ctx.real(o)
    def __rsub__(self,o):return self.ctx.real(o)+-self
    def __mul__(self,o):
        o=self.ctx.real(o);q=self.ctx.scale
        v=[self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi]
        return Real(self.ctx,min(v)//q,ceildiv(max(v),q))
    __rmul__=__mul__
    def square(self):
        q=self.ctx.scale
        lo=0 if self.lo<=0<=self.hi else min(self.lo*self.lo,self.hi*self.hi)
        hi=max(self.lo*self.lo,self.hi*self.hi)
        return Real(self.ctx,lo//q,ceildiv(hi,q))
    def reciprocal(self):
        if self.lo<=0<=self.hi:raise ZeroDivisionError('interval includes zero')
        q2=self.ctx.scale**2
        return Real(self.ctx,q2//self.hi,ceildiv(q2,self.lo))
    def __truediv__(self,o):return self*self.ctx.real(o).reciprocal()
    def __rtruediv__(self,o):return self.ctx.real(o)*self.reciprocal()
    def __pow__(self,n):
        if not isinstance(n,int):raise TypeError('integer exponent required')
        if n<0:return self.reciprocal()**(-n)
        a=self.ctx.real(1);b=self
        while n:
            if n&1:a=a*b
            n//=2
            if n:b=b*b
        return a
    def sqrt(self):
        if self.lo<0:raise ValueError('negative square-root interval')
        q=self.ctx.scale
        lo=isqrt(self.lo*q);hi=isqrt(self.hi*q)
        if hi*hi<self.hi*q:hi+=1
        return Real(self.ctx,lo,hi)
    def inflate(self,radius):
        r=self.ctx.real(radius)
        if r.lo<0:raise ValueError('negative radius')
        return Real(self.ctx,self.lo-r.hi,self.hi+r.hi)
    def contains_zero(self):return self.lo<=0<=self.hi
    def width(self):return Fraction(self.hi-self.lo,self.ctx.scale)
    def record(self):
        return {'lower_integer':str(self.lo),'upper_integer':str(self.hi),'decimal_scale':self.ctx.digits}
    def decimal(self,n=50):
        # Directed decimal endpoints, not a binary floating approximation.
        if n>self.ctx.digits:raise ValueError('too many display digits')
        div=10**(self.ctx.digits-n)
        ll=self.lo//div;hh=ceildiv(self.hi,div)
        def fmt(v):
            sg='-' if v<0 else '';v=abs(v);a,b=divmod(v,10**n)
            return f'{sg}{a}.{b:0{n}d}'
        return [fmt(ll),fmt(hh)]

class Complex:
    def __init__(self,re:Real,im:Real):
        if re.ctx is not im.ctx:raise ValueError('mixed contexts')
        self.ctx=re.ctx;self.re=re;self.im=im
    def __add__(self,o):
        o=self.ctx.complex(o);return Complex(self.re+o.re,self.im+o.im)
    __radd__=__add__
    def __neg__(self):return Complex(-self.re,-self.im)
    def __sub__(self,o):return self+-self.ctx.complex(o)
    def __rsub__(self,o):return self.ctx.complex(o)+-self
    def __mul__(self,o):
        o=self.ctx.complex(o)
        return Complex(self.re*o.re-self.im*o.im,self.re*o.im+self.im*o.re)
    __rmul__=__mul__
    def conjugate(self):return Complex(self.re,-self.im)
    def norm2(self):return self.re.square()+self.im.square()
    def reciprocal(self):
        den=self.norm2();return Complex(self.re/den,-self.im/den)
    def __truediv__(self,o):return self*self.ctx.complex(o).reciprocal()
    def __rtruediv__(self,o):return self.ctx.complex(o)*self.reciprocal()
    def __pow__(self,n):
        if n<0:return self.reciprocal()**(-n)
        a=self.ctx.complex(1);b=self
        while n:
            if n&1:a=a*b
            n//=2
            if n:b=b*b
        return a
    def inflate(self,radius):return Complex(self.re.inflate(radius),self.im.inflate(radius))
    def record(self):return {'real':self.re.record(),'imag':self.im.record()}

@lru_cache(None)
def shifted_chebyshev(n:int):
    if n<0:raise ValueError('nonnegative index required')
    if n==0:return (1,)
    if n==1:return (-1,2)
    a=shifted_chebyshev(n-1);b=shifted_chebyshev(n-2)
    c=[0]*(n+1)
    for j,v in enumerate(a):c[j]-=2*v;c[j+1]+=4*v
    for j,v in enumerate(b):c[j]-=v
    return tuple(c)

class Evaluator:
    def __init__(self,target_digits:int=35,max_order:int=12):
        if target_digits<5:raise ValueError('target_digits >= 5 required')
        self.target_digits=target_digits;self.max_order=max_order
        self.K=1
        while Fraction(16,3*4**self.K)>Fraction(1,10**(target_digits+8)):self.K+=1
        self.ctx=Context(target_digits+2*self.K+65)
        self.euler_terms=1
        tail=Fraction(4)*Fraction(3,4)**2
        while tail>Fraction(1,10**(self.ctx.digits+3)):
            self.euler_terms+=1;tail*=Fraction(3,4)
        self.euler_tail=tail
        self._singles={};self._doubles={}
    def root(self,q:int,r:int):
        c=self.ctx;r%=q
        if r==0:return c.complex(1)
        if q==4:
            return [c.complex(1),c.complex(0,1),c.complex(-1),c.complex(0,-1)][r]
        if q==3:
            return c.complex(Fraction(-1,2), (c.real(3).sqrt()/2)*(1 if r==1 else -1))
        if q==2:return c.complex(-1)
        raise ValueError('certified implementation supports levels 2, 3, and 4')
    def singles(self,q:int,r:int):
        r%=q;key=(q,r)
        if key in self._singles:return self._singles[key]
        c=self.ctx
        if r==0:
            neg=self.singles(2,1)
            ans={s:-neg[s]/Fraction(1-Fraction(2)**(1-s)) for s in range(2,self.max_order+1)}
            self._singles[key]=ans;return ans
        z=self.root(q,r);t=z/(z-1)
        if not t.norm2().hi*16<c.scale*9:
            raise ArithmeticError('Euler ratio bound not established')
        h=[c.real(1)]+[c.real(0)]*(self.max_order-1)
        acc={s:c.complex(0) for s in range(1,self.max_order+1)}
        power=t
        for n in range(1,self.euler_terms+1):
            for d in range(1,self.max_order):h[d]=h[d]+h[d-1]/n
            for s in range(1,self.max_order+1):acc[s]=acc[s]-power*c.complex(h[s-1]/n)
            power=power*t
        ans={s:v.inflate(self.euler_tail) for s,v in acc.items()}
        self._singles[key]=ans;return ans
    def square_root_one_minus(self,q:int,r:int):
        z=1-self.root(q,r);norm=z.norm2().sqrt()
        u=((norm+z.re)/2).sqrt()
        if z.im.lo==z.im.hi==0:return self.ctx.complex(u)
        v=((norm-z.re)/2).sqrt()
        if z.im.hi<0:v=-v
        elif not z.im.lo>0:raise ValueError('undetermined square-root sign')
        return self.ctx.complex(u,v)
    def moments(self,a:int,b:int,q:int,v:int):
        v%=q;c=self.ctx;z=self.root(q,v);sing=self.singles(q,v)
        mmax=max(a,b);hs={r:c.complex(0) for r in range(1,mmax+1)}
        out=[];power=z
        for shift in range(1,self.K+1):
            for r in range(1,mmax+1):hs[r]=hs[r]+power/Fraction(shift**r)
            aa={r:Fraction((-1)**(b-r)*comb(a+b-r-1,a-1),shift**(a+b-r)) for r in range(1,b+1)}
            bb={r:Fraction((-1)**b*comb(a+b-r-1,b-1),shift**(a+b-r)) for r in range(1,a+1)}
            ans=c.complex(0)
            if v==0:
                if aa[1]+bb[1]!=0:
                    raise ArithmeticError('divergent harmonic coefficient did not cancel')
                ans=ans-hs[1]*bb[1]
                for r in range(2,mmax+1):
                    ans=ans+sing[r]*(aa.get(r,0)+bb.get(r,0))-hs[r]*bb.get(r,0)
            else:
                # z^(-shift) is evaluated as a root, avoiding interval dependency.
                invpower=self.root(q,(-v*shift)%q)
                for r,coef in aa.items():ans=ans+sing[r]*coef
                for r,coef in bb.items():ans=ans+invpower*(sing[r]-hs[r])*coef
            out.append(ans);power=self.root(q,(v*(shift+1))%q)
        return out
    def double(self,a:int,b:int,q:int,x:int,y:int):
        if min(a,b)<1 or max(a,b)>self.max_order:raise ValueError('unsupported indices')
        x%=q;y%=q
        if x==0:raise ValueError('outer argument 1 is outside this certified implementation')
        key=(a,b,q,x,y)
        if key in self._doubles:return self._doubles[key]
        z=self.root(q,x);d=self.square_root_one_minus(q,x);rho=(1-d)/(1+d)
        if not rho.norm2().hi*16<self.ctx.scale:
            raise ArithmeticError('rho < 1/4 not proved')
        if not d.norm2().lo>=self.ctx.scale:
            raise ArithmeticError('|sqrt(1-x)| >= 1 not proved')
        moments=self.moments(a,b,q,(x+y)%q)
        result=moments[0];power=rho
        for n in range(1,self.K):
            moment=self.ctx.complex(0)
            for j,coef in enumerate(shifted_chebyshev(n)):
                moment=moment+moments[j]*coef
            result=result+2*power*moment;power=power*rho
        result=(z/d*result).inflate(Fraction(16,3*4**self.K))
        self._doubles[key]=result;return result
    def constants(self):
        ii=self.singles(4,1);minus=self.singles(2,1)
        out={'P':4*ii[1].im,'L':-minus[1].re}
        for s in range(2,self.max_order+1):
            if s%2==0:out[f'B{s}']=ii[s].im
            else:out[f'Z{s}']=(-minus[s]/Fraction(1-Fraction(2)**(1-s))).re
        return out
    def polynomial(self,expr):
        # Only exact SymPy polynomial ASTs produced by derive_identities.py.
        import sympy as s
        const=self.constants()
        def go(e):
            if e.is_Rational:return self.ctx.real(Fraction(int(e.p),int(e.q)))
            if e.is_Symbol:return const[str(e)]
            if e.is_Add:return sum((go(a) for a in e.args),self.ctx.real(0))
            if e.is_Mul:
                v=self.ctx.real(1)
                for a in e.args:v=v*go(a)
                return v
            if e.is_Pow and e.exp.is_Integer:return go(e.base)**int(e.exp)
            raise TypeError(f'unsupported expression: {e}')
        return go(s.expand(expr))
