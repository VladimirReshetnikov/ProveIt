"""Finite symbolic formulas. Z(A,B) denotes the convergent double zeta."""
from __future__ import annotations
from functools import lru_cache
from math import comb
import sympy as sp

Z = sp.Function('Z')
t, v = sp.symbols('t v')

def choose(n,k):
    return sp.Integer(comb(n,k)) if n>=0 and 0<=k<=n else sp.Integer(0)

def even(j):
    return sp.Integer(1) if j==0 else 2*(1-sp.Rational(2)**(1-2*j))*sp.zeta(2*j)

def cone(m,n):
    W=m+n
    return [(choose(W-2-k,b-1),W-1-k,k+1) for a,b in [(m,n),(n,m)] for k in range(a)]

@lru_cache(None)
def cjet(A,B,nu):
    if A==B==1:
        return (sum(sp.zeta(k+1)*sp.zeta(nu-k+1) for k in range(1,nu))+(nu+1)*sp.zeta(nu+2))/2
    r=-sp.rf(A,nu)/sp.factorial(nu)*Z(A+nu,B)
    for k in range(1,nu+1):
        r+=sp.rf(A,nu-k)*sp.rf(B,k)/(sp.factorial(nu-k)*sp.factorial(k))*(Z(B+k,A+nu-k)+sp.zeta(A+B+nu))
    return sp.expand(r)

@lru_cache(None)
def jet(m,n,h=0,negative=False):
    r=sp.Integer(0)
    for j in range(h//2+1):
        nu=h+1-2*j
        for c,A,B in cone(m,n):
            q=cjet(A,B,nu)
            if negative:
                q-=sum(sp.rf(A,nu-k)*sp.rf(B,k)/(sp.factorial(nu-k)*sp.factorial(k))*sp.zeta(B+k) for k in range(1,nu+1))
            r+=even(j)*c*q
    return sp.expand((-1 if negative else 1)*sp.factorial(h)*r)

@lru_cache(None)
def compact(m,n):
    W=m+n
    r=(choose(W,m-1)+choose(W,n-1))*sp.zeta(W+1)
    for j in range(1,W):
        b=choose(W-j-1,m-1)+choose(W-j-1,n-1)-choose(j-1,m-1)-choose(j-1,n-1)
        r+=j*b*Z(j+1,W-j)
    return sp.expand(r)

@lru_cache(None)
def one_jet(n,h):
    return sp.expand(-sp.factorial(h)*sum(even(j)*sp.rf(n,h+1-2*j)/sp.factorial(h+1-2*j)*sp.zeta(n+h+1-2*j) for j in range(h//2+1)))

@lru_cache(None)
def beta_moment(d,h):
    if d<0: raise ValueError('Base beta moment needs d>=0')
    p=sp.prod(1+v/sp.Integer(k) for k in range(1,d+1))
    e=sum(even(j)*v**(2*j) for j in range(h//2+1))
    return sp.expand(sp.factorial(h)/sp.Integer(d+1)*sp.expand(p*e).coeff(v,h))

def terms(R):
    R=sp.expand(sp.cancel(R))
    ans={}
    for term in sp.Add.make_args(R):
        exponent=term.as_powers_dict().get(t,sp.Integer(0))
        if not exponent.is_Integer: raise ValueError('Laurent polynomial required')
        coefficient=sp.cancel(term/t**exponent)
        if coefficient.has(t): raise ValueError('Laurent polynomial required')
        ans[int(exponent)]=ans.get(int(exponent),0)+coefficient
    return ans

def decompose(R):
    d=terms(R)
    S=sp.expand(sum(c*(t**(j+1)-1)/sp.Integer(j+1) for j,c in d.items() if j!=-1))
    K=sp.cancel(S/(t*(1-t)))
    return d.get(-1,sp.Integer(0)),S,sp.expand(K)

@lru_cache(None)
def reduce_kernel(R,orders,h=0):
    """Finite rational-kernel reduction; input integrability is caller's duty."""
    R=sp.expand(R)
    if R==0: return sp.Integer(0)
    if h<0 or any(n<0 for n in orders): raise ValueError('Nonnegative orders and h required')
    if 0 in orders:
        a=list(orders); a.remove(0)
        return reduce_kernel(sp.expand(-t*R),tuple(a),h)
    if not orders:
        return sp.expand(sum(c*beta_moment(d,h) for d,c in terms(R).items()))
    c,S,K=decompose(R)
    if len(orders)==2:
        base=jet(*orders,h)
    elif len(orders)==1:
        base=one_jet(orders[0],h)
    else: raise ValueError('Implementation handles at most two factors')
    result=c*base
    for i in range(len(orders)):
        b=list(orders); b[i]-=1
        result-=reduce_kernel(K,tuple(b),h)
    if h:
        result-=h*reduce_kernel(K,orders,h-1)
    return sp.expand(result)

def moment(N,a,m,n,h=0):
    if N<1 or not -1<=a<N or min(m,n)<1: raise ValueError('N>=1, -1<=a<N, m,n>=1 required')
    return reduce_kernel(sp.expand(t**(a-1)*(1-t)**(N-a-1)),(m,n),h)

def inversion(n,y):
    return -y**n/sp.factorial(n)-2*sum((1-sp.Rational(2)**(1-2*k))*sp.zeta(2*k)*y**(n-2*k)/sp.factorial(n-2*k) for k in range(1,n//2+1))

def central(m,n,h=0):
    """N=1 central odd-parity moments, in ordinary zeta data only."""
    if (m+n+h)%2!=1: raise ValueError('Parity not projected by this formula')
    D=m+n+h
    # Exact secant series avoids symbolic differentiation at zeta(1).
    sec=sum((-1)**k*sp.euler(2*k)*sp.pi**(2*k)*v**(2*k)/sp.factorial(2*k) for k in range(D//2+1))
    def jseries(s):
        constant=-2*sp.log(2) if s==1 else (2-sp.Integer(2)**s)*sp.zeta(s)
        z=constant-sum(sp.rf(s,k)/sp.factorial(k)*(sp.Integer(2)**(s+k)-1)*sp.zeta(s+k)*v**k for k in range(1,D+1))
        return sp.expand(sp.pi*sec*z)
    def apply(p,f):
        return sum(c*sp.factorial(k+h)*f.coeff(v,k+h) for (k,),c in sp.Poly(p,v).terms())
    P=inversion(m,v); Q=inversion(n,v)
    return sp.expand((apply(P,jseries(n))+apply(Q,jseries(m))-apply(P*Q,sp.expand(sp.pi*sec)))/2)

LOW={Z(2,1):sp.zeta(3),Z(3,1):sp.zeta(4)/4,Z(2,2):3*sp.zeta(4)/4,
     Z(4,1):2*sp.zeta(5)-sp.zeta(2)*sp.zeta(3),
     Z(2,3):sp.Rational(9,2)*sp.zeta(5)-2*sp.zeta(2)*sp.zeta(3),
     Z(3,2):3*sp.zeta(2)*sp.zeta(3)-sp.Rational(11,2)*sp.zeta(5)}
def low(expr): return sp.expand(expr.xreplace(LOW))

if __name__=='__main__':
    for N,a,m,n,h in [(1,0,1,1,0),(1,-1,1,1,0),(2,1,1,1,0),(3,1,2,1,0),(3,2,2,2,0),(2,0,2,1,0),(1,-1,2,1,0),(2,1,2,2,1)]:
        print((N,a,m,n,h),low(moment(N,a,m,n,h)))
    for m,n,h in [(1,2,0),(1,1,1),(2,3,0),(2,2,1),(1,4,0)]:
        print('central',m,n,h,central(m,n,h))
