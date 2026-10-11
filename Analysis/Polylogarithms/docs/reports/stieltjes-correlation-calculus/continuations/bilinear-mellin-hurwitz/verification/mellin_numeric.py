"""Independent high-precision diagnostics, not interval certificates."""
from __future__ import annotations
from functools import lru_cache
from math import comb
import mpmath as mp


def choose(n: int, k: int) -> int:
    return comb(n, k) if n >= 0 and 0 <= k <= n else 0

@lru_cache(maxsize=10000)
def _double(A: int, B: int, qstr: str, dps: int, M: int, K: int):
    q = mp.mpf(qstr)
    if A < 2 or B < 1 or q <= 0:
        raise ValueError('A>=2, B>=1, q>0 required')
    z = M + q
    if B == 1:
        total = mp.mpf(0)
        h = mp.mpf(0)
        for n in range(M):
            v = n + q
            total += h / v**A
            h += 1/v
        tail = -mp.diff(lambda s: mp.zeta(s, z), A) - mp.digamma(q)*mp.zeta(A,z)
        tail -= mp.zeta(A+1,z)/2
        for k in range(1,K+1):
            tail -= mp.bernoulli(2*k)/(2*k)*mp.zeta(A+2*k,z)
        return total+tail
    total = mp.fsum((n+q)**(-A)*mp.zeta(B,n+q) for n in range(M))
    tail = mp.zeta(A+B-1,z)/(B-1)+mp.zeta(A+B,z)/2
    for k in range(1,K+1):
        tail += mp.bernoulli(2*k)/mp.factorial(2*k)*mp.rf(B,2*k-1)*mp.zeta(A+B+2*k-1,z)
    return mp.zeta(A,q)*mp.zeta(B,q)-total-tail

def double(A: int, B: int, q=1, M=64, K=24):
    return _double(A,B,str(mp.mpf(q)),mp.mp.dps,M,K)

def delta(k: int, q):
    return -mp.euler-mp.digamma(q) if k==1 else mp.zeta(k,q)-mp.zeta(k)

def connected(A: int, B: int, q, M=64, K=24):
    if A>=2:
        return double(A,B,1,M,K)-double(A,B,q,M,K)+mp.zeta(A,q)*delta(B,q)
    if B>=2:
        return double(B,1,q,M,K)-double(B,1,1,M,K)+delta(B+1,q)-delta(1,q)*mp.zeta(B)
    return (delta(1,q)**2+delta(2,q))/2

def cone_coeffs(m: int, n: int):
    W=m+n
    for left,right in [(m,n),(n,m)]:
        for k in range(left):
            yield choose(W-2-k,right-1), W-1-k,k+1

def master(a, m: int, n: int, M=64,K=24):
    a=mp.mpf(a)
    if not -2 < a < 1 or a == mp.floor(a):
        raise ValueError("Use a real noninteger -2<a<1; use the resonance functions at a=0,-1")
    q=1-a
    return mp.pi/mp.sin(mp.pi*a)*mp.fsum(c*connected(A,B,q,M,K) for c,A,B in cone_coeffs(m,n))

def inversion(n: int, y):
    return -y**n/mp.factorial(n)-2*mp.fsum((1-mp.mpf(2)**(1-2*k))*mp.zeta(2*k)*y**(n-2*k)/mp.factorial(n-2*k) for k in range(1,n//2+1))

def li_integer(n: int,u):
    """Inversion keeps all library polylogs in the convergent unit disk."""
    if n==0:
        return -1/(1+mp.exp(-u))
    if n==1:
        return -mp.log1p(mp.exp(u)) if u<=0 else -u-mp.log1p(mp.exp(-u))
    if u<=0:
        return mp.polylog(n,-mp.exp(u))
    return inversion(n,u)-(-1)**n*mp.polylog(n,-mp.exp(-u))

def direct(a,m: int,n: int,N=1,h=0,z=1,w=1):
    def integrand(u):
        # Stable logistic Mellin density; never subtract near-equal exponentials.
        density=mp.exp((a-N)*u)/(1+mp.exp(-u))**N if u>0 else mp.exp(a*u)/(1+mp.exp(u))**N
        return density*u**h*li_integer(m,u+mp.log(z))*li_integer(n,u+mp.log(w))
    return mp.quad(integrand,[-mp.inf,-4,0,4,mp.inf])

def cjet(A: int,B: int,nu: int,M=64,K=24):
    if A==B==1:
        return (mp.fsum(mp.zeta(v+1)*mp.zeta(nu-v+1) for v in range(1,nu))+(nu+1)*mp.zeta(nu+2))/2
    out=-mp.rf(A,nu)/mp.factorial(nu)*double(A+nu,B,1,M,K)
    for v in range(1,nu+1):
        out+=mp.rf(A,nu-v)*mp.rf(B,v)/(mp.factorial(nu-v)*mp.factorial(v))*(double(B+v,A+nu-v,1,M,K)+mp.zeta(A+B+nu))
    return out

def resonant_jet(m: int,n: int,h=0,M=64,K=24):
    total=mp.mpf(0)
    for j in range(h//2+1):
        e=1 if j==0 else 2*(1-mp.mpf(2)**(1-2*j))*mp.zeta(2*j)
        nu=h+1-2*j
        total+=e*mp.fsum(c*cjet(A,B,nu,M,K) for c,A,B in cone_coeffs(m,n))
    return mp.factorial(h)*total

def compact_resonance(m: int,n: int,M=64,K=24):
    W=m+n
    total=(choose(W,m-1)+choose(W,n-1))*mp.zeta(W+1)
    for j in range(1,W):
        b=choose(W-j-1,m-1)+choose(W-j-1,n-1)-choose(j-1,m-1)-choose(j-1,n-1)
        total+=j*b*double(j+1,W-j,1,M,K)
    return total

if __name__=='__main__':
    mp.mp.dps=40
    for m,n,a in [(1,1,mp.mpf('.3')),(2,1,mp.mpf('-.5')),(2,2,mp.mpf('.4')),(3,1,mp.mpf('-1.4'))]:
        lhs=direct(a,m,n)
        rhs=master(a,m,n)
        print(m,n,a,mp.nstr(lhs,20),mp.nstr(rhs,20),mp.nstr(lhs-rhs,6),flush=True)
    for m,n,h in [(1,1,0),(2,1,0),(2,2,1),(3,1,2),(1,1,3)]:
        lhs=direct(0,m,n,h=h); rhs=resonant_jet(m,n,h)
        print('jet',m,n,h,mp.nstr(lhs,20),mp.nstr(rhs,20),mp.nstr(lhs-rhs,6),flush=True)
    v=direct(mp.mpf('.5'),1,2)
    r=mp.mpf(21)/2*mp.pi*mp.zeta(3)+mp.mpf(2)/3*mp.pi**3*mp.log(2)
    print('central',mp.nstr(v-r,8),flush=True)
    v=direct(1,1,1,N=2,z=1,w=2)
    r=mp.pi**2/6+2*mp.log(2)-mp.log(2)**2
    print('multiscale',mp.nstr(v-r,8),flush=True)
