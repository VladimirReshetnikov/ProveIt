"""All-orders saddle coefficients for square-root-restricted partitions.

Only mpmath is required. Numerical coefficient evaluation is not an interval
proof; certificate.py separately checks the signs used in the article using
exact rational interval arithmetic.
"""
from __future__ import annotations
from dataclasses import dataclass
from math import comb, factorial, isqrt
from typing import Dict, List, Tuple
import mpmath as mp

Poly = Dict[Tuple[int, int], mp.mpf]  # powers of y and theta


def add_term(p: Poly, y: int, theta: int, value: mp.mpf) -> None:
    if value:
        key = (y, theta)
        p[key] = p.get(key, mp.mpf(0)) + value


def multiply(p: Poly, q: Poly) -> Poly:
    r: Poly = {}
    for (a, b), c in p.items():
        for (d, e), f in q.items():
            add_term(r, a+d, b+e, c*f)
    return r


def gaussian(p: Poly) -> Dict[int, mp.mpf]:
    """Evaluate y=iZ for Z standard normal, leaving theta symbolic."""
    out: Dict[int, mp.mpf] = {}
    for (a, b), c in p.items():
        if a % 2 == 0:
            j = a // 2
            moment = (-1)**j * mp.factorial(2*j)/(2**j*mp.factorial(j))
            out[b] = out.get(b, mp.mpf(0)) + c*moment
    return out


@dataclass
class Saddle:
    alpha: mp.mpf
    u: mp.mpf
    H: mp.mpf
    V: mp.mpf
    C: mp.mpf

    @classmethod
    def make(cls, alpha=1) -> 'Saddle':
        alpha = mp.mpf(alpha)
        if not mp.isfinite(alpha) or alpha <= 0:
            raise ValueError('alpha must be finite and positive')
        def F(z):
            return (mp.zeta(2)-mp.polylog(2, mp.exp(-z)))/z
        def J(z):
            return (F(z)+mp.log(-mp.expm1(-z)))/z
        lo = mp.mpf('0.00001')
        while J(lo) <= alpha:
            lo /= 2
        hi = mp.mpf(1)
        while J(hi) >= alpha:
            hi *= 2
        # Bisection is reliable even for small or large alpha.
        for _ in range(4*mp.mp.dps+20):
            mid = (lo+hi)/2
            if J(mid) > alpha:
                lo = mid
            else:
                hi = mid
        u = (lo+hi)/2
        f0 = F(u)
        f1 = (mp.polylog(1, mp.exp(-u))-f0)/u
        f2 = (-mp.polylog(0, mp.exp(-u))-2*f1)/u
        G = mp.sqrt(u/(-mp.expm1(-u)))
        return cls(alpha, u, alpha*u+f0, f2, G/(2*mp.pi*mp.sqrt(f2)))

    def derivatives(self, order: int):
        z = self.u
        q = mp.exp(-z)
        F = [(mp.zeta(2)-mp.polylog(2,q))/z]
        for r in range(1, order+1):
            numerator = (-1)**(r+1)*mp.polylog(2-r,q)
            F.append((numerator-r*F[-1])/z)
        ell = [mp.log(z/(-mp.expm1(-z)))/2]
        for r in range(1,order+1):
            ell.append(((-1)**(r-1)*mp.factorial(r-1)/z**r
                        +(-1)**r*mp.polylog(1-r,q))/2)
        return F, ell

    def E_derivative(self, r: int, v: int) -> mp.mpf:
        """v-th derivative of E_{2r-1}(u)."""
        p = 2*r-1
        s = mp.mpf(0)
        for a in range(min(v,p)+1):
            s += (comb(v,a)*mp.factorial(p)/mp.factorial(p-a)
                  *self.u**(p-a)*(-1)**(v-a)
                  *mp.polylog(1-p-v+a, mp.exp(-self.u)))
        s *= -mp.bernoulli(2*r)/mp.factorial(2*r)
        if r == 1:
            if v == 0:
                s -= self.u/24
            elif v == 1:
                s -= mp.mpf(1)/24
        return s

    def coefficients(self, K: int, sigma=0, tau=0, floor_phase=False):
        """Return D_0,...,D_K. In floor_phase mode D_k is a theta polynomial
        for sigma=2*theta, tau=theta**2, represented by ascending coefficients.
        """
        if not isinstance(K,int) or K < 0:
            raise ValueError('K must be a nonnegative integer')
        sigma, tau = mp.mpf(sigma), mp.mpf(tau)
        F, ell = self.derivatives(2*K+2)
        E: List[Poly] = [{} for _ in range(2*K+1)]
        for r in range(3,2*K+3):
            n = r-2
            add_term(E[n],r,0,F[r]/(mp.factorial(r)*self.V**(mp.mpf(r)/2)))
        for r in range(1,2*K+1):
            add_term(E[r],r,0,ell[r]/(mp.factorial(r)*self.V**(mp.mpf(r)/2)))
        if 2*K >= 1:
            add_term(E[1],1,1 if floor_phase else 0,
                     (2 if floor_phase else sigma)/mp.sqrt(self.V))
        if 2*K >= 2:
            add_term(E[2],0,2 if floor_phase else 0,
                     (1 if floor_phase else tau)*self.u)
        if 2*K >= 3:
            add_term(E[3],1,2 if floor_phase else 0,
                     (1 if floor_phase else tau)/mp.sqrt(self.V))
        for r in range(1,K+1):
            start = 4*r-2
            if start > 2*K:
                break
            for v in range(2*K-start+1):
                add_term(E[start+v],v,0,self.E_derivative(r,v)
                         /(mp.factorial(v)*self.V**(mp.mpf(v)/2)))
        R: List[Poly] = [{(0,0):mp.mpf(1)}]
        for n in range(1,2*K+1):
            rn: Poly = {}
            for j in range(1,n+1):
                for (a,b),c in multiply(E[j],R[n-j]).items():
                    add_term(rn,a,b,mp.mpf(j)*c/n)
            R.append(rn)
        out=[]
        for k in range(K+1):
            d=gaussian(R[2*k])
            if floor_phase:
                out.append([d.get(b,mp.mpf(0)) for b in range(2*k+1)])
            else:
                out.append(d.get(0,mp.mpf(0)))
        return out

    def phase_polynomials(self,K: int):
        D=self.coefficients(K,floor_phase=True)
        P=[]
        for k in range(K+1):
            p=[mp.mpf(0)]*(2*k+1)
            for r in range(k+1):
                for degree,value in enumerate(D[r]):
                    p[degree+k-r] += comb(k+1,k-r)*value
            P.append(p)
        return P

    def d1(self,sigma=0,tau=0):
        F,l=self.derivatives(4)
        s=l[1]+sigma
        return (self.E_derivative(1,0)+tau*self.u-(l[2]+s*s)/(2*self.V)
                +F[3]*s/(2*self.V**2)+F[4]/(8*self.V**2)
                -5*F[3]**2/(24*self.V**3))

    def core_inverse(self, Y):
        Y=mp.mpf(Y)
        arg=-self.H*mp.sqrt(self.C/Y)/2
        if arg < -1/mp.e:
            raise ValueError('Y is below the large-branch Lambert threshold')
        return -2*mp.lambertw(arg,-1).real/self.H


def evaluate_poly(p,theta):
    return mp.polyval(list(reversed(p)),theta)


def exact_tables(max_m: int):
    """Exact DP for all A097356 values up to (max_m+1)^2-1, and three
    quadratic subsequences. O(max_m^3) additions and O(max_m^2) storage.
    """
    if not isinstance(max_m,int) or max_m < 1:
        raise ValueError('max_m must be a positive integer')
    N=(max_m+1)**2-1
    dp=[0]*(N+1)
    dp[0]=1
    a=[0]*(N+1)
    a[0]=1
    shifted={s:[1] for s in (-1,0,1)}
    for m in range(1,max_m+1):
        for n in range(m,N+1):
            dp[n]+=dp[n-m]
        for s in shifted:
            shifted[s].append(dp[m*m+s*m])
        for n in range(m*m,min((m+1)**2,N+1)):
            a[n]=dp[n]
    return a,shifted


def log_coefficients(D):
    """ell_k for log(1+sum D_k*z^k), with ell_0=0."""
    L=[mp.mpf(0)]
    for n in range(1,len(D)):
        L.append(D[n]-sum(mp.mpf(k)*L[k]*D[n-k] for k in range(1,n))/n)
    return L


def inverse_coefficients(H,L):
    """q_r in x=X+sum q_r X^{-r}, where H X-2 log X is the core.
    L[k] is the kth logarithmic correction. Uses truncated formal arithmetic.
    """
    K=len(L)-1
    def mul(a,b):
        c=[mp.mpf(0)]*(K+1)
        for i,x in enumerate(a):
            for j,y in enumerate(b[:K+1-i]):
                c[i+j]+=x*y
        return c
    def pwr(a,j):
        out=[mp.mpf(1)]+[mp.mpf(0)]*K
        for _ in range(j):
            out=mul(out,a)
        return out
    q=[mp.mpf(0)]*(K+1)
    for r in range(1,K+1):
        T=[mp.mpf(0)]+q[:K]  # T=t*Delta
        residual=[mp.mpf(0)]*(K+1)
        for j in range(1,K+1):
            P=pwr(T,j)
            for i in range(K+1):
                residual[i]+=-2*(-1)**(j+1)*P[i]/j
        for k in range(1,K+1):
            for j in range(K-k+1):
                P=pwr(T,j)
                b=(-1)**j*comb(k+j-1,j)
                for i in range(K-k+1):
                    residual[i+k]+=L[k]*b*P[i]
        q[r]=-residual[r]/H
    return q
