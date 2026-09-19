"""Positive-series algorithms for subcritical tetration (0 < q < 1).

All numerical answers use arbitrary-precision floating point, not interval
arithmetic. The Koenigs truncation enclosure is a proved analytic bound;
roundoff is not included in that enclosure. No claim of certified floating-
point evaluation is made. Set mp.dps BEFORE constructing a model.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import List, Optional, Tuple
from mpmath import mp


def checked_q(q):
    q = mp.mpf(q)
    if not (0 < q < 1):
        raise ValueError("q must be real and strictly between 0 and 1")
    return q


def koenigs_enclosure(q, u=1, digits: Optional[int] = None,
                       max_steps: int = 1_000_000):
    """Return (lower, upper, iterations) for Phi_q(u), excluding roundoff.

    u_j = 1-exp(-q*u_{j-1}), Phi_n = u_n/q**n, and
    Phi_n*exp(-q*u_n/(2*(1-q))) <= Phi(u) <= Phi_n.
    The requested relative enclosure width is approximately 10**(-digits).
    """
    q = checked_q(q)
    u = mp.mpf(u)
    if u < 0:
        raise ValueError("u must be nonnegative")
    if digits is None:
        digits = max(10, mp.dps - 15)
    if digits <= 0 or max_steps < 1:
        raise ValueError("digits and max_steps must be positive")
    if u == 0:
        return mp.mpf(0), mp.mpf(0), 0
    threshold = mp.power(10, -digits)
    qn = mp.mpf(1)
    for n in range(max_steps + 1):
        eta = q*u/(2*(1-q))
        if eta < threshold:
            upper = u/qn
            return upper*mp.exp(-eta), upper, n
        if n == max_steps:
            break
        u = -mp.expm1(-q*u)
        qn *= q
    raise ArithmeticError("Koenigs enclosure did not reach the requested tolerance")


@dataclass
class TetrationModel:
    """T(z)=L*(1-sum(b[n]*q**(n*(z+2)), n>=1)).

    b[n] are coefficients of H(R*v), with radius exactly one.
    The finite coefficient list is a truncation, NOT an adaptive guarantee.
    """
    q: object
    L: object
    a: object
    R: object
    R_lower: object
    R_upper: object
    b: List[object]
    koenigs_steps: int
    dps: int

    @classmethod
    def build(cls, q, terms: int = 400, digits: Optional[int] = None):
        q = checked_q(q)
        if not isinstance(terms, int) or terms < 2:
            raise ValueError("terms must be an integer >= 2")
        lo, hi, steps = koenigs_enclosure(q, digits=digits)
        Rlo, Rhi = lo/q, hi/q
        R = (Rlo+Rhi)/2
        b = [mp.mpf(0)]*(terms+1)
        b[1] = R
        qp = [mp.power(q,j) for j in range(terms+1)]
        # Differentiate q*H(s) = -log(1-H(q*s)); this avoids Bell polynomials.
        for n in range(2, terms+1):
            b[n] = mp.fsum((n-j)*b[n-j]*b[j]*qp[j]
                           for j in range(1,n))/(n*(1-qp[n-1]))
        L = mp.exp(q)
        return cls(q,L,mp.exp(q/L),R,Rlo,Rhi,b,steps,mp.dps)

    def evaluate(self, z, terms: Optional[int] = None):
        z = mp.mpc(z)
        if mp.re(z) <= -2:
            raise ValueError("The positive power series requires Re(z)>-2")
        terms = len(self.b)-1 if terms is None else terms
        if not (1 <= terms < len(self.b)):
            raise ValueError("terms outside the precomputed range")
        v = mp.power(self.q, z+2)
        # Horner evaluation, retaining exact normalization outside the sum.
        s = mp.mpc(0)
        for n in range(terms,0,-1):
            s = (s+self.b[n])*v
        return self.L*(1-s)

    def derivative(self, z, order: int = 1):
        if not isinstance(order,int) or order < 1:
            raise ValueError("order must be a positive integer")
        z = mp.mpc(z)
        if mp.re(z) <= -2:
            raise ValueError("Re(z)>-2 required")
        v = mp.power(self.q,z+2)
        return -self.L*mp.fsum(self.b[n]*mp.power(v,n)*
                    mp.power(n*mp.log(self.q),order)
                    for n in range(1,len(self.b)))

    def scaled_newton_coefficients(self, N: int):
        """Return A[n]/q**(2*n), n>=1, by a positive summation.

        A[n] = F[1,q,...,q**n], F(w)=T(log(w)/log(q)).
        The omitted spectral tail and all floating-point errors are unbounded
        by this routine. Increase both terms and mp.dps to check stability.
        """
        if N < 1 or N >= len(self.b):
            raise ValueError("Need 1 <= N < the number of stored coefficients")
        q = self.q
        M = len(self.b)-1
        qp = [mp.power(q,j) for j in range(M+1)]
        out = [mp.nan]
        for n in range(1,N+1):
            gauss = mp.mpf(1)
            power = mp.mpf(1)
            summands = [self.b[n]]
            for k in range(1,M-n+1):
                gauss *= (1-qp[n+k])/(1-qp[k])
                power *= q*q
                summands.append(self.b[n+k]*power*gauss)
            out.append(-self.L*mp.fsum(summands))
        return out

    def newton_partial_sums(self, z, scaled_coefficients):
        """Stable finite Newton sums, including on/outside the boundary.

        This is a POLYNOMIAL evaluation, not an assertion of convergence.
        """
        w = mp.power(self.q,mp.mpc(z))
        v = self.q*self.q*w
        partial = mp.mpc(1)
        result = [partial]
        product = mp.mpc(1)
        vn = mp.mpc(1)
        qj = mp.mpf(1)
        for n in range(1,len(scaled_coefficients)):
            product *= 1-qj/w
            vn *= v
            partial += scaled_coefficients[n]*vn*product
            result.append(partial)
            qj *= self.q
        return result


def qbinomial(n: int, k: int, q):
    """Gaussian binomial at integer n,k, using a finite product."""
    if k < 0 or k > n:
        return mp.mpf(0)
    k = min(k,n-k)
    return mp.fprod((1-q**(n-k+j))/(1-q**j) for j in range(1,k+1))


def original_qnewton_partial(q, z, N: int):
    """Literal double-sum formula from the 2017 conjecture.

    This deliberately cancellation-prone implementation is for independent
    small-N cross-checks. It is not the recommended evaluation method.
    """
    q = checked_q(q)
    if N < 0:
        raise ValueError("N must be nonnegative")
    L = mp.exp(q)
    loga = q/L
    towers = [mp.mpf(1)]
    for _ in range(N):
        towers.append(mp.exp(loga*towers[-1]))
    total = towers[0]
    qz = mp.power(q,z)
    basis = mp.mpc(1)
    for n in range(1,N+1):
        beta = mp.fsum((-1)**(n-k)*q**((n-k)*(n-k-1)//2)*
                       qbinomial(n,k,q)*towers[k] for k in range(n+1))
        basis *= (1-qz*q**(-(n-1)))/(1-q**n)
        total += beta*basis
    return total
