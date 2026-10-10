"""Deterministic Fourier approximation of total variation.

Reference certificates use exact rational input and mpmath.iv elementary
interval arithmetic. Fast NumPy results are explicitly NOT roundoff-certified.
See the accompanying article for the analytic certificates and complexity.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Sequence, Any
import math
import numpy as np
from mpmath import iv

Rational = Fraction | int | str


def rational(x: Rational) -> Fraction:
    if isinstance(x, float):
        raise TypeError("Use Fraction or a decimal/rational string, not a float.")
    return Fraction(x)


def _row(xs: Sequence[Rational]) -> tuple[Fraction, ...]:
    r = tuple(rational(x) for x in xs)
    if not r or any(x < 0 for x in r) or sum(r) != 1:
        raise ValueError("Each probability row must be nonempty, nonnegative, and sum exactly to 1.")
    return r


def _ivq(q: Fraction | int):
    q = Fraction(q)
    return iv.mpf(q.numerator) / iv.mpf(q.denominator)


def _dyadic(t: tuple[int, int, int, int]) -> Fraction:
    sign, mantissa, exponent, _ = t
    value = Fraction(-mantissa if sign else mantissa)
    return value * (2 ** exponent) if exponent >= 0 else value / (2 ** (-exponent))


def bounds(x) -> tuple[Fraction, Fraction]:
    """Exact dyadic endpoints, not float conversions."""
    if not hasattr(x, "_mpi_"):
        x = iv.mpf(x)
    return _dyadic(x._mpi_[0]), _dyadic(x._mpi_[1])


def _ceil(q: Fraction) -> int:
    return -((-q.numerator) // q.denominator)


def _nonnegative_interval(x):
    lo, hi = bounds(x)
    if hi < 0:
        raise ArithmeticError("An interval contradicts a known nonnegative quantity.")
    return iv.mpf([_ivq(max(Fraction(0), lo)), _ivq(hi)])


def _atom_data(p, q):
    data = []
    for a, b in zip(p, q):
        if a > 0 and b > 0:
            aa, bb = _ivq(a), _ivq(b)
            data.append((iv.sqrt(aa * bb), iv.ln(aa) - iv.ln(bb)))
    return data


def _atom_sum(data, t):
    re, im = iv.mpf(0), iv.mpf(0)
    for w, s in data:
        phase = t * s
        re += w * iv.cos(phase)
        im += w * iv.sin(phase)
    return re, im


def _mul(z, w):
    a, b = z
    c, d = w
    return a * c - b * d, a * d + b * c


@dataclass(frozen=True)
class ProductPair:
    p: tuple[tuple[Fraction, ...], ...]
    q: tuple[tuple[Fraction, ...], ...]

    @classmethod
    def create(cls, p, q) -> "ProductPair":
        pp, qq = tuple(map(_row, p)), tuple(map(_row, q))
        if not pp or len(pp) != len(qq) or any(len(a) != len(b) for a, b in zip(pp, qq)):
            raise ValueError("Products need the same nonempty list of alphabet sizes.")
        return cls(pp, qq)

    @property
    def input_size(self) -> int:
        return sum(map(len, self.p))

    def lower_bound(self) -> Fraction:
        # A singleton cylinder gives a rational lower bound without rational
        # addition across an entire alphabet.
        return max(abs(a-b) for p, q in zip(self.p, self.q) for a, b in zip(p, q))

    def common_mass(self) -> Fraction:
        pc, qc = Fraction(1), Fraction(1)
        for p, q in zip(self.p, self.q):
            pc *= sum(a for a, b in zip(p, q) if a > 0 and b > 0)
            qc *= sum(b for a, b in zip(p, q) if a > 0 and b > 0)
        return pc + qc

    def prepare_iv(self):
        data = [_atom_data(p, q) for p, q in zip(self.p, self.q)]
        A = iv.mpf(1)
        for row in data:
            A *= sum((w for w, _ in row), iv.mpf(0))

        def transform(t):
            z = (iv.mpf(1), iv.mpf(0))
            for row in data:
                z = _mul(z, _atom_sum(row, t))
            return z
        return A, transform

    def transform_numpy(self, t: np.ndarray) -> tuple[float, np.ndarray]:
        t = np.asarray(t, dtype=float)
        result = np.ones(t.shape, dtype=complex)
        A = 1.0
        for p, q in zip(self.p, self.q):
            pp, qq = np.array(p, dtype=float), np.array(q, dtype=float)
            keep = (pp > 0) & (qq > 0)
            w = np.sqrt(pp[keep] * qq[keep])
            s = np.log(pp[keep]) - np.log(qq[keep])
            A *= float(w.sum())
            f = np.zeros(t.shape, dtype=complex)
            for weight, shift in zip(w, s):
                f += weight * np.exp(1j * t * shift)
            result *= f
        return A, result


@dataclass(frozen=True)
class MarkovPair:
    p0: tuple[Fraction, ...]
    q0: tuple[Fraction, ...]
    p: tuple[tuple[tuple[Fraction, ...], ...], ...]
    q: tuple[tuple[tuple[Fraction, ...], ...], ...]

    @classmethod
    def create(cls, p0, q0, p, q) -> "MarkovPair":
        pp0, qq0 = _row(p0), _row(q0)
        pp = tuple(tuple(map(_row, matrix)) for matrix in p)
        qq = tuple(tuple(map(_row, matrix)) for matrix in q)
        r = len(pp0)
        if len(qq0) != r or len(pp) != len(qq):
            raise ValueError("Incompatible Markov laws.")
        if any(len(M) != r or any(len(row) != r for row in M) for M in pp+qq):
            raise ValueError("All transition matrices must have the same state size.")
        return cls(pp0, qq0, pp, qq)

    @property
    def input_size(self) -> int:
        return len(self.p0) + len(self.p)*len(self.p0)**2

    def lower_bound(self) -> Fraction:
        # Initial and adjacent-pair cylinder probabilities detect equality of
        # fully observed Markov path laws, including unreachable states.
        r, s = list(self.p0), list(self.q0)
        ell = max(abs(a-b) for a, b in zip(r, s))
        for P, Q in zip(self.p, self.q):
            size = len(r)
            rp = [[r[x]*P[x][y] for y in range(size)] for x in range(size)]
            sq = [[s[x]*Q[x][y] for y in range(size)] for x in range(size)]
            ell = max(ell, max(abs(rp[x][y]-sq[x][y]) for x in range(size) for y in range(size)))
            r = [sum(rp[x][y] for x in range(size)) for y in range(size)]
            s = [sum(sq[x][y] for x in range(size)) for y in range(size)]
        return ell

    def common_mass(self) -> Fraction:
        r = [a if a > 0 and b > 0 else Fraction(0) for a, b in zip(self.p0, self.q0)]
        s = [b if a > 0 and b > 0 else Fraction(0) for a, b in zip(self.p0, self.q0)]
        size = len(r)
        for P, Q in zip(self.p, self.q):
            r = [sum(r[x]*P[x][y] for x in range(size) if P[x][y] > 0 and Q[x][y] > 0) for y in range(size)]
            s = [sum(s[x]*Q[x][y] for x in range(size) if P[x][y] > 0 and Q[x][y] > 0) for y in range(size)]
        return sum(r)+sum(s)

    def prepare_iv(self):
        size = len(self.p0)
        def datum(a, b):
            if a == 0 or b == 0:
                return iv.mpf(0), iv.mpf(0)
            aa, bb = _ivq(a), _ivq(b)
            return iv.sqrt(aa*bb), iv.ln(aa)-iv.ln(bb)
        initial = [datum(a,b) for a,b in zip(self.p0,self.q0)]
        matrices = [[[datum(P[x][y],Q[x][y]) for y in range(size)] for x in range(size)] for P,Q in zip(self.p,self.q)]

        def transform(t):
            v = [(w*iv.cos(t*s),w*iv.sin(t*s)) for w,s in initial]
            for M in matrices:
                out = []
                for y in range(size):
                    re, im = iv.mpf(0), iv.mpf(0)
                    for x in range(size):
                        w,s = M[x][y]
                        a,b = _mul(v[x], (w*iv.cos(t*s),w*iv.sin(t*s)))
                        re += a
                        im += b
                    out.append((re,im))
                v = out
            return sum((z[0] for z in v),iv.mpf(0)), sum((z[1] for z in v),iv.mpf(0))
        A = transform(iv.mpf(0))[0]
        return A, transform

    def transform_numpy(self, t: np.ndarray) -> tuple[float, np.ndarray]:
        t = np.asarray(t,dtype=float)
        size=len(self.p0)
        def data(P,Q):
            P,Q=np.array(P,dtype=float),np.array(Q,dtype=float)
            keep=(P>0)&(Q>0)
            w=np.sqrt(P*Q)
            s=np.zeros(P.shape)
            s[keep]=np.log(P[keep])-np.log(Q[keep])
            return w,s
        w,s=data(self.p0,self.q0)
        v=w[None,:]*np.exp(1j*t[:,None]*s[None,:])
        av=w.copy()
        for P,Q in zip(self.p,self.q):
            w,s=data(P,Q)
            out=np.zeros_like(v)
            for x in range(size):
                for y in range(size):
                    out[:,y] += v[:,x]*w[x,y]*np.exp(1j*t*s[x,y])
            v=out
            av=av@w
        return float(av.sum()),v.sum(axis=1)


Pair = ProductPair | MarkovPair


@dataclass(frozen=True)
class Certificate:
    estimate: Fraction
    lower: Fraction
    upper: Fraction
    tolerance: Fraction
    nodes: int
    decimal_precision: int
    mode: str
    ell: Fraction = Fraction(0)
    quadrature_lower: Fraction = Fraction(0)
    quadrature_upper: Fraction = Fraction(0)

    def as_dict(self) -> dict[str,Any]:
        return {k: str(v) if isinstance(v,Fraction) else v for k,v in vars(self).items()}


def relative_certificate(pair: Pair, epsilon: Rational="0.1", dps: int=40,
                         max_nodes: int=2_000_000, max_dps: int=4096) -> Certificate:
    """Return exact rational endpoints enclosing the true TV distance.

    The theorem is unconditional mathematics. The computed enclosure additionally
    relies on mpmath.iv's directed elementary interval operations. It is not a
    proof-assistant-checked implementation. Resource limits raise, never silently
    relax the requested guarantee. iv precision is restored; calls are not thread-safe.
    """
    eps=rational(epsilon)
    if not 0 < eps <= 1:
        raise ValueError("epsilon must lie in (0,1].")
    ell0=pair.lower_bound()
    if ell0==0:
        return Certificate(Fraction(0),Fraction(0),Fraction(0),eps,0,dps,"exact-equality")
    old_dps=iv.dps
    try:
        while dps <= max_dps:
            iv.dps=dps
            A,F=pair.prepare_iv()
            alo,ahi=bounds(A)
            if ahi==0:
                return Certificate(Fraction(1),Fraction(1),Fraction(1),eps,0,dps,"exact-disjoint")
            # A probability-law affinity belongs to [0,1].
            alo,ahi=max(Fraction(0),alo),min(Fraction(1),ahi)
            if ahi-alo > ell0:
                dps*=2
                continue
            ell=max(ell0,1-ahi)
            a=eps/4
            T=8/(eps*ell)
            ai,Ti,ei=_ivq(a),_ivq(T),_ivq(eps)
            W=iv.ln(Ti/ai)
            V=1+iv.ln(1+4*Ti**2)/3
            m=max(1,_ceil(bounds(4*V*W/ei)[1]))
            if m>max_nodes:
                raise RuntimeError(f"The certified plan needs {m} nodes, exceeding max_nodes={max_nodes}.")
            h=W/m
            B=1-A
            for j in range(m):
                t=ai*iv.exp(h*_ivq(Fraction(2*j+1,2)))
                re,_=F(t)
                H=_nonnegative_interval(A-re)
                B += h*t/(iv.pi*(t*t+_ivq(Fraction(1,4))))*H
            blo,bhi=bounds(B)
            if bhi-blo > eps*ell/2:
                dps*=2
                continue
            lo=max(Fraction(0),ell0,blo/(1+eps/8))
            hi=min(Fraction(1),(bhi+eps*ell/12)/(1-7*eps/48))
            est=min(hi,max(lo,(blo+bhi)/2))
            if lo>hi or not lo<=est<=hi:
                raise ArithmeticError("Internal certificate inconsistency.")
            return Certificate(est,lo,hi,eps,m,dps,"relative-log-frequency-interval",ell,blo,bhi)
        raise RuntimeError("Interval evaluation did not meet its error budget before max_dps.")
    finally:
        iv.dps=old_dps


def relative_fast(pair: Pair, epsilon: float=0.1) -> dict[str,Any]:
    """NumPy prototype; analytic interval ignores roundoff and is NOT certified."""
    if not 0<epsilon<=1:
        raise ValueError("epsilon must lie in (0,1].")
    l0=float(pair.lower_bound())
    if l0==0:
        if pair.lower_bound()!=0:
            raise FloatingPointError("Lower bound underflows; use relative_certificate.")
        return dict(estimate=0.0,lower=0.0,upper=0.0,nodes=0,certified=False)
    A,_=pair.transform_numpy(np.array([0.0]))
    if A==0:
        # Underflow is indistinguishable from disjointness in this prototype.
        return dict(estimate=1.0,lower=1.0,upper=1.0,nodes=0,certified=False)
    ell=max(l0,1-A)
    a=epsilon/4
    T=8/(epsilon*ell)
    W=math.log(T/a)
    V=1+math.log1p(4*T*T)/3
    m=math.ceil(4*V*W/epsilon)
    h=W/m
    t=a*np.exp(h*(np.arange(m)+0.5))
    A,F=pair.transform_numpy(t)
    B=1-A+float(np.sum(h*t/(math.pi*(t*t+0.25))*(A-F.real)))
    return dict(estimate=min(1,max(0,B)),lower=max(0,B/(1+epsilon/8)),
                upper=min(1,(B+epsilon*ell/12)/(1-7*epsilon/48)),nodes=m,
                affinity=A,ell=ell,certified=False)


@dataclass
class PeriodicTable:
    L: int
    K: int
    rho_upper: Fraction
    A_upper: Fraction
    common_mass: Fraction
    coefficients: list[Any]
    transforms: list[tuple[Any,Any]]
    dps: int


def periodic_table(pair: Pair, epsilon: Rational="0.01", dps: int=40) -> PeriodicTable:
    eps=rational(epsilon)
    if not 0<eps<=1:
        raise ValueError("epsilon must lie in (0,1].")
    r=0
    while Fraction(1,2**r)>eps/16:
        r+=1
    L=2*r
    K=max(1,_ceil(2*L/(9*eps)))
    old=iv.dps
    try:
        iv.dps=dps
        A,F=pair.prepare_iv()
        cs,fs=[],[]
        for j in range(K+1):
            t=2*iv.pi*j/L
            cs.append(1/(L*(_ivq(Fraction(1,4))+t*t)))
            fs.append(F(t) if j else (A,iv.mpf(0)))
        return PeriodicTable(L,K,Fraction(1,2**r),min(Fraction(1),bounds(A)[1]),
                             pair.common_mass(),cs,fs,dps)
    finally:
        iv.dps=old


def periodic_tv_certificate(table: PeriodicTable, epsilon: Rational="0.01") -> Certificate:
    old=iv.dps
    try:
        iv.dps=table.dps
        S=table.coefficients[0]*table.transforms[0][0]
        for c,(re,_) in zip(table.coefficients[1:],table.transforms[1:]):
            S+=2*c*re
        slo,shi=bounds(S)
        tail=table.A_upper*table.L/(18*table.K)
        alias=table.common_mass*table.rho_upper/(1-table.rho_upper)
        lo=max(Fraction(0),1-shi-tail)
        hi=min(Fraction(1),1-slo+tail+alias)
        return Certificate((lo+hi)/2,lo,hi,rational(epsilon),table.K+1,table.dps,"additive-periodic-interval")
    finally:
        iv.dps=old


def bayes_risk_certificate(table: PeriodicTable, alpha: Rational) -> tuple[Fraction,Fraction]:
    """Pointwise enclosure using a table with simultaneous analytic error control."""
    a=rational(alpha)
    if not 0<=a<=1:
        raise ValueError("Prior must lie in [0,1].")
    if a==0 or a==1:
        return Fraction(0),Fraction(0)
    old=iv.dps
    try:
        iv.dps=table.dps
        shift=iv.ln(_ivq(a))-iv.ln(_ivq(1-a))
        S=table.coefficients[0]*table.transforms[0][0]
        for j,(c,(re,im)) in enumerate(zip(table.coefficients[1:],table.transforms[1:]),1):
            phase=2*iv.pi*j/table.L*shift
            S+=2*c*(re*iv.cos(phase)-im*iv.sin(phase))
        S*=iv.sqrt(_ivq(a*(1-a)))
        slo,shi=bounds(S)
        tail=table.A_upper*table.L/(36*table.K)
        alias=table.rho_upper/(1-table.rho_upper)
        return max(Fraction(0),slo-tail-alias),min(a,1-a,shi+tail)
    finally:
        iv.dps=old
