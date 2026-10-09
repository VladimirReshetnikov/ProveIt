"""Sharp skewness-conditioned envelopes for centered Gaussian quadratic forms.

The routines evaluate formulas proved in article.tex. Floating-point evaluations
are diagnostics, not interval-certified proofs. Coefficients are real eigenvalues.
"""
from __future__ import annotations
import math
from typing import Iterable
import numpy as np


def parameters(delta: float) -> tuple[float, float]:
    """Return a,b >= 0 with a*a+b*b=1 and a**3-b**3=delta."""
    delta = float(delta)
    if not math.isfinite(delta) or abs(delta) > 1.0 + 2e-13:
        raise ValueError("delta must be finite and in [-1,1]")
    delta = max(-1.0, min(1.0, delta))
    if delta == 1.0:
        return 1.0, 0.0
    if delta == -1.0:
        return 0.0, 1.0
    c = 2.0 * math.sin(math.asin(delta) / 3.0)
    s = math.sqrt(max(0.0, 2.0-c*c))
    return (s+c)/2.0, (s-c)/2.0


def normalize(coefficients: Iterable[float]) -> tuple[np.ndarray, float, float]:
    """Return normalized spectrum, Frobenius norm, and normalized third trace."""
    z = np.asarray(list(coefficients), dtype=float)
    if z.ndim != 1 or not z.size or not np.all(np.isfinite(z)):
        raise ValueError("a nonempty finite real coefficient vector is required")
    scale = float(np.max(np.abs(z)))
    if scale == 0.0:
        raise ValueError("the zero form is handled separately")
    scaled = z/scale
    length = math.sqrt(float(np.dot(scaled, scaled)))
    norm = scale * length
    if not math.isfinite(norm):
        raise OverflowError("Frobenius norm exceeds the floating-point range")
    z = scaled/length
    delta = float(np.sum(z*z*z))
    return z, norm, delta


def centered_moments(coefficients: Iterable, max_order: int) -> list:
    """Cumulant recurrence; integer/Fraction inputs give exact arithmetic."""
    z = list(coefficients)
    if max_order < 0 or int(max_order) != max_order:
        raise ValueError("max_order must be a nonnegative integer")
    max_order = int(max_order)
    kappa = [0]*(max_order+1)
    for r in range(2, max_order+1):
        kappa[r] = 2**(r-1)*math.factorial(r-1)*sum(c**r for c in z)
    m = [0]*(max_order+1)
    m[0] = 1
    for n in range(2, max_order+1):
        m[n] = sum(math.comb(n-1, r-1)*kappa[r]*m[n-r]
                   for r in range(2, n+1))
    return m


def log_mgf(coefficients: Iterable[float], t: float) -> float:
    z = np.asarray(list(coefficients), dtype=float)
    if z.ndim != 1 or not np.all(np.isfinite(z)) or not math.isfinite(t):
        raise ValueError("a finite one-dimensional spectrum and finite t are required")
    u = 2*t*z
    if np.any(u >= 1):
        return math.inf
    # log1p keeps the logarithm accurate near t=0; mild cancellation remains.
    return float(np.sum((-u - np.log1p(-u))/2))


def envelope_log_mgf(delta: float, t: float) -> float:
    a, b = parameters(delta)
    return log_mgf([a, -b], t)


def kurtosis_frontier(delta: float, standardized: bool = True) -> float:
    a, b = parameters(delta)
    m4 = 12 + 48*(a**4+b**4)
    return m4/4 if standardized else m4


def rigidity(coefficients: Iterable[float]) -> dict[str, float]:
    z, norm, delta = normalize(coefficients)
    a, b = parameters(delta)
    u = max(0.0, float(np.max(z)))
    v = max(0.0, float(np.max(-z)))
    defect = a**4+b**4-float(np.sum(z**4))
    distance_squared = max(0.0, 2-2*(a*u+b*v))
    if min(a,b) == 0:
        constant = 0.0  # the only admissible spectra are already extremizers
    else:
        constant = 2/min((a+b)*min(a,b), a**4+b**4)
    return {"norm": norm, "delta": delta, "a": a, "b": b,
            "fourth_trace_defect": defect, "distance_squared": distance_squared,
            "rigidity_constant": constant}


def chernoff(delta: float, x: float) -> tuple[float, float, float]:
    """Return right-tail Chernoff bound, rate I, and optimizing t for x>=0.

    The variable is normalized to Frobenius norm one, hence variance two.
    No claim of pointwise stochastic domination by the two-mode law is made.
    """
    if not math.isfinite(x) or x < 0:
        raise ValueError("x must be finite and nonnegative")
    a, b = parameters(delta)
    if x == 0:
        return 1.0, 0.0, 0.0
    if a == 0:
        if x >= 1:
            return 0.0, math.inf, math.inf
        t = x/(2*(1-x))
        rate = (-x-math.log1p(-x))/2
        return math.exp(-rate), rate, t
    if b == 0:
        t = (x/(1+x))/2
        rate = (x-math.log1p(x))/2
        return math.exp(-rate), rate, t
    c, d = a-b, a*b
    # Scale the quadratic root by x when x is large, avoiding both
    # overflow in the discriminant and cancellation near delta=-1.
    if x >= 1:
        root_scaled = math.hypot(math.sqrt(1+2*d)*(1+c/x), 2*d/x)
        linear_scaled = c+1/x
        if linear_scaled < 0:
            t = (root_scaled-linear_scaled)/(4*d*(1+c/x))
        else:
            t = 1/(linear_scaled+root_scaled)
    else:
        root = math.hypot(math.sqrt(1+2*d)*(x+c), 2*d)
        linear = 1+c*x
        t = x/(linear+root)
    q = 1+2*b*t
    # Stationarity gives 1-2*a*t = a/(x+c+b/q). Use this form
    # when positive to retain a small distance from the MGF pole.
    positive_factor = a/(x+c+b/q) if x+c > 0 else 1-2*a*t
    if not positive_factor > 0:
        raise ArithmeticError("insufficient floating-point precision at the MGF pole")
    rate = max(0.0, t*(x+c)+(math.log(positive_factor)+math.log(q))/2)
    return math.exp(-rate), rate, t


def zero_skew_absolute_moment(p: float) -> float:
    if not math.isfinite(p) or p <= -1:
        raise ValueError("p must be finite and > -1")
    return math.exp(1.5*p*math.log(2)+2*math.lgamma((p+1)/2)-math.log(math.pi))
