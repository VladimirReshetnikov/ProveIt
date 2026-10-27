"""Integer-only schedules and analytic constants for balanced ETH contraction.

These are parameter routines, not an end-to-end tensor contractor or SAT solver.
The adaptive schedule is the schedule proved in report.tex.
"""
from dataclasses import dataclass
from fractions import Fraction
from math import isqrt, log, log2, pi, sqrt

def ceil_log2(n):
    if not isinstance(n, int) or n < 1:
        raise ValueError("positive integer required")
    return (n - 1).bit_length()

def ceil_nth_root(n, k):
    if n < 0 or k < 1:
        raise ValueError("nonnegative n and positive k required")
    if n <= 1:
        return n
    lo, hi = 0, 1 << ((n.bit_length() + k - 1) // k)
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid ** k >= n:
            hi = mid
        else:
            lo = mid
    return hi

@dataclass(frozen=True)
class Schedule:
    s: int
    r: int
    b: int
    lam: int
    delta: int
    guard: int
    depth_budget: int
    reserve: int
    cap: int
    taper_budget: int

    @classmethod
    def build(cls, s, r=54, b=9):
        if s < 2 or r < 7 or not (1 < b and 2*b < r):
            raise ValueError("require s>=2, r>=7 and 1<b<r/2")
        lam = ceil_log2(s)
        delta = ceil_nth_root(s ** 9, 10)
        guard = ceil_log2((lam + 1) ** 8)
        depth_budget = ceil_log2(lam)
        reserve = (depth_budget + 1) * guard
        room = s // (4 * delta * lam ** 6)
        cap = -1
        if room >= 1:
            cap = 0
            while room >= r * r:
                room //= r * r
                cap += 1
        return cls(s, r, b, lam, delta, guard, depth_budget,
                   reserve, cap, cap - reserve)

    @property
    def root_fallback(self):
        return self.lam < 4 or self.cap < 0 or self.taper_budget <= 0

    def u(self, d):
        if d < 0:
            raise ValueError("nonnegative depth required")
        if self.taper_budget <= 0:
            return 0
        return ((self.b - 1) * self.taper_budget) // self.b ** (d + 1)

    def a(self, d):
        if d < 0:
            return 0
        return sum(self.u(j) for j in range(d + 1)) + (d + 1) * self.guard

    def active_fallback(self, M, d):
        if M <= (self.s + self.lam - 1) // self.lam:
            return True
        return self.root_fallback or self.u(d) == 0

def taper_slope(M, a, u):
    if M < 1 or not 1 <= u <= a:
        raise ValueError("require M>=1 and 1<=u<=a")
    L = 1 << a
    W = sum((L >> i) * (u - i) for i in range(u))
    numerator = M * (2 * L - 1) + 1
    return (numerator + W - 1) // W

def safe_precision(p, M, a, u, i):
    if not 0 <= i < u:
        raise ValueError("retained valuation required")
    h = taper_slope(M, a, u)
    D = 1 << (a - i)
    return p + 6 * h * D + h * u * (a + 1)

def cauchy_weight(b):
    if b < 0:
        raise ValueError("nonnegative mode index required")
    return 3 * b + 1 - 2 * b.bit_count()

def tuple_count(precision, colors, factorial=True):
    """Count all nonnegative tuples of weight < precision, infinite mode range."""
    if precision < 1 or colors < 0:
        raise ValueError("invalid count parameters")
    dp = [1] + [0] * (precision - 1)
    weights, b = [], 0
    while True:
        w = cauchy_weight(b) if factorial else b + 1
        if w >= precision:
            break
        weights.append(w)
        b += 1
    for _ in range(colors):
        for w in weights:
            for p in range(w, precision):
                dp[p] += dp[p - w]
    return sum(dp)

def displayed_constants():
    old = 2*pi*sqrt(4320)/(log(2)*(1-(3/128)*sqrt(12)))
    cstar = 9*pi/(4*log(2))*sqrt(15*log2(54))
    return {
        "prior_best_explicit": old,
        "prior_optimized_boundary_at_r251": 2*pi*sqrt(480*log2(251))/(log(2)*(1-(6/251)**(2/3))**1.5),
        "prior_optimized_boundary_at_r251_plus_cauchy": 2*pi*sqrt(160*log2(251))/(log(2)*(1-(6/251)**(2/3))**1.5),
        "prior_best_plus_cauchy": old/sqrt(3),
        "new_fixed_r64": 2*pi*sqrt(90)/(log(2)*(1-sqrt(10)/32)),
        "new_fixed_r54_eps_2_over_259": 9*pi/(4*log(2))*sqrt(259/3),
        "new_adaptive": cstar,
        "old_explicit_coefficient_over_new": old/cstar,
        "composed_coefficient_over_new": old/sqrt(3)/cstar,
        "interpretation": "Ratios of upper-bound coefficients, not measured runtime ratios."
    }

def atan_interval(x, terms=45):
    """Exact rational interval from the alternating arctangent series."""
    partial = sum(((-1)**j * x**(2*j+1) / (2*j+1)
                   for j in range(terms)), Fraction(0))
    next_term = (-1)**terms * x**(2*terms+1) / (2*terms+1)
    return min(partial, partial + next_term), max(partial, partial + next_term)

def log_interval(x, terms=45):
    """Exact interval for log(x), x>=1, from the positive atanh series."""
    if x < 1:
        raise ValueError("x>=1 required")
    t = (x - 1) / (x + 1)
    lower = 2*sum((t**(2*j+1)/(2*j+1) for j in range(terms)), Fraction(0))
    tail = 2*t**(2*terms+1)/((2*terms+1)*(1-t*t))
    return lower, lower + tail

def certified_cstar_interval(digits=12):
    """Rigorous rational enclosure of the coefficient, not floating point."""
    a, b = atan_interval(Fraction(1,5)), atan_interval(Fraction(1,239))
    pil, piu = 16*a[0]-4*b[1], 16*a[1]-4*b[0]  # Machin's identity.
    l2, l27_16 = log_interval(Fraction(2)), log_interval(Fraction(27,16))
    l54 = (5*l2[0]+l27_16[0], 5*l2[1]+l27_16[1])
    low2 = Fraction(1215,16)*pil*pil*l54[0]/l2[1]**3
    high2 = Fraction(1215,16)*piu*piu*l54[1]/l2[0]**3
    scale = 10**digits
    lower = isqrt(low2.numerator*scale*scale//low2.denominator)
    upper = isqrt(high2.numerator*scale*scale//high2.denominator)
    if upper*upper*high2.denominator < high2.numerator*scale*scale:
        upper += 1
    return Fraction(lower,scale), Fraction(upper,scale)
