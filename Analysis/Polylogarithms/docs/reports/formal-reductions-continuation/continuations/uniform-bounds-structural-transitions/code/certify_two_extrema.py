#!/usr/bin/env python3
"""An exact rational parameter pair with exactly two small radial extrema.

The actual implicit zero is enclosed, not a truncated Taylor polynomial.
The B_j equation is summed through j=17, with explicit geometric tails
for every mixed derivative of total order at most three. Uniform negative
third derivative of Phi(t)=eta(sqrt(t)) proves concavity of Phi'.

Standard-library rational arithmetic only. The interval arithmetic is
imported from the companion certify_radial_degeneracy.py.
"""

from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import json

from certify_radial_degeneracy import I, BITS, log_integer, serialize

N = 18
LOG_TERMS = 100
EXP_TERMS = 100
A = F("1.0014289951689850677")
B = F("0.9974958668828783544")


def scaled_log_integer(n, log2):
    k = n.bit_length()-1
    power2 = 1 << k
    z = F(n-power2, n+power2)
    assert 0 <= z < F(1, 3)
    total, power = F(0), z
    for j in range(LOG_TERMS):
        total += 2*power/(2*j+1)
        power *= z*z
    tail = 2*power/((2*LOG_TERMS+1)*(1-z*z))
    return k*log2+I.make(total, total+tail)


def exp_rational(x):
    assert 0 <= x < 5
    total, term = F(1), F(1)
    for j in range(1, EXP_TERMS+1):
        term *= x/j
        total += term
    omitted = term*x/(EXP_TERMS+1)
    tail = omitted/(1-x/(EXP_TERMS+2))
    return I.make(total, total+tail)


def exp_interval(x):
    return I.make(exp_rational(x.lo).lo, exp_rational(x.hi).hi)


def coefficients():
    log2 = log_integer(2)
    p, h = {}, I.make(0)
    for n in range(1, 2*N+2):
        logarithm = scaled_log_integer(n, log2)
        if n >= 2:
            p[n] = h/exp_interval(A*logarithm)
        h += exp_interval(B*logarithm).reciprocal()
    return p


def falling(n, r):
    return factorial(n)//factorial(n-r)


def partial_polynomial(p, t, v, dt=0, dv=0):
    ans = I.make(0)
    for j in range(dt, N):
        poly = I.make(0)
        for k in range(dv, j+2):
            coefficient = (-1)**(j+1-k)*comb(j+1, k)*2**k*falling(k, dv)
            poly += coefficient*p[2*j+3-k]*v**(k-dv)
        ans += falling(j, dt)*t**(j-dt)*poly
    return ans


def tail_bound(tmax, dt=0, dv=0):
    """Valid for |v|<=1 and 0<=t<=tmax; N>dt, total order <=3.

    |partial_t^r partial_v^s B_j(v)t^j|
    <= 15 (4/3)^s j^(r+s+1) 3^j tmax^(j-r).
    For q=3tmax, j=N+l and d=r+s+1:
    sum_{j>=N} j^d q^j <= q^N N^d d!/(1-q)^(d+1).
    """
    assert 0 < tmax < F(1, 3) and dt+dv <= 3 and N > dt
    q = 3*tmax
    d = dt+dv+1
    return 15*F(4, 3)**dv*tmax**(-dt)*q**N*N**d*factorial(d)/(1-q)**(d+1)


def partial(p, t, v, tmax, dt=0, dv=0):
    result = partial_polynomial(p, t, v, dt, dv)
    error = tail_bound(tmax, dt, dv)
    return result + I.make(-error, error)


def main():
    p = coefficients()
    # The t values and every v endpoint are exact rationals.
    samples = [
        (F(1, 4000), F("0.4999997523696561491537822164489257"),
         F("0.4999997523696561491537822164489258"), -1),
        (F(1, 1000), F("0.4999997523696561491585589286444854"),
         F("0.4999997523696561491585589286444855"), 1),
        (F(7, 4000), F("0.4999997523696561491634252121229728"),
         F("0.4999997523696561491634252121229729"), -1),
    ]
    records = []
    for t, vl, vh, desired_sign in samples:
        at_low = partial(p, I.make(t), I.make(vl), t)
        at_high = partial(p, I.make(t), I.make(vh), t)
        assert at_low.hi < 0 < at_high.lo
        Ev = partial(p, I.make(t), I.make(vl, vh), t, dv=1)
        Et = partial(p, I.make(t), I.make(vl, vh), t, dt=1)
        assert Ev.lo > 0
        U = -Et/Ev
        if desired_sign < 0:
            assert U.hi < 0
        else:
            assert U.lo > 0
        records.append({"t": str(t), "v_lower": str(vl), "v_upper": str(vh),
                        "E_at_lower": serialize(at_low), "E_at_upper": serialize(at_high),
                        "E_v": serialize(Ev), "Phi_prime": serialize(U)})

    # A fixed strip containing the actual implicit root for every t in [0,tmax].
    tmax = F(7, 4000)
    vlow, vhigh = F("0.499999752369655"), F("0.499999752369657")
    tI, vI = I.make(0, tmax), I.make(vlow, vhigh)
    edge_low = partial(p, tI, I.make(vlow), tmax)
    edge_high = partial(p, tI, I.make(vhigh), tmax)
    assert edge_low.hi < 0 < edge_high.lo
    derivatives = {(r, s): partial(p, tI, vI, tmax, r, s)
                   for r in range(4) for s in range(4-r)}
    Ev, Et = derivatives[0, 1], derivatives[1, 0]
    assert Ev.lo > 0
    U = -Et/Ev
    V = -(derivatives[2, 0]+2*derivatives[1, 1]*U+derivatives[0, 2]*U**2)/Ev
    W = -(derivatives[3, 0]+3*derivatives[2, 1]*U+3*derivatives[1, 2]*U**2
          +derivatives[0, 3]*U**3+3*derivatives[1, 1]*V
          +3*derivatives[0, 2]*U*V)/Ev
    assert W.hi < 0
    assert F("-2.1e-10") < W.lo < W.hi < F("-1.9e-10")
    advertised = [(F("-3.158e-17"), F("-3.156e-17")),
                  (F("2.537e-17"), F("2.538e-17")),
                  (F("-3.136e-17"), F("-3.135e-17"))]
    for record, (lo, hi) in zip(records, advertised):
        interval = record["Phi_prime"]
        assert lo < F(interval["lower"]) <= F(interval["upper"]) < hi
        record["advertised_Phi_prime"] = [str(lo), str(hi)]
    data = {
        "status": "Exact rational certificate for the actual angular zero and exactly two radial extrema.",
        "a": str(A), "b": str(B), "precision_bits": BITS,
        "terms_j": N, "log_terms_after_binary_range_reduction": LOG_TERMS,
        "exp_terms": EXP_TERMS, "samples": records,
        "uniform_strip": {"t_lower": "0", "t_upper": str(tmax),
                          "v_lower": str(vlow), "v_upper": str(vhigh),
                          "E_lower_edge": serialize(edge_low), "E_upper_edge": serialize(edge_high),
                          "E_v": serialize(Ev), "Phi_third": serialize(W)},
        "tail_bounds_at_tmax": {f"dt{r}_dv{s}": str(tail_bound(tmax, r, s))
                                for r in range(4) for s in range(4-r)},
        "analytic_dependencies": [
            "The convergent binomial E equation equals the normalized imaginary-part equation.",
            "Opposite E signs and E_v>0 enclose the true root at all sample points and throughout the uniform strip.",
            "The positive-order angular-zero theorem identifies this implicit root with eta_{a,b}.",
            "Implicit differentiation gives Phi'= -E_t/E_v and the displayed formulas for Phi'' and Phi'''.",
            "Uniform Phi'''<0 makes Phi' strictly concave on [0,7/4000]. The three signs -,+,- force exactly two zeros, both simple.",
            "The first critical point lies in t in (1/4000,1/1000) and is a strict minimum; the second lies in (1/1000,7/4000) and is a strict maximum.",
            "No assertion about critical points at larger radii is made."
        ]
    }
    path = Path(__file__).resolve().parents[1]/"data"/"two_extrema_certificate.json"
    path.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"output": str(path), "a": str(A), "b": str(B),
                      "derivative_intervals": [record["advertised_Phi_prime"] for record in records],
                      "Phi_third": data["uniform_strip"]["Phi_third"]}, indent=2))


if __name__ == "__main__":
    main()
