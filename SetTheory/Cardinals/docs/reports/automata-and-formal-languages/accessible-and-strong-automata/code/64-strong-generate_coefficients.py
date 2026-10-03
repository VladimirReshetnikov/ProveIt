"""Generate any requested fixed-order strongly-connected automata coefficients.

Uses finite formal power-series arithmetic, Gaussian saddle moments, exact
Uniform[0,1] endpoint moments, and analytically evaluated Fuss-Catalan moments.
No numerical fitting is used. Working precision includes a large-k allowance
for exponentially small rho. Numeric output is not an interval certificate or
a guarantee of every requested digit; replay with higher --digits or
--guard-digits to test stability.

Requires mpmath and sympy. Example:
  python generate_coefficients.py --k 2 --order 5 --digits 80
"""
import argparse
import json
from math import comb, factorial
import mpmath as mp
import sympy as sp


def imaginary_unit_power(m):
    """Exact four-cycle, avoiding built-in complex-power phase roundoff."""
    return (1, mp.j, -1, -mp.j)[m % 4]


def mul(a, b, N):
    out = [mp.mpf(0) for _ in range(N + 1)]
    for i in range(min(len(a), N + 1)):
        for j in range(min(len(b), N + 1 - i)):
            out[i + j] += a[i] * b[j]
    return out


def inv(a, N):
    out = [1 / a[0]] + [mp.mpf(0)] * N
    for j in range(1, N + 1):
        out[j] = -sum(a[i] * out[j - i]
                      for i in range(1, min(j + 1, len(a)))) / a[0]
    return out


def exp_series(a, N):
    out = [mp.exp(a[0])] + [mp.mpf(0)] * N
    for j in range(1, N + 1):
        out[j] = sum(i * a[i] * out[j - i]
                     for i in range(1, min(j + 1, len(a)))) / j
    return out


def log_series(a, N):
    derivative = [(i + 1) * a[i + 1] for i in range(min(N, len(a) - 1))]
    ratio = mul(derivative, inv(a, N), N - 1)
    return [mp.log(a[0])] + [ratio[i - 1] / i for i in range(1, N + 1)]


def pmul(a, b):
    out = {}
    for i, x in a.items():
        for j, y in b.items():
            out[i + j] = out.get(i + j, 0) + x * y
    return out


def saddle(kappa, amplitude, J):
    """Relative saddle series for a multiplier with log-derivatives amplitude."""
    N = 2 * J
    variance = kappa[2]
    Q = [{} for _ in range(N + 1)]
    for m in range(3, N + 3):
        Q[m - 2][m] = kappa[m] * imaginary_unit_power(m) / (factorial(m) * variance ** (mp.mpf(m) / 2))
    for m in range(1, N + 1):
        Q[m][m] = Q[m].get(m, 0) + amplitude[m] * imaginary_unit_power(m) / (
            factorial(m) * variance ** (mp.mpf(m) / 2))
    E = [{0: mp.mpf(1)}] + [{} for _ in range(N)]
    for j in range(1, N + 1):
        for ell in range(1, j + 1):
            for deg, value in pmul(Q[ell], E[j - ell]).items():
                E[j][deg] = E[j].get(deg, 0) + ell * value / j
    out = []
    for j in range(0, N + 1, 2):
        value = sum(value * mp.mpf(factorial(deg)) /
                    (2 ** (deg // 2) * factorial(deg // 2))
                    for deg, value in E[j].items() if deg % 2 == 0)
        out.append(mp.re(value))
    return out


def cumulants(k, v, order):
    z, u = sp.symbols("z u")
    P = z
    out = [mp.mpf(0)]
    for m in range(1, order + 1):
        evaluate = sp.lambdify((z, u), P, "mpmath")
        out.append(evaluate(k * v, 1 - v) / v ** m)
        P = sp.expand(z * ((1 - u) * (sp.diff(P, z) - u * sp.diff(P, u)) - m * u * P))
    return out


def fuss_moments(k, v, order):
    x = sp.symbols("x")
    cx = k * x - k + 1
    c = k * v - k + 1
    P = sp.Integer(1)
    out = []
    for m in range(order + 1):
        out.append(sp.lambdify(x, P, "mpmath")(v) / c ** (2 * m + 1))
        P = sp.expand(-(1 - x) * x * (cx * sp.diff(P, x) - (2 * m + 1) * k * P))
    out[0] -= 1  # exclude r=0
    return out


def interpolate(values):
    """Monomial coefficients from consecutive integer-node values."""
    N = len(values) - 1
    out = [mp.mpf(0)] * (N + 1)
    diff = list(values)
    basis = [mp.mpf(1)]
    for j in range(N + 1):
        for ell, b in enumerate(basis):
            out[ell] += diff[0] * b
        diff = [diff[i + 1] - diff[i] for i in range(len(diff) - 1)]
        basis = mul(basis, [-mp.mpf(j), mp.mpf(1)], j + 1)
        basis = [x / (j + 1) for x in basis]
    return out


def exact_counts(k, N):
    H = [0] * (N + 1)
    for n in range(1, N + 1):
        H[n] = n ** (k * n) - sum(comb(n, h) * n ** (k * (n - h)) * H[h]
                                 for h in range(1, n))
    return [0] + [H[n] // factorial(n) for n in range(1, N + 1)]


def generate(k, J, digits, guard_digits=35):
    if k < 2 or J < 1 or digits < 1 or guard_digits < 1:
        raise ValueError("Need k>=2, order>=1, digits>=1 and guard_digits>=1")
    # Forming 1-rho loses about k/log(10) places for rho approximately exp(-k).
    mp.mp.dps = max(50, digits+guard_digits)
    large_k_digits = int(mp.ceil(mp.mpf(k)/mp.log(10)))+5
    working_digits = digits+guard_digits+large_k_digits
    mp.mp.dps = working_digits
    rho = -mp.lambertw(-k*mp.exp(-k))/k
    v = 1-rho
    if rho <= 0 or 1-v == 0:
        raise ArithmeticError("Lost positive exponentially small rho; increase working precision")
    c = 1-k*rho
    d = k - 1
    kap = cumulants(k, v, 2 * J + 2)
    amp0 = [mp.mpf(0)] * (2 * J + 1)
    S0 = saddle(kap, amp0, J)
    factorial_log = [mp.mpf(0)] * (J + 1)
    for j in range(1, J + 1, 2):
        factorial_log[j] = mp.bernoulli(j + 1) * (mp.mpf(k) ** (-j) - 1) / ((j + 1) * j)
    tau = mul(exp_series(factorial_log, J), S0, J)
    ltau = log_series(tau, J)
    moments = fuss_moments(k, v, 2 * J)

    endpoint = []
    for r in range(2 * J + 1):
        elog = [mp.mpf(0)] * (J + 1)
        for j in range(1, J + 1):
            elog[j] = mp.mpf(d * r ** (j + 1)) / (j * (j + 1)) + mp.mpf(r ** j) / (2 * j)
            elog[j] += sum(ltau[m] * comb(j - 1, m - 1) * r ** (j - m) for m in range(1, j))
        uniform_log = [mp.mpf(0)] * (J + 1)
        uniform_log[1] = mp.mpf(r) / 2
        for j in range(2, J + 1, 2):
            uniform_log[j] = r * mp.bernoulli(j) / (j * factorial(j))
        uniform_mgf = exp_series(uniform_log, J)
        falling = mp.mpf(1)
        Hnorm = []
        for j in range(J + 1):
            Hnorm.append((-1) ** j * falling * uniform_mgf[j])
            falling *= d * r - j
        endpoint.append(mul(exp_series(elog, J), Hnorm, J))

    source = [mp.mpf(0)] * (J + 1)
    hmax = J // d
    a = exact_counts(k, hmax)
    for h in range(1, hmax + 1):
        start = d * h
        N = J - start
        amp = [mp.mpf(0)] * (2 * J + 1)
        for m in range(1, 2 * J + 1):
            amp[m] = h * k * v - h * kap[m] + (k * h if m == 1 else 0)
        S = saddle(kap, amp, N)
        relative = mul(S, inv(S0, N), N)
        numerator = [mp.mpf(1)]
        denominator = [mp.mpf(1)]
        for i in range(h):
            numerator = mul(numerator, [1, -mp.mpf(i)], N)
        for j in range(k * h):
            denominator = mul(denominator, [1, -mp.mpf(j) / k], N)
        relative = mul(relative, mul(numerator, inv(denominator, N), N), N)
        for ell, value in enumerate(relative):
            source[start + ell] += a[h] * v ** start * value

    coeff = [c] + [mp.mpf(0)] * J
    for j in range(1, J + 1):
        values = []
        for r in range(2 * j + 1):
            shifted = [coeff[0]] + [mp.mpf(0)] * j
            for b in range(1, j + 1):
                shifted[b] = sum(coeff[i] * comb(b - 1, i - 1) * r ** (b - i)
                                 for i in range(1, min(b, j - 1) + 1))
            values.append(sum(endpoint[r][ell] * shifted[j - ell] for ell in range(j + 1)))
        polynomial = interpolate(values)
        total = sum(x * moments[ell] for ell, x in enumerate(polynomial))
        coeff[j] = -c * (total + source[j])
    # Transfer via n B_n=n P_n+sum_j(n-j)B_(n-j)P_j.
    # Small-index B values are exact rationals; b contains B_n/T_n.
    from fractions import Fraction
    Bsmall = [Fraction(0)] * (hmax + 1)
    for n in range(1, hmax + 1):
        Bsmall[n] = Fraction(a[n]) + sum(Fraction(n-j, n) * Bsmall[n-j] * a[j]
                                       for j in range(1, n))
    b = [c] + [mp.mpf(0)] * J
    q = rho*v**d
    ratios = {}
    for r in range(1, hmax+1):
        NN = J-d*r
        elog = [mp.mpf(0)]*(NN+1)
        for j in range(1, NN+1):
            elog[j] = mp.mpf(d*r**(j+1))/(j*(j+1)) + mp.mpf(r**j)/(2*j)
            elog[j] += sum(ltau[m]*comb(j-1,m-1)*r**(j-m) for m in range(1,j))
        ratios[r] = [mp.mpf(0)]*(d*r) + [q**r*x for x in exp_series(elog,NN)]
    def shifted(C,r,N):
        return [C[0]] + [sum(C[i]*comb(j-1,i-1)*r**(j-i)
                            for i in range(1,min(j+1,len(C)))) for j in range(1,N+1)]
    for ell in range(1,J+1):
        total = coeff[ell]
        for r in range(1,min(hmax,ell//d)+1):
            right = mul(mul(ratios[r],[1,-mp.mpf(r)],J),shifted(b,r,J),J)
            total += a[r]*right[ell]
            Bs = mp.mpf(Bsmall[r].numerator)/Bsmall[r].denominator
            left = mul(ratios[r],shifted(coeff,r,J),J)
            total += r*Bs*left[ell-1]
        b[ell]=total
    alpha = [x / c for x in mul(b, tau, J)]
    fmt = lambda x: mp.nstr(x, digits)
    return {"alphabet": k, "order": J, "digits": digits,
            "guard_digits": guard_digits, "working_digits": working_digits,
            "method": "formal saddle, strict renewal and logarithmic transfer; no fitting; numerical coefficients are not interval-certified; requested digits require stability replay",
            "v": fmt(v), "rho": fmt(rho), "p": [fmt(x) for x in coeff], "b": [fmt(x) for x in b],
            "tau": [fmt(x) for x in tau], "alpha": [fmt(x) for x in alpha],
            "small_boundary_source": [fmt(x) for x in source]}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=2)
    parser.add_argument("--order", type=int, default=5)
    parser.add_argument("--digits", type=int, default=60)
    parser.add_argument("--guard-digits", type=int, default=35)
    parser.add_argument("--output")
    args = parser.parse_args()
    result = generate(args.k, args.order, args.digits, args.guard_digits)
    text = json.dumps(result, indent=2)
    print(text)
    if args.output:
        from pathlib import Path
        Path(args.output).write_text(text + "\n")
