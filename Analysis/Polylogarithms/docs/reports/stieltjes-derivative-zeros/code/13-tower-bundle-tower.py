"""Stieltjes/Lerch parameter-derivative tower.

Exact routines use fractions.Fraction. Numerical routines use mpmath and are
cross-checks, not interval arithmetic. See the accompanying article for proofs.
"""
from __future__ import annotations
from fractions import Fraction as F
from math import gcd
import mpmath as mp


def prime_divisors(n: int) -> list[int]:
    if n < 1:
        raise ValueError('n must be positive')
    out = []
    p = 2
    while p*p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        out.append(n)
    return out


def units(d: int) -> list[int]:
    return [0] if d == 1 else [a for a in range(1, d) if gcd(a, d) == 1]


def extension_matrix(q: int, s: int) -> tuple[list[int], list[list[F]]]:
    """Exact q x phi(q) extension from unit coordinates; rows indexed 0..q-1.

    Implements the prime-step inverses of the article without characters.
    Requires q >= 2 and integer s >= 1.
    """
    if q < 2 or s < 1:
        raise ValueError('require q >= 2 and s >= 1')
    uq = units(q)
    width = len(uq)
    E = {q: {a: [F(int(i == j)) for i in range(width)]
             for j, a in enumerate(uq)}}
    divisors = sorted((d for d in range(1, q+1) if q % d == 0), reverse=True)
    for d in divisors[1:]:
        p = prime_divisors(q//d)[0]
        g = p*d
        S = {a: [sum((E[g][b][j] for b in units(g) if b % d == a % d), F(0))
                 for j in range(width)] for a in units(d)}
        if d % p == 0:
            E[d] = {a: [v/F(p**s) for v in row] for a, row in S.items()}
        else:
            E[d] = {}
            for a in units(d):
                orbit = [a]
                invp = pow(p, -1, d) if d > 1 else 0
                b = (a*invp) % d if d > 1 else 0
                while b != a:
                    orbit.append(b)
                    b = b*invp % d
                ell = len(orbit)
                den = p**(s*ell)-1
                E[d][a] = [sum((F(p**(s*(ell-1-j)), den)*S[b][i]
                                    for j, b in enumerate(orbit)), F(0))
                            for i in range(width)]
    out = []
    for a in range(q):
        g = gcd(a, q)
        d = q//g
        b = a//g if d > 1 else 0
        out.append(E[d][b])
    return uq, out


def distribution_rows(q: int, s: int) -> list[list[int]]:
    rows = []
    for p in prime_divisors(q):
        for b in range(q//p):
            row = [0]*q
            for j in range(p):
                row[b+j*(q//p)] += 1
            row[(p*b) % q] -= p**s
            rows.append(row)
    return rows


def harmonic_coefficients(k: int, n: int):
    if k < 1 or n < 0:
        raise ValueError('require k >= 1 and n >= 0')
    e = [mp.mpf(1)] + [mp.mpf(0)]*n
    for j in range(1, k+1):
        for i in range(min(j, n), 0, -1):
            e[i] += e[i-1]/j
    return e


def appell_coefficients(N: int):
    """Ascending coefficients of Q_0,...,Q_N, at current mp.dps."""
    if N < 0:
        raise ValueError('N must be nonnegative')
    b = [mp.mpf(1)]
    ell = [mp.mpf(0), mp.euler] + [(-1)**(j+1)*mp.zeta(j) for j in range(2, N+1)]
    for n in range(1, N+1):
        b.append(sum(ell[j]*b[n-j] for j in range(1, n+1))/n)
    return [[mp.factorial(n)/mp.factorial(j)*b[n-j] for j in range(n+1)]
            for n in range(N+1)]


def appell(n: int, x):
    return mp.polyval(appell_coefficients(n)[n][::-1], x)


def normalized_stieltjes(n: int, k: int, a):
    """(-1)^(n+k) a^(k+1) gamma_n^(k)(a)/k!, using Hurwitz jets."""
    a = mp.mpf(a)
    if a <= 0:
        raise ValueError('a must be positive')
    # The unscaled Hurwitz jets can be extremely small.  Supply enough
    # guard digits before multiplying by a**(k+1), rather than trusting
    # an absolute-small-value cutoff at the caller's precision.
    guard = max(0, int(mp.ceil((k+1)*max(mp.mpf(0), mp.log10(a)))))+10
    with mp.extradps(guard):
        e = harmonic_coefficients(k, n)
        value = a**(k+1)*mp.factorial(n)*sum(
            e[i]*mp.zeta(k+1, a, derivative=n-i)/mp.factorial(n-i)
            for i in range(n+1))
    return +value


def stieltjes_derivative(n: int, k: int, a):
    a = mp.mpf(a)
    return (-1)**(n+k)*mp.factorial(k)*normalized_stieltjes(n, k, a)/a**(k+1)


def normalized_integral(n: int, k: int, a, rho=1):
    """Independent Mellin/Laplace quadrature, for cross-checks at modest k."""
    a, rho = mp.mpf(a), mp.mpf(rho)
    if a <= 0 or not 0 <= rho <= 1 or k < 1:
        raise ValueError('require a > 0, 0 <= rho <= 1, k >= 1')
    Q = appell_coefficients(n)[n][::-1]
    def integrand(x):
        if x == 0:
            return mp.mpf(0)
        den = -mp.expm1(-x) if rho == 1 else 1-rho*mp.exp(-x)
        return mp.exp(k*mp.log(x)-a*x)*mp.polyval(Q, mp.log(x))/den
    return a**(k+1)/mp.factorial(k)*mp.quad(integrand, [0, 1, mp.inf])


def normalized_concentration(n: int, k: int, a, rho=1):
    """Independent scale-first gamma-expectation quadrature, avoiding tiny jets."""
    a, rho = mp.mpf(a), mp.mpf(rho)
    if a <= 0 or k < 1 or n < 0 or not 0 <= rho <= 1:
        raise ValueError('invalid concentration parameters')
    c = a/k
    Q = appell_coefficients(n)[n][::-1]
    lognorm = (k+1)*mp.log(k)-mp.loggamma(k+1)
    def integrand(y):
        if y == 0:
            return mp.mpf(0)
        x = y/c
        den = -mp.expm1(-x) if rho == 1 else 1-rho*mp.exp(-x)
        return mp.exp(lognorm+k*mp.log(y)-k*y)*mp.polyval(Q, mp.log(x))/den
    return mp.quad(integrand, [0, mp.mpf('.5'), mp.mpf('.8'), 1,
                              mp.mpf('1.2'), mp.mpf('1.5'), 3, mp.inf])


def finite_sum(n: int, k: int, a, M: int, rho=1):
    """Unnormalized derivative approximant; article gives an analytic tail bound."""
    a, rho = mp.mpf(a), mp.mpf(rho)
    if a <= 0 or M < 1 or not 0 <= rho <= 1:
        raise ValueError('require a > 0, M >= 1, 0 <= rho <= 1')
    e = harmonic_coefficients(k, n)
    def B(x):
        return mp.factorial(n)*sum(e[i]*(-x)**(n-i)/mp.factorial(n-i)
                                   for i in range(n+1))
    return (-1)**(n+k)*mp.factorial(k)*mp.fsum(
        rho**m*B(mp.log(a+m))/(a+m)**(k+1) for m in range(M))


def tail_bound(n: int, k: int, a, M: int, radius, rho=1):
    """Mathematical absolute-error bound, numerically evaluated (not rounded out)."""
    a, rho, R = mp.mpf(a), mp.mpf(rho), mp.mpf(radius)
    B = a+M
    if not (k >= 1 and n >= 0 and M >= 1 and B >= 1 and 0 < R < k and 0 <= rho <= 1):
        raise ValueError('invalid tail-bound parameters')
    P = mp.fprod(1+R/j for j in range(1, k+1))
    factor = 1+B/(k-R)
    if rho < 1:
        factor = min(factor, 1/(1-rho))
    return mp.factorial(k)*mp.factorial(n)*P*R**(-n)*rho**M*B**(-k-1+R)*factor


def zero_slopes(n: int, rho=1):
    """Return (x, c, d) with a_zero = k*c+d+O(1/k), increasing c."""
    if n < 1:
        raise ValueError('n must be positive')
    rho = mp.mpf(rho)
    Q = appell_coefficients(n)
    xx = sorted(mp.polyroots(Q[n][::-1], maxsteps=1000), reverse=True)
    result = []
    for x in xx:
        c = mp.exp(-x)
        qp = n*mp.polyval(Q[n-1][::-1], x)
        qpp = n*(n-1)*mp.polyval(Q[n-2][::-1], x) if n > 1 else 0
        d = c/2*(1+qpp/qp)-rho/(mp.exp(1/c)-rho)
        result.append((x, c, d))
    return result


def zero_next_coefficient(n: int, x, c, d, rho=1):
    """Coefficient b_1 in a_zero = k*c+d+b_1/k+O(k^-2)."""
    rho = mp.mpf(rho)
    Q = appell_coefficients(n)[n][::-1]
    def h(z):
        den = -mp.expm1(-z) if rho == 1 else 1-rho*mp.exp(-z)
        return mp.polyval(Q, mp.log(z))/den
    z = 1/c
    h1, h2, h3, h4 = (mp.diff(h, z, j) for j in range(1,5))
    g0p = -z*z*h1
    g0pp = 2*z**3*h1+z**4*h2
    g1p = -z*z*(h1+2*z*h2+z*z*h3/2)
    g2 = z*z*h2+mp.mpf(5)/6*z**3*h3+z**4*h4/8
    return -(g0pp*d*d/2+g1p*d+g2)/g0p


def lseries(s, character):
    q = len(character)
    return mp.fsum(character[a]*mp.zeta(s, mp.mpf(a)/q)
                    for a in range(1, q) if character[a])/q**s


def log_coefficients(a, N: int):
    """Coefficients of log(A(t)/A(0)) through degree N (formal arithmetic)."""
    if a[0] == 0:
        raise ValueError('nonzero constant term is required')
    b = [v/a[0] for v in a]
    ell = [mp.mpf(0)]*(N+1)
    for n in range(1, N+1):
        ell[n] = b[n] - sum(j*ell[j]*b[n-j] for j in range(1, n))/n
    return ell


def bridge_cumulant(r: int, k: int, q: int, delta: int):
    if r == 1:
        return mp.euler+mp.log(2*mp.pi/q)-mp.harmonic(k)
    H = mp.fsum(mp.mpf(j)**(-r) for j in range(1, k+1))
    if r % 2:
        return mp.factorial(r-1)*(mp.zeta(r)-H)
    return mp.factorial(r-1)*(H+(-1)**delta*(1-mp.mpf(2)**(1-r))*mp.zeta(r))
