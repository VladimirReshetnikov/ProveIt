#!/usr/bin/env python3
"""Floating-point illustrations only; the proof in paper.tex uses no numerics.
Dependencies: Python 3, scipy, mpmath.  No network or repository checkout needed.
"""
import math
import mpmath as mp
from scipy.integrate import quad

mp.mp.dps = 35


def kz(t):
    t = abs(t)
    if t > 4:
        return 0.0
    a = math.pi * math.exp(2*t)
    return math.exp(t/2) * sum((4*(a*n*n)**2-6*a*n*n)*math.exp(-a*n*n)
                               for n in range(1, 13))


def kb(t):
    t = abs(t)
    if t > 4:
        return 0.0
    a = math.pi * math.exp(2*t)/4
    return 2*math.exp(1.5*t)*sum((-1)**j*(2*j+1)*math.exp(-a*(2*j+1)**2)
                                 for j in range(12))


def transform(k, z):
    return 2*quad(lambda t: k(t)*math.cos(z*t), 0, 4,
                  epsabs=3e-13, epsrel=3e-13, limit=300)[0]


def xi(s):
    return s*(s-1)*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)/2


def beta(s):
    return mp.dirichlet(s, [0, 1, 0, -1])


def completed_beta(s):
    return (4/mp.pi)**((s+1)/2)*mp.gamma((s+1)/2)*beta(s)


def test_dirichlet():
    print('Theta integral / completed function checks (absolute errors)')
    for z in (0.0, 1.0, 4.0, 10.0, 20.0):
        s = mp.mpf('0.5') + 1j*z
        e1 = abs(transform(kz, z) - xi(s))
        e2 = abs(transform(kb, z) - completed_beta(s))
        print(f'z={z:5.1f}: xi {float(e1):.3e}, beta {float(e2):.3e}')
        assert e1 < 2e-11 and e2 < 2e-11
    mz, mb = transform(kz, 0), transform(kb, 0)
    # For these two functions the individual kernels are already positive.
    # The normalized convolution transform is their product.
    print('\nNormalized product transform at selected ordinates')
    ordinates = [('zeta', float(mp.zetazero(n).imag)) for n in (1, 2, 3)]
    for guess in (6.02, 10.24):
        # Use the real-valued completed beta along its central line.
        root = mp.findroot(lambda x: mp.re(completed_beta(mp.mpf('0.5')+1j*x)),
                           (mp.mpf(str(guess-.01)), mp.mpf(str(guess+.01))))
        assert abs(beta(mp.mpf('0.5')+1j*root)) < mp.mpf('1e-25')
        ordinates.append(('beta', float(root)))
    for family, z in ordinates:
        a, b = transform(kz, z)/mz, transform(kb, z)/mb
        print(f'{family:5s} {z:18.12f}: |product|={abs(a*b):.3e}, '
              f'|xi|={abs(a):.3e}, |beta|={abs(b):.3e}')
        assert abs(a*b) < 2e-11
    print(f'Normalization masses: xi={mz:.12f}, beta={mb:.12f}')


def test_signed_smoothing():
    # Even signed test density. Its bilateral Laplace transform is strictly
    # positive: choose b = (integral t^2 rho)/(2 integral rho).
    # With u real, cosh(ut) is increasing in t^2; positive covariance shows
    # E[t^2 cosh(ut)] >= E[t^2] E[cosh(ut)].  Therefore H(u)>0.
    # The exact rho is exp(-cosh(t)) everywhere; the floating-point
    # quadrature truncates at |t|=10 to avoid unnecessary underflow.
    def rho(t):
        return math.exp(-math.cosh(t)) if abs(t) < 10 else 0.0
    m0 = 2*quad(rho, 0, 10, epsabs=1e-12)[0]
    m2 = 2*quad(lambda t: t*t*rho(t), 0, 10, epsabs=1e-12)[0]
    b = m2/(2*m0)
    def h(t):
        return (t*t-b)*rho(t)
    A = 1.0
    assert b < A*A
    N = -2*quad(h, 0, math.sqrt(b))[0]
    P = quad(h, A+1, A+2)[0]
    D = max(1.0, math.log(N/P)+1)
    B = 8.0
    sigma = 3.0
    # Constants in the proof, with B,sigma chosen for this numerical illustration.
    R = D*sigma*sigma+A+2+B
    print('\nSigned-kernel compact smoothing illustration')
    print(f'b={b:.9f}, h(0)={h(0):.9f}, H(0)={m2/2:.9f}')
    print(f'A={A:g}, N={N:.9f}, P={P:.9f}, D={D:.6f}, sigma={sigma:g}, R={R:.6f}')
    assert math.exp(D)*P > N
    # Check the middle-region tilted integral on a finite grid.
    vals = [quad(lambda t: h(t)*math.exp(u*t-t*t/(2*sigma*sigma)),
                 -B, B, epsabs=1e-9, epsrel=1e-10)[0]
            for u in [(D+1)*i/100 for i in range(101)]]
    print(f'Minimum sampled tilted integral: {min(vals):.9f}')
    assert min(vals)>0
    # Factor out exp(-x^2/(2 sigma^2)) to avoid underflow in the middle.
    for x in (0, 1, 3, D*sigma*sigma, D*sigma*sigma+A+2):
        val = quad(lambda t: h(t)*math.exp(x*t/sigma**2-t*t/(2*sigma*sigma)),
                   -B, B, epsabs=1e-9, epsrel=1e-10)[0]
        assert val > 0
        print(f'x={x:8.3f}: scaled middle contribution {val:.9e}')
    print('Finite numerical checks passed; the lemma proves existence of parameters, not certification of this grid-selected pair.')


if __name__ == '__main__':
    test_dirichlet()
    test_signed_smoothing()
