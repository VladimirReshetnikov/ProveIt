#!/usr/bin/env python3
"""Independent quadrature checks for Barnes moments and monomial contacts."""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 90

def da_D(a, b):
    d = b-a
    if not d:
        return -1/(2*a*a)
    return (mp.log1p(d/a)-d/a)/(d*d)

def remainder(a, b):
    """I - d_a D - psi(1+b)/a - zeta(2)log(b/a), stably."""
    z2 = mp.zeta(2)
    def mixed(x):
        return ((mp.polygamma(1, 1+x+b)-z2)/(x+a)
                -(mp.polygamma(1, 1+x+a)-z2)/(x+b))
    def regular(x):
        return mp.polygamma(1, 1+x+a)*mp.digamma(1+x+b)
    knots = sorted(set([mp.mpf(0), a, b, mp.mpf(1)]))
    return (-da_D(1+a, 1+b)-mp.digamma(2+b)/(1+a)
            +z2*mp.log((1+a)/(1+b))
            +mp.quad(mixed, knots)+mp.quad(regular, [0, 1]))

def predicted(q, lam, mu, qi=None, j=None):
    v = mp.zeta(2)*mp.log(mu/lam)
    if qi is not None:
        v += (-1)**(qi+1)*mp.zeta(qi+1)*mu**qi/lam
    if j is not None:
        v += lam**j/mu**(j+2)*((j+1)*mp.log(mu/lam)-1)
    return v

def ct_approximant(eps, q, lam, mu, rem=None):
    a, b = lam*eps**q, mu*eps
    L = mp.log(b/a)
    v = da_D(a, b)+mp.digamma(1+b)/a+mp.zeta(2)*L
    # Remove all strictly divergent monomials and all zero-power log terms.
    # q is 90-digit mp data, so exact resonances are detected to 70 digits.
    v += 1/(a*b)
    j = 0
    while j*(q-1)-2 <= mp.mpf('1e-70'):
        exponent = j*(q-1)-2
        coeff = a**j/b**(j+2)
        if exponent < -mp.mpf('1e-70'):
            v -= coeff*((j+1)*L-1)
        else:
            v -= coeff*(j+1)*(1-q)*mp.log(eps)
        j += 1
    v += mp.euler/a
    k = 1
    while k-q < -mp.mpf('1e-70'):
        v -= (-1)**(k+1)*mp.zeta(k+1)*b**k/a
        k += 1
    v -= mp.zeta(2)*(1-q)*mp.log(eps)
    return v+(remainder(a, b) if rem is None else rem)

def s(x):
    return mp.nstr(x, 45)

def main():
    records = []
    cases = [
        ('q2_equal', mp.mpf(2), mp.mpf(1), mp.mpf(1), 2, 2),
        ('q3_equal', mp.mpf(3), mp.mpf(1), mp.mpf(1), 3, 1),
        ('q4_equal', mp.mpf(4), mp.mpf(1), mp.mpf(1), 4, None),
        ('q_5over3_equal', mp.mpf(5)/3, mp.mpf(1), mp.mpf(1), None, 3),
        ('q_sqrt2_unequal', mp.sqrt(2), mp.mpf('1.3'), mp.mpf('.7'), None, None),
        ('q2_unequal', mp.mpf(2), mp.mpf('1.3'), mp.mpf('.7'), 2, 2),
    ]
    for name, q, lam, mu, qi, j in cases:
        expected = predicted(q, lam, mu, qi, j)
        rows = []
        for digits in (3, 6, 9):
            eps = mp.mpf(10)**(-digits)
            rem = remainder(lam*eps**q, mu*eps)
            observed = ct_approximant(eps, q, lam, mu, rem)
            rows.append({'eps': s(eps), 'analytic_remainder': s(rem),
                         'ct_approximant': s(observed),
                         'ct_error': s(observed-expected)})
        record = {'case': name, 'expected_ct': s(expected), 'rows': rows}
        if name == 'q_sqrt2_unequal':
            for row in rows:
                eps = mp.mpf(row['eps'])
                a, b = lam*eps**q, mu*eps
                correction = sum(a**j/b**(j+2)*((j+1)*mp.log(b/a)-1)
                                 for j in (5, 6))
                accelerated = mp.mpf(row['ct_approximant'])-correction
                row['accelerated_ct_approximant'] = s(accelerated)
                row['accelerated_ct_error'] = s(accelerated-expected)
            record['acceleration_note'] = (
                'The first two positive-power rational-kernel terms j=5,6 are '
                'subtracted; both tend to zero. The leading unaccelerated '
                'exponent is 5*sqrt(2)-7 = 0.071067811865..., so raw diagnostics '
                'are not yet in the decreasing-to-zero regime at all displayed scales.')
        records.append(record)
    def density(x):
        return mp.pi/2/mp.cosh(mp.pi*x)**2
    def U(x):
        return mp.digamma(mp.mpf('.5')+1j*x)+mp.euler+1
    barnes = []
    for name, f, target in [
        ('centered_mean_real', lambda x: U(x).real, mp.mpf(0)),
        ('centered_absolute_square', lambda x: abs(U(x))**2, mp.mpf(1)),
        ('centered_square_real', lambda x: (U(x)**2).real, 1-mp.zeta(2)),
        ('centered_mixed_cubic_real', lambda x: (U(x)*abs(U(x))**2).real,
         2*mp.zeta(3)-2),
        ('centered_absolute_fourth', lambda x: abs(U(x))**4,
         9-2*mp.zeta(2)-mp.mpf('3.5')*mp.zeta(4)),
        ('trigamma_absolute_square',
         lambda x: abs(mp.polygamma(1, mp.mpf('.5')+1j*x))**2,
         16*mp.zeta(4)),
    ]:
        result = 2*mp.quad(lambda x: density(x)*f(x), [0, 1, 4, mp.inf])
        barnes.append({'identity': name, 'quadrature': s(result),
                       'expected': s(target), 'error': s(result-target)})
    out = {'precision_digits': mp.mp.dps,
           'method': 'Ordinary mpmath quadrature after exact singular subtraction; floating-point diagnostics, not interval certificates.',
           'collision_checks': records, 'barnes_checks': barnes}
    path = Path(__file__).with_suffix('.json')
    path.write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps(out, indent=2))

if __name__ == '__main__':
    main()
