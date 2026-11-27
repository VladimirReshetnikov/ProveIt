#!/usr/bin/env python3
"""Numerical checks of the real-character transfer and conductor-shift law.

Uses finite prime sums, elementary functions, and Hurwitz zeta evaluations.
This is a high-precision consistency check, not an interval certificate.
"""
from pathlib import Path
import json
import mpmath as mp
from verify_resonance import kernel, K0, D, prime_power, max_abs, decimal

mp.mp.dps = 90
CHARACTERS = {
    'chi_minus4': [0, 1, 0, -1],
    'chi_8': [0, 1, 0, -1, 0, -1, 0, 1],
    'chi_minus8': [0, 1, 0, 1, 0, -1, 0, -1],
}

def dirichlet_value(s, values):
    q = len(values)
    return mp.fsum(values[a % q] * mp.zeta(s, mp.mpf(a)/q)
                   for a in range(1, q+1) if values[a % q]) / mp.power(q, s)

def kappa_value(values):
    q = len(values)
    parity = 0 if values[-1] == 1 else 1
    # At s=1 the common Hurwitz pole cancels. The constant term is -digamma.
    L1 = -mp.fsum(values[a % q] * mp.digamma(mp.mpf(a)/q)
                  for a in range(1, q+1) if values[a % q]) / q
    delta = mp.mpf('1e-18')
    derivative = (dirichlet_value(1+delta, values)
                  - dirichlet_value(1-delta, values))/(2*delta)
    derivative2 = (dirichlet_value(1+delta/2, values)
                   - dirichlet_value(1-delta/2, values))/delta
    # Richardson removes the O(delta^2) term; retained precision is ample
    # for every covariance difference used below.
    derivative = (4*derivative2-derivative)/3
    return (mp.log(mp.mpf(q)/mp.pi) + mp.digamma(mp.mpf(1+parity)/2)
            + 2*derivative/L1), L1, derivative

def character_kernel(t, values, kappa):
    t = abs(mp.mpf(t))
    if t == 0:
        return kappa
    q = len(values)
    parity = 0 if values[-1] == 1 else 1
    sh, ch = mp.sinh(t/2), mp.cosh(t/2)
    # Closed form of the parity-dependent convolution in Lemma 3.3.
    convolution = (2-parity)*t*sh + 2*parity*ch*mp.log(ch)
    prime_difference = mp.mpf(0)
    for n in range(2, int(mp.floor(mp.exp(t)))+1):
        pk = prime_power(n)
        if pk:
            p, _ = pk
            prime_difference += (2*mp.log(p)*(1-values[n % q])/mp.sqrt(n)
                                 * mp.sinh((t-mp.log(n))/2))
    return (kernel(t)+(kappa-K0)*ch-mp.log(q)*sh
            +convolution-prime_difference)

def matrix_data(values, kappa, epsilon, n=8):
    q = len(values)
    h = q*epsilon
    ell = mp.log(1/epsilon)+D
    K = lambda t: character_kernel(t, values, kappa)
    V = 2*(kappa-K(h))
    assert abs(V/h-ell) < 100*h
    A, R = mp.matrix(n), mp.eye(n)
    for i in range(1,n+1):
        for j in range(i+1,n+1):
            lag = mp.log(mp.mpf(j)/i)
            R[i-1,j-1] = R[j-1,i-1] = (2*K(lag)-K(lag+h)-K(lag-h))/V
            pk = prime_power(j//i) if j % i == 0 else None
            if pk:
                p, k = pk
                A[i-1,j-1] = A[j-1,i-1] = values[p % q]**k*mp.log(p)/mp.sqrt(p**k)
    mp.cholesky(R)
    error = max_abs(ell*(mp.eye(n)-R)-A)
    assert error < 1000*h
    return {
        'epsilon': decimal(epsilon), 'h': decimal(h), 'ell': decimal(ell),
        'matrix_error': decimal(error), 'logdet': decimal(mp.log(mp.det(R))),
        'variance_error_divided_by_h_squared': decimal((V-h*ell)/h**2),
    }

def main():
    constants, rows = {}, {}
    for name, values in CHARACTERS.items():
        kappa, L1, derivative = kappa_value(values)
        assert kappa > 0
        constants[name] = {'conductor': len(values), 'values': values,
                          'kappa': decimal(kappa), 'L_at_1': decimal(L1),
                          'L_prime_at_1': decimal(derivative)}
        rows[name] = [matrix_data(values, kappa, mp.mpf(e))
                      for e in ['1e-4','1e-6','1e-9']]
    comparison=[]
    for k in range(3):
        epsilon=mp.mpf(rows['chi_8'][k]['epsilon'])
        ell=mp.mpf(rows['chi_8'][k]['ell'])
        values={name:mp.mpf(r[k]['logdet']) for name,r in rows.items()}
        spread=max(values.values())-min(values.values())
        assert spread < 10000*epsilon/ell
        comparison.append({'epsilon':decimal(epsilon),
                           'max_logdet_minus_min_logdet':decimal(spread),
                           'spread_times_ell_over_epsilon':decimal(spread*ell/epsilon)})
    out={'status':'all finite real-character checks passed',
         'precision_decimal_digits':mp.mp.dps,
         'scope':'Numerical consistency checks, not interval certificates or proofs.',
         'constants':constants,'matrix_checks':rows,'conductor_aligned_comparisons':comparison}
    dest=Path(__file__).resolve().parents[1]/'results'/'characters.json'
    dest.write_text(json.dumps(out,indent=2)+'\n')
    print('All real-character checks passed at 90 digits; N=8.')
    for name, row in constants.items():
        print(name, 'kappa =', mp.nstr(mp.mpf(row['kappa']),18))
    for row in comparison:
        print('epsilon='+row['epsilon']+'; determinant spread='+row['max_logdet_minus_min_logdet'])

if __name__=='__main__':
    main()
