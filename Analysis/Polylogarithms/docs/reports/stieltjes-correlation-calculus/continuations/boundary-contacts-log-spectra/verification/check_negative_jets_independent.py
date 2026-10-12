"""Independent diagnostics for even-weight and negative-point spectral jets.

Three calculations are compared:
  (1) the ordinary remainder sum, by a finite head and a convergent
      Hurwitz-derivative tail;
  (2) the branch-cut density integral, with stable formulas at infinity;
  (3) the original spectral derivative at -1, using independently generated
      binomial Taylor coefficients about s=-1.

The analytic power-tail bound is evaluated numerically. The quadratures
and floating-point residuals are diagnostics, not interval certificates.
"""

import argparse
import json
from functools import lru_cache
from pathlib import Path

import mpmath as mp


def multiply(left, right, order):
    return [mp.fsum(left[j] * right[k-j]
                    for j in range(max(0, k-len(right)+1), min(k+1, len(left))))
            for k in range(order+1)]


def run_case(r, a_text, mass_texts, cutoff=32, order=32):
    a = mp.mpf(a_text)
    masses = list(map(mp.mpf, mass_texts))
    N = len(masses)
    m = 1
    # Here P(z)=prod(z+mu), so its zero-point weighted jet is E^{(r)}(-1).
    P = [mp.mpf(1)]
    for mu in masses:
        old = P
        P = [mp.mpf(0)] * (len(old)+1)
        for d, value in enumerate(old):
            P[d] += mu*value
            P[d+1] += value
    D = len(P)-1
    coefficient_order = order+D
    L = [mp.mpf(0)] + [(-1)**(k+1)*mp.fsum(mu**k for mu in masses)/k
                       for k in range(1, coefficient_order+1)]
    powers = [[mp.mpf(1)] + [mp.mpf(0)]*coefficient_order]
    for j in range(1, r+1):
        powers.append(multiply(powers[-1], L, coefficient_order))

    @lru_cache(None)
    def hz(point, derivative, tail):
        shift = a+cutoff if tail else a
        return mp.zeta(mp.mpf(point), shift, derivative=derivative)

    def poly(z):
        return mp.fsum(p*z**d for d, p in enumerate(P))

    def subtractor(z, log_z):
        return mp.fsum(
            p*mp.binomial(r,j)*N**(r-j)*powers[j][k]
            *z**(d-k)*log_z**(r-j)
            for d,p in enumerate(P)
            for k in range(d+1)
            for j in range(r+1))

    def F_at_x(x):
        z = x*x
        log_z = 2*mp.log(x)
        increment = mp.fsum(mp.log1p(mu/z) for mu in masses)
        # Cancel the whole j=0 logarithmic term symbolically.
        value = poly(z)*mp.fsum(mp.binomial(r,j)*(N*log_z)**(r-j)
                                *increment**j for j in range(1,r+1))
        value -= mp.fsum(
            p*mp.binomial(r,j)*N**(r-j)*powers[j][k]
            *z**(d-k)*log_z**(r-j)
            for d,p in enumerate(P)
            for k in range(1,d+1)
            for j in range(1,r+1))
        return value

    ordinary_sum = mp.fsum(F_at_x(n+a) for n in range(cutoff))
    for h in range(1,order+1):
        for j in range(1,r+1):
            coefficient = mp.fsum(p*powers[j][h+d] for d,p in enumerate(P))
            ordinary_sum += (mp.binomial(r,j)*(2*N)**(r-j)
                             *coefficient*(-1)**(r-j)*hz(2*h,r-j,True))

    baseline = mp.fsum(
        p*(-1)**j*mp.binomial(r,j)*(2*N)**(r-j)*powers[j][k]
        *hz(-2*(d-k),r-j,False)
        for d,p in enumerate(P)
        for k in range(d+1)
        for j in range(r+1))

    if N == 1 and r == 3:
        mu = masses[0]
        explicit_baseline = (8*hz(-2,3,False)+8*mu*hz(0,3,False)
                             -12*mu*hz(0,2,False))
    elif N == 2 and r == 2:
        sigma1, sigma2 = sum(masses), mp.fprod(masses)
        square_sum = sum(mu*mu for mu in masses)
        explicit_baseline = (
            16*(hz(-4,2,False)+sigma1*hz(-2,2,False)+sigma2*hz(0,2,False))
            -8*sigma1*hz(-2,1,False)
            -8*(square_sum/2+2*sigma2)*hz(0,1,False)
            +sigma1*sigma1*hz(0,0,False))
    else:
        raise ValueError('This independent verifier intentionally covers the two specified targets.')

    # Independent spectral continuation: generate c_k(s) from the binomial
    # recurrence directly at s=-1, without using the L(u)^j coefficients.
    cjets = [[mp.mpf(0)]*(r+1) for _ in range(coefficient_order+1)]
    cjets[0][0] = 1
    for mu in masses:
        local = [[mp.mpf(0)]*(r+1) for _ in range(coefficient_order+1)]
        local[0][0] = 1
        for k in range(1,coefficient_order+1):
            for j in range(r+1):
                local[k][j] = -mu/k*((k-1-m)*local[k-1][j]
                                     +(local[k-1][j-1] if j else 0))
        combined = [[mp.mpf(0)]*(r+1) for _ in range(coefficient_order+1)]
        for k in range(coefficient_order+1):
            for j in range(r+1):
                combined[k][j] = mp.fsum(
                    cjets[h][ell]*local[k-h][j-ell]
                    for h in range(k+1) for ell in range(j+1))
        cjets = combined
    original_jet = mp.fsum(
        mp.fprod((n+a)**2+mu for mu in masses)**m
        *(-mp.fsum(mp.log((n+a)**2+mu) for mu in masses))**r
        for n in range(cutoff))
    original_jet += mp.factorial(r)*mp.fsum(
        cjets[k][j]*(2*N)**(r-j)/mp.factorial(r-j)
        *hz(2*k-2*N*m,r-j,True)
        for k in range(coefficient_order+1) for j in range(r+1))

    def Q(t):
        if not t:
            return mp.polygamma(1,a)
        root = mp.sqrt(t)
        return mp.im(mp.digamma(a+1j*root))/root

    def cut_density(t):
        log_z = mp.log(t)+1j*mp.pi
        if t in masses:
            # P has a root here and P(z)*Log(z+mu)^r tends to zero.
            first = mp.mpc(0)
        else:
            cut_log = (mp.fsum(mp.log(abs(mu-t)) for mu in masses)
                       +1j*mp.pi*sum(mu<t for mu in masses))
            first = poly(-t)*cut_log**r
        return -mp.im(first-subtractor(-t,log_z))/mp.pi

    def stable_tail_density(t):
        if N == 1 and r == 3:
            mu = masses[0]
            q = mu/t
            delta = mp.log1p(-q)
            g = q*mp.hyp2f1(1,1,3,q)/2
            return 6*mu*mp.log(t)*g+3*t*(1-q)*delta*delta
        # For r=2 only the j=1 term has an imaginary part on the far cut.
        # Remove the first d Taylor terms of each log before multiplying
        # by t^d, then use an exact hypergeometric remainder.
        return 2*N/t*mp.fsum(
            p*(-1)**d*mu**(d+1)/(d+1)*mp.hyp2f1(1,d+1,d+2,mu/t)
            for d,p in enumerate(P) for mu in masses)

    T = 2*max(masses)
    integral = mp.mpf(0)
    endpoints = sorted(set([mp.mpf(0)]+masses+[T]))
    for left,right in zip(endpoints,endpoints[1:]):
        middle = (left+right)/2
        integral += mp.quad(lambda t: cut_density(t)*Q(t), [left,middle,right])
    lower = mp.sqrt(T)
    integral += mp.quad(lambda y: 2*y*stable_tail_density(y*y)*Q(y*y),
                        [lower,lower+1,2*lower+2,mp.inf])
    tail_formula_residuals = [abs(cut_density(t)-stable_tail_density(t))
                              for t in [T,2*T,10*T]]

    radius = 1/(2*max(masses))
    majorant = mp.fsum(-mp.log1p(-mu*radius) for mu in masses)
    polynomial_majorant = mp.fsum(abs(p)*radius**(-d) for d,p in enumerate(P))
    omitted_tail_bound = (polynomial_majorant*radius**(-order-1)
                         /(1-1/(radius*(cutoff+a)**2))
                         *mp.fsum(mp.binomial(r,j)*(2*N)**(r-j)*majorant**j
                                   *(-1)**(r-j)*hz(2*order+2,r-j,True)
                                   for j in range(1,r+1)))

    integral_jet = baseline+(-1)**r*integral
    sum_jet = baseline+(-1)**r*ordinary_sum
    result = dict(
        N=N,negative_point=-m,derivative_order=r,a=str(a),masses=list(map(str,masses)),
        polynomial_coefficients_ascending=list(map(str,P)),
        finite_head=cutoff,remainder_power_terms=order,
        binomial_coefficient_terms=coefficient_order+1,
        ordinary_remainder_sum=mp.nstr(ordinary_sum,55),
        density_integral=mp.nstr(integral,55),
        sum_integral_residual=mp.nstr(abs(ordinary_sum-integral),8),
        analytic_power_tail_bound_evaluated_numerically=mp.nstr(omitted_tail_bound,8),
        baseline=mp.nstr(baseline,55),
        explicit_baseline_residual=mp.nstr(abs(baseline-explicit_baseline),8),
        density_tail_formula_max_residual=mp.nstr(max(tail_formula_residuals),8),
        spectral_jet_from_integral=mp.nstr(integral_jet,55),
        spectral_jet_from_original_binomial_continuation=mp.nstr(original_jet,55),
        original_vs_integral_residual=mp.nstr(abs(original_jet-integral_jet),8),
        original_vs_remainder_sum_residual=mp.nstr(abs(original_jet-sum_jet),8))
    assert abs(ordinary_sum-integral) < mp.mpf('1e-42')
    assert abs(original_jet-integral_jet) < mp.mpf('1e-40')
    assert abs(baseline-explicit_baseline) < mp.mpf('1e-45')
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--digits',type=int,default=60)
    parser.add_argument('--output',default=str(Path(__file__).resolve().parents[1] / 'data' / 'negative_jets_independent_checks.json'))
    args = parser.parse_args()
    mp.mp.dps = args.digits
    results = dict(
        working_digits=mp.mp.dps,
        status='Independent numerical diagnostics; no interval certification is claimed.',
        methods=['Finite head plus convergent Hurwitz-derivative remainder tail',
                 'Piecewise cut quadrature with stable exact tails',
                 'Independent binomial Taylor continuation directly at the negative spectral point'],
        cases=[])
    for spec in [(3,'0.7',['0.8']), (2,'0.7',['0.8','1.4'])]:
        case = run_case(*spec)
        results['cases'].append(case)
        Path(args.output).write_text(json.dumps(results,indent=2)+'\n',encoding='utf-8')
        print(json.dumps(case,indent=2),flush=True)
