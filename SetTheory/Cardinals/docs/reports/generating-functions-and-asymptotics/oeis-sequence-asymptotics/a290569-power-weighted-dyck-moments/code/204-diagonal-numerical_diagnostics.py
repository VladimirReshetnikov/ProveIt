#!/usr/bin/env python3
"""Deterministic numerical cross-checks. No interval certification is claimed."""
import json
from fractions import Fraction
from pathlib import Path

import mpmath as mp
from coefficients import (compile_multiplicity, cutoff_majorants,
                          logarithmic_coefficients, multiplicity_coefficients,
                          normalized_walk, partition_product, require,
                          row_box_coefficients)
from inverse import inverse_profile_coefficients, lambert_scale, smooth_root


def fmt(x, digits=65):
    return mp.nstr(x, digits)


def _rational_single_part_test():
    # With only part 1, a partition is a column of M boxes and D_k=M^k/k.
    # Its geometric moments give an independent finite-multiplicity test.
    from math import factorial
    import sympy as sp
    from sympy.functions.combinatorial.numbers import stirling
    M = sp.Symbol('M')
    tests = []
    for tau, sigma, q in [(Fraction(1), Fraction(0), Fraction(1,3)),
                          (Fraction(3,2), Fraction(-2,3), Fraction(2,5))]:
        got = multiplicity_coefficients(1, 3, tau, sigma, q)
        b = [sp.Integer(1)]
        for r in range(1,4):
            b.append(sp.expand(-sum(k*(sp.Rational(tau)*(M**(k+1))/(k+1)
                +sp.Rational(sigma)*M**k/k)*b[r-k] for k in range(1,r+1))/r))
        expected = []
        y = q/(1-q)
        for br in b:
            value = Fraction(0)
            for (r,), coefficient in sp.Poly(br,M).terms():
                moment = sum(int(stirling(r,l,kind=2))*factorial(l)*y**l for l in range(r+1))
                value += Fraction(int(coefficient.p),int(coefficient.q))*moment
            expected.append(value)
        require(got == expected, 'exact single-part multiplicity test')
        tests.append({'tau':str(tau),'sigma':str(sigma),'q':str(q),
                      'coefficients':[str(x) for x in got]})
    return tests


def run(output_dir):
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    mp.mp.dps = 85
    rational_tests = _rational_single_part_test()
    rational_log = logarithmic_coefficients([Fraction(1),Fraction(1,3),Fraction(2,5)])
    require(rational_log == [Fraction(0),Fraction(1,3),Fraction(31,90)]
            and all(isinstance(x,Fraction) for x in rational_log),
            'exact rational logarithmic coefficient arithmetic')
    from exact_checks import walk_dp
    from math import factorial
    small_walk_checks = []
    for n in range(1,9):
        for tau,sigma in [('1','0'),('1','1'),('0.5','0'),('0.5','0.5')]:
            p = mp.mpf(tau)*n+mp.mpf(sigma)
            if p != int(p):
                continue
            exact = Fraction(walk_dp(n,int(p)),factorial(n)**int(p))
            numeric = normalized_walk(n,tau,sigma)
            error = numeric-mp.mpf(exact.numerator)/exact.denominator
            require(abs(error) < mp.mpf('1e-75'),'small exact normalized walk tolerance')
            small_walk_checks.append({'n':n,'tau':tau,'sigma':sigma,'p':int(p),
                                      'exact_ratio':str(exact),'difference':fmt(error)})
    # The recurrence needs no b_r or ell_r at orders zero and one.
    for order in (0,1):
        require(len(inverse_profile_coefficients(mp.mpf(3),mp.mpf(2),[],order)) == order+1,
                'empty logarithmic coefficient list endpoint')
    c = multiplicity_coefficients(J=200, order=4)
    box = row_box_coefficients(L=175, order=4)
    differences = [box[r]-c[r] for r in range(5)]
    require(max(abs(x) for x in differences) < mp.mpf('1e-60'),
            'independent coefficient engine diagnostic tolerance')
    Q = partition_product(1)
    q = mp.exp(-1)
    mu = mp.fsum((mp.mpf(j*j)-mp.mpf(j)/2)*q**j/(1-q**j) for j in range(1,1201))
    require(abs(c[1]+mu) < mp.mpf('1e-70'), 'Lambert c1 diagnostic tolerance')
    ell = logarithmic_coefficients(c)
    tv_coefficient = (mu*(1+q)-q/2)/Q
    forward, inverse, tv = [], [], []
    for n in [10,20,40,80,160]:
        ratio = normalized_walk(n)
        forward.append({'n':n, 'R':fmt(ratio), 'R_over_Q':fmt(ratio/Q),
                        'scaled_remainders':[fmt((ratio/Q-mp.fsum(
                            c[r]/n**r for r in range(K+1)))*n**(K+1)) for K in range(5)]})
        logY = n*mp.loggamma(n+1)+mp.log(ratio)
        t = lambert_scale(logY)
        alpha = inverse_profile_coefficients(mp.log(t),Q,ell,2)
        H = 2*mp.log(t)-1
        A = (mp.log(t)+mp.log(2*mp.pi))/2
        d = mp.mpf(1)/12+mp.log(Q)
        displayed = [-A/H]
        displayed.append(-((H+2)*displayed[0]**2/2+(A+mp.mpf('.5'))*displayed[0]+d)/H)
        displayed.append(-((H+2)*displayed[0]*displayed[1]+displayed[0]**3/3
                          +(A+mp.mpf('.5'))*displayed[1]+displayed[0]**2/4+ell[1])/H)
        require(max(abs(a-b) for a,b in zip(alpha,displayed)) < mp.mpf('1e-75'),
                'general inverse recurrence diagnostic tolerance')
        root = smooth_root(logY,Q,ell,seed=n)
        inverse.append({'n':n,'log_a_n':fmt(logY),'t_minus_n':fmt(t-n),
                        'alpha':list(map(fmt,alpha)),
                        'profile_errors':[fmt(t+mp.fsum(alpha[j]*t**(-j) for j in range(J+1))-n)
                                          for J in range(3)],
                        'H4_root_minus_n':fmt(root-n),
                        'scaled_H4_error':fmt((root-n)*n**6*mp.log(n))})
        single_lr = mp.e*(1-mp.mpf(1)/n)**n*Q/ratio
        size_two_lr = mp.e**2*(1-mp.mpf(2)/n)**n*Q/ratio
        require(single_lr > 1 and size_two_lr < 1, 'finite-n TV sign diagnostic')
        value = (1+(1-mp.mpf(1)/n)**n)/ratio-(1+q)/Q
        tv.append({'n':n,'TV':fmt(value),'n_times_TV':fmt(n*value),
                   'n2_residual':fmt(n*n*(value-tv_coefficient/n)),
                   'singleton_likelihood_ratio':fmt(single_lr),
                   'size_two_max_likelihood_ratio':fmt(size_two_lr)})
    cutoff = []
    for r in range(1,5):
        b = cutoff_majorants(200,r,'.09')
        cutoff.append({'r':r,'majorant_coefficient':b['majorant_coefficient'],
                       'missing_unnormalized_tail_majorant':fmt(b['missing_tail']),
                       'normalization_majorant':fmt(b['normalization']),
                       'total_majorant_diagnostic':fmt(b['total'])})
    general = []
    for tau,sigma,Lbox in [('0.5','-0.7',120),('1.3','0.4',70),('2','1',50)]:
        cc = row_box_coefficients(Lbox,3,tau,sigma)
        qt = partition_product(tau)
        T,S = mp.mpf(tau),mp.mpf(sigma)
        direct = -T*mp.fsum(j*j/mp.expm1(T*j) for j in range(1,1201)) + (
            T/2-S)*mp.fsum(j/mp.expm1(T*j) for j in range(1,1201))
        general.append({'tau':tau,'sigma':sigma,'box_L':Lbox,'coefficients':list(map(fmt,cc)),
                        'c1_Lambert_difference':fmt(cc[1]-direct),
                        'n60_scaled_third_order_remainder':fmt((normalized_walk(60,tau,sigma)/qt
                            -mp.fsum(cc[r]/60**r for r in range(4)))*60**4)})
    compiled = compile_multiplicity(4,False)
    result = {
        'status':'PASS diagnostic tolerances and exact rational subchecks',
        'qualification':'Ordinary 85-digit mpmath arithmetic; no directed rounding or certified numerical interval',
        'precision_decimal_digits':85,'printed_significant_digits':65,
        'multiplicity_largest_part_J':200,'row_box_L':175,'Q_product_terms':1200,
        'multiplicity_moment_states':len(compiled['states']),
        'exact_single_part_multiplicity_checks':rational_tests,
        'exact_rational_logarithmic_coefficients':[str(x) for x in rational_log],
        'small_exact_normalized_walk_diagnostics':small_walk_checks,
        'empty_logarithmic_list_inverse_orders_checked':[0,1],
        'Q':fmt(Q),'mu':fmt(mu),'coefficients':list(map(fmt,c)),
        'row_box_coefficients':list(map(fmt,box)),
        'row_box_minus_multiplicity':list(map(fmt,differences)),
        'c1_plus_Lambert_mu':fmt(c[1]+mu),'logarithmic_coefficients':list(map(fmt,ell)),
        'TV_coefficient':fmt(tv_coefficient),'forward':forward,'inverse':inverse,
        'TV':tv,'cutoff':cutoff,'general_parameters':general,
        'threshold_warning':'Smooth root errors are diagnostics only; the asymptotic two-ceiling constant is not numerically certified. Exact integer threshold boundary checks are in exact_checks.json.',
        'normalization_note':'Multiplicities use Q_J conditional normalization; row-box sums are divided by the full-product approximation to Q.'}
    (output_dir/'numerical_diagnostics.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    return result


if __name__ == '__main__':
    result = run(Path(__file__).resolve().parent/'results')
    print('Numerical diagnostics passed; coefficients:', ', '.join(result['coefficients']))
