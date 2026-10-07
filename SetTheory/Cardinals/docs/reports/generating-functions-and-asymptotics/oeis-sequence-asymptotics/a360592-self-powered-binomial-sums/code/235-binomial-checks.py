#!/usr/bin/env python3
"""Exact rational corroboration for Report235; no network or source writes."""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
import argparse
from fractions import Fraction
import sympy as S
from sympy.functions.combinatorial.numbers import stirling
from common import emit, new_file_path, require
from coupling import coupling_checks
from algebra import (A, b, c, t, u, r, h, associated_stirling, centered_moment,
    defect, expansion, scalar_log_coeffs, theta, signed_density, weighted_truncate,
    binomial_defect, finite_weights, recurrent_weights, coefficients)

z = S.symbols('z')

def gaussian_derivative(poly, degree):
    for _ in range(degree):
        poly=S.expand(S.diff(poly,z)-S.Rational(3,2)*z*poly)
    return poly

def operator_coefficients(K):
    # E F(tX) = [exp(c*sum_{j>=2} t^(j-1) D^j/j!) F](c).
    # Remove the common Gaussian exp(-3z²/4) before differentiating.
    V=S.Rational(3,4)*z*z
    for j in range(1,K+2):
        V+=t**(2*j)*defect(j).subs(r,z/t)
    V=S.Poly(S.expand(V),t)
    v={j:V.coeff_monomial(t**j) for j in range(1,K+1)}
    H={0:S.Integer(1)}
    for j in range(1,K+1):
        H[j]=S.expand(sum(s*v[s]*H[j-s] for s in range(1,j+1))/j)
    # The operator coefficients are polynomials in a formal derivative d.
    d=S.symbols('d')
    O={0:S.Integer(1)}
    for j in range(1,K+1):
        O[j]=S.expand(sum(s*c*d**(s+1)*O[j-s]/S.factorial(s+1)
                           for s in range(1,j+1))/j)
    coeffs=[]
    for k in range(K+1):
        value=0
        for j in range(k+1):
            for (deg,),v0 in S.Poly(O[j],d).terms():
                value+=v0*gaussian_derivative(H[k-j],deg).subs(z,c)
        coeffs.append(S.expand(value))
    return coeffs


def average(P):
    out=0
    for (i,j),co in S.Poly(S.expand(P),t,u).terms():
        out+=co*t**i*sum(associated_stirling(j,k)*c**k*t**(j-k)
                         for k in range(j//2+1))
    return S.expand(out)

def direct_raw_marked(K=2):
    J=K+2; W=2*J+1
    V=A*c*c+sum(t**(2*j)*defect(j).subs(r,(c+u)/t) for j in range(1,J+2))
    V=weighted_truncate(V,W)
    term=P=S.Integer(1)
    for j in range(1,W+1):
        term=weighted_truncate(term*V/j,W)
        P+=term
    M=[average(weighted_truncate(P*(c+u)**d,W)) for d in range(3)]
    # Finite series quotient, avoiding symbolic rational expression blow-up.
    M=[S.series(m,t,0,J+1).removeO().expand() for m in M]
    inv=S.series(1/M[0],t,0,J+1).removeO().expand()
    raw1=S.series(M[1]*inv,t,0,J+1).removeO().expand()
    raw2=S.series(M[2]*inv,t,0,J+1).removeO().expand()
    mean=S.series(raw1/t,t,0,K+1).removeO().expand()
    variance=S.series((raw2-raw1**2)/t**2,t,0,K+1).removeO().expand()
    return mean,variance


def run():
    C = expansion(4)
    require(all(S.expand(x-y) == 0 for x,y in zip(C, operator_coefficients(4))),
            'scalar and differential generators differ')
    for d in range(13):
        alt = sum(S.binomial(d,j)*(-c)**(d-j)*t**j *
                  sum(stirling(j,k,kind=2)*(c/t)**k for k in range(j+1))
                  for j in range(d+1))
        require(S.expand(alt-centered_moment(d)) == 0, 'centered moment mismatch')
    x = S.Symbol('x')
    for rr in range(10):
        finite = (S.Rational(1,2)/x-S.Rational(rr,2))*S.log(1+rr*x)-S.Rational(rr,2)
        finite += sum(S.log(1+(rr-2*hh)*x) for hh in range(rr))
        poly = S.Poly(S.series(finite,x,0,6).removeO().expand(),x)
        for j in range(1,6):
            require(S.expand(poly.coeff_monomial(x**j)-defect(j).subs(r,rr)) == 0,
                    'direct finite logarithm mismatch')
    expected = [1,1,2,5,14,44,149,543,2096,8539,36444,162380,752181]
    require([sum(finite_weights(n).values()) for n in range(len(expected))] == expected,
            'OEIS A360592 prefix mismatch')
    fixtures = []
    for n in [0,1,2,3,8,9,19,20,60,99,100,199,200]:
        weights = finite_weights(n)
        require(weights == recurrent_weights(n), 'full exact marked recurrence mismatch')
        moments = [sum(rr**d*w for rr,w in weights.items()) for d in range(5)]
        marks = {str(q): str(sum((Fraction(w)*q**rr for rr,w in weights.items()), Fraction(0)))
                 for q in (Fraction(1,2), Fraction(1), Fraction(3,2))}
        fixtures.append({'n': n, 'raw_marked_moment_sums_0_to_4': moments,
                         'marked_weight_polynomial_values': marks})
    L = scalar_log_coeffs(4)
    expected_L = [0, c/4+11*c**3/8, 15*c*c/16-11*c**4/3,
                  -5*c/96-577*c**3/96+7487*c**5/640,
                  -169*c*c/96+12035*c**4/384-1249*c**6/30]
    require(all(S.expand(x-y) == 0 for x,y in zip(L,expected_L)), 'scalar log fixture mismatch')
    mean, var = direct_raw_marked(2)
    wanted_mean = c/t-2*A*c*c+sum(theta(L[j])*t**j for j in [1,2])
    wanted_var = c/t-4*A*c*c+sum(theta(L[j],2)*t**j for j in [1,2])
    require(S.expand(mean-wanted_mean) == 0, 'direct raw mean mismatch')
    require(S.expand(var-wanted_var) == 0, 'direct raw variance mismatch')
    P1,Z1 = signed_density(1)
    require(S.expand(P1-(1-A*u*u+t*(A*c+c**3/4)+t*(A+3*c*c/4)*u)) == 0,
            'first signed density mismatch')
    require(S.expand(Z1-1-c**3*t/4) == 0, 'first normalizer mismatch')
    # Exact normalized weighted logarithm versus the binomial logarithm.
    nu, y = S.symbols('nu y')
    mu = c/t
    delta = S.Rational(3,4)*c**3*t+(S.Rational(21,8)*c*c-S.Rational(55,24)*c**4)*t*t
    invM = S.Rational(3,2)*t*t-S.Rational(15,4)*c*t**3
    binlog = weighted_truncate(delta*u/c,5)
    for j in [1,2]:
        binlog += binomial_defect(j).subs({r:(c+u)/t,nu:mu+delta})*invM**j
    binlog = weighted_truncate(binlog,5)
    P,Z = signed_density(2)
    q = weighted_truncate(P-1,5)
    actual = weighted_truncate(q-q*q/2-S.series(S.log(Z),t,0,3).removeO(),5)
    target = S.Rational(5,8)*t*(u**3-3*c*t*u)
    require(S.expand(actual-binlog-target) == 0, 'full cubic log comparison mismatch')
    C3 = y**3-3*y*y+(2-3*mu)*y+2*mu
    require(S.expand(weighted_truncate(S.Rational(5,8)*t**4*C3.subs(y,u/t),5)-target) == 0,
            'third Charlier identification mismatch')
    # Exact symbolic CF derivative identities for L=nu*log(1+p*w)/p.
    # These rational/log expressions apply to each of the three parity-filter roots.
    nn,vv,pp,ww = S.symbols('nu v p w', nonzero=True)
    f = S.log(1+pp*ww)/pp
    fp = S.diff(f,pp)
    p_of = 1-vv/nn
    exponent = nn*f.subs(pp,p_of)
    require(S.simplify(S.diff(exponent,nn)-(f+(1-pp)*fp).subs(pp,p_of)) == 0,
            'exact CF mean derivative mismatch')
    require(S.simplify(S.diff(exponent,vv)+fp.subs(pp,p_of)) == 0,
            'exact CF variance derivative mismatch')
    require(S.expand(S.series(f+(1-pp)*fp,ww,0,3).removeO()-(ww-ww*ww/2)) == 0,
            'CF mean derivative expansion mismatch')
    require(S.expand(S.series(-fp,ww,0,3).removeO()-ww*ww/2) == 0,
            'CF variance derivative expansion mismatch')
    signed_checks = 0
    p = S.Symbol('p')
    for M in range(2,9):
        vn = M*p*(1-p)
        signed1 = sum((rr-M*p)*(-1)**rr*S.binomial(M,rr)*p**rr*(1-p)**(M-rr)
                      for rr in range(M+1))
        signed2 = sum((rr-M*p)**2*(-1)**rr*S.binomial(M,rr)*p**rr*(1-p)**(M-rr)
                      for rr in range(M+1))
        require(S.expand(signed1+2*vn*(1-2*p)**(M-1)) == 0, 'signed first moment mismatch')
        require(S.expand(signed2-vn*(4*vn-1)*(1-2*p)**(M-2)) == 0, 'signed second moment mismatch')
        signed_checks += 2
    return {'status': 'PASS', 'scope': 'Finite exact rational and symbolic checks; analytic remainder and global infimum proofs are in the article.',
            'independent_scalar_orders_0_to_4': True, 'centered_moments_through': 12,
            'direct_defect_checks': 50, 'OEIS_A360592_prefix': expected,
            'exact_marked_fixtures': fixtures, 'coefficients': coefficients(4),
            'direct_raw_mean_through_t2': str(mean), 'direct_raw_variance_through_t2': str(var),
            'exact_log_density_difference_weight5': str(S.expand(actual-binlog)),
            'exact_CF_derivative_identities': True, 'exact_signed_moment_polynomial_checks': signed_checks,
            'supplementary_residue_coupling': coupling_checks(),
            'integer_decimal_digit_cap': sys.get_int_max_str_digits()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output')
    args = parser.parse_args()
    if args.output is not None:
        new_file_path(args.output)
    emit(run(), args.output)


if __name__ == '__main__':
    try:
        main()
    except (ValueError, RuntimeError, OSError, ArithmeticError) as exc:
        raise SystemExit(str(exc))
