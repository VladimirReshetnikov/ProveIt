#!/usr/bin/env python3
"""Exact Takeuchi recurrence residuals at any requested fixed order.

Requires Python 3 and SymPy. No numerical fitting, external data, or CAS-specific
notebooks. The residual returned is for sum_k c(n,k) v(n-k-1)/v(n); the known
forcing is superpolynomially small and not part of the formal h=1/n series.
"""
import argparse
import json
import time
from pathlib import Path
import sympy as s

w, k = s.symbols('w k')
d = w / (1 + w)
g = w**2 / 2 - s.log(1 + w) / 2
p1 = -w**2*(26*w**2+67*w+46)/(24*(1+w)**3)
p2 = -w**2*(12*w**6+100*w**5+310*w**4+457*w**3+310*w**2+36*w-54)/(48*(1+w)**6)


def cancel(expr):
    return s.cancel(expr)


def shift_derivative(jets, order):
    """D(sum h^m f_m) = sum h^(m+1) [d f'_m - m f_m]."""
    return {m+1: cancel(d*s.diff(f,w)-m*f)
            for m,f in jets.items() if m < order}


def log_product_coefficient(r):
    """[h^r] log[(1-kh) product_(i=0)^(k-1) (1+ih)]."""
    powersum = (s.bernoulli(r+1,k)-s.bernoulli(r+1,0))/(r+1)
    return s.expand(((-1)**(r+1)*powersum-k**r)/r)


def residual_coefficients(order, corrections=(), progress=False):
    """Return A[1..order], R[0..order] as exact SymPy expressions.

    corrections[j-1] is p_j(w), in log v = F+g+sum_j p_j h^j,
    with F'(n)=w and w=W(n). All inputs may be rational functions of w;
    generic symbolic smooth coefficients work with the slower EX domain.
    R[r] = E B_r(K), K~Poisson(w), where exp(sum A_r h^r)=sum B_r h^r.
    Every formal step is finite. There is no claim that the series converges.
    """
    if order < 1:
        raise ValueError('order must be positive')
    rational = all(s.sympify(p).is_rational_function(w) for p in corrections)
    domain = s.QQ.frac_field(w) if rational else s.EX
    poly = lambda f: s.Poly(f,k,domain=domain)
    zero, one = poly(0), poly(1)
    # These are coefficients of D(log v), not log v itself.
    jets = {0:w, 1:cancel(d*s.diff(g,w))}
    for j,p in enumerate(corrections,1):
        if j+1 <= order:
            jets[j+1] = cancel(d*s.diff(p,w)-j*p)
    A = [zero for _ in range(order+1)]
    for t in range(1,order+2):
        shift = poly((-k-1)**t / s.factorial(t))
        for m,f in jets.items():
            if m <= order:
                A[m] += shift.mul_ground(f)
        jets = shift_derivative(jets,order)
    A[0] += poly((k+1)*w)  # remove base ratio exp[-(k+1)w]
    assert A[0].is_zero
    for r in range(1,order+1):
        A[r] += poly(log_product_coefficient(r))
    B = [one]
    moments = [s.bell(i,w) for i in range(2*order+1)]
    residuals = [s.Integer(1)]
    for r in range(1,order+1):
        br = sum((i*A[i]*B[r-i] for i in range(1,r+1)),zero).mul_ground(s.Rational(1,r))
        B.append(br)
        er = sum((coef*moments[power[0]] for power,coef in br.terms()),s.S.Zero)
        er = s.factor(er)
        residuals.append(er)
        if progress:
            print('R_%d = %s' % (r,er),flush=True)
    return [a.as_expr() for a in A], residuals


def solve_rational_ode(H,j,denominator_power,numerator_degree,factor_power=0):
    """Try one explicitly specified rational ansatz; fail rather than assume it.

    p=w^factor_power * (sum_(i=0)^(degree-factor_power) a_i w^i)
      /(1+w)^denominator_power.
    Returns None if inconsistent or if the solution is not unique.
    """
    a = s.symbols('a0:%d' % (numerator_degree-factor_power+1))
    trial = w**factor_power*sum(ai*w**i for i,ai in enumerate(a))/(1+w)**denominator_power
    equation = s.together(-w*s.diff(trial,w)+j*(w+1)*trial+H).as_numer_denom()[0]
    system = s.Poly(equation,w).all_coeffs()
    solutions = s.solve(system,a,dict=True)
    if len(solutions) != 1 or any(ai not in solutions[0] for ai in a):
        return None
    p = s.factor(trial.subs(solutions[0]))
    assert cancel(-w*s.diff(p,w)+j*(w+1)*p+H) == 0
    return p


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order',type=int,default=4)
    parser.add_argument('--include-p3',action='store_true')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    start=time.time()
    corrections=[p1,p2]
    _,residuals=residual_coefficients(4,corrections,progress=True)
    H3=residuals[4]
    p3=solve_rational_ode(H3,3,9,13,2)
    print('H3 =',H3,flush=True)
    print('p3 =',p3,flush=True)
    if p3 is None:
        raise RuntimeError('The prescribed rational ansatz is inconsistent or nonunique')
    print('ODE check =',cancel(-w*s.diff(p3,w)+3*(w+1)*p3+H3),flush=True)
    if args.include_p3:
        corrections.append(p3)
    if args.order != 4 or args.include_p3:
        _,checked=residual_coefficients(args.order,corrections,progress=True)
    else:
        checked=residuals
    if args.include_p3:
        assert all(r == 0 for r in checked[1:5])
    result={'H3':s.sstr(H3),'p3':s.sstr(p3),
            'H3_latex':s.latex(H3),'p3_latex':s.latex(p3),
            'residuals':[s.sstr(r) for r in checked],
            'order':args.order,'include_p3':args.include_p3,
            'elapsed_seconds':time.time()-start,'sympy_version':s.__version__}
    print('elapsed_seconds = %.3f' % result['elapsed_seconds'],flush=True)
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')

if __name__ == '__main__':
    main()
