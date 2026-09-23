#!/usr/bin/env python3
"""Finite exact checks accompanying the surcomplex Gamma--zeta manuscript.

Requires Python 3 and SymPy.  These checks are not a proof assistant and do
not verify strong summability, surreal inequalities, or universal theorems.
Run from any directory; results.json is written beside this script.
"""
from __future__ import annotations

import json
import math
import platform
from pathlib import Path
from fractions import Fraction
import sympy as sp

T = sp.Symbol('t')
S = sp.Symbol('s')
L, C = sp.symbols('L C')  # formal log(x), log(2*pi)/2
RESULTS: list[dict[str, object]] = []


def check(name: str, expression: sp.Expr | bool, detail: str = '') -> None:
    ok = expression if isinstance(expression, bool) else sp.simplify(expression) == 0
    RESULTS.append({'name': name, 'passed': bool(ok), 'detail': detail})
    if not ok:
        raise AssertionError(f'{name}: {expression}')


def trim(expr: sp.Expr, order: int) -> sp.Expr:
    return sp.series(sp.expand(expr), T, 0, order + 1).removeO().expand()


def binom_series(exponent: sp.Expr, order: int) -> sp.Expr:
    return sp.Add(*(sp.prod(exponent - j for j in range(k)) / sp.factorial(k)
                    * T**k for k in range(order + 1)))


def loggamma_shift(shift: sp.Expr, order: int) -> sp.Expr:
    logpart = L + sp.Add(*((-1)**(j+1) * shift**j * T**j / j
                           for j in range(1, order + 3)))
    out = (1/T + shift-sp.Rational(1,2))*logpart - 1/T-shift+C
    for r in range(1, (order + 2)//2 + 1):
        m = 2*r-1
        out += sp.bernoulli(2*r)/(2*r*m) * T**m * sp.Add(*(
            (-1)**k * sp.rf(m,k)/sp.factorial(k) * shift**k * T**k
            for k in range(max(0,order-m)+1)))
    return trim(out,order)


def conv(a: list[Fraction], b: list[Fraction], nmax: int) -> list[Fraction]:
    c = [Fraction(0) for _ in range(nmax+1)]
    for m in range(1,nmax+1):
        if a[m]:
            for n in range(1,nmax//m+1):
                if b[n]:
                    c[m*n] += a[m]*b[n]
    return c


def run() -> None:
    order = 8
    base = loggamma_shift(sp.Integer(0), order)
    check('Stirling recurrence through t^8',
          trim(loggamma_shift(sp.Integer(1),order)-base-L,order))
    for m in [2,3,4,5]:
        lhs = sum(loggamma_shift(sp.Rational(r,m),order) for r in range(m))
        rhs = (sp.Rational(m,1)/T-sp.Rational(1,2))*(L+sp.log(m))-m/T+C
        rhs += sum(sp.bernoulli(2*r)/(2*r*(2*r-1))*(T/m)**(2*r-1)
                   for r in range(1,(order+2)//2+1))
        rhs += (m-1)*C+(sp.Rational(1,2)-m/T)*sp.log(m)
        check(f'Gauss multiplication m={m} through t^8',trim(lhs-rhs,order))

    h = sp.Symbol('h')
    shifted = loggamma_shift(h,6)-loggamma_shift(sp.Integer(0),6)-h*L
    expected = sum((-1)**(n+1)*(sp.bernoulli(n+1,h)-sp.bernoulli(n+1,0))
                   / (n*(n+1))*T**n for n in range(1,7))
    check('Bernoulli finite shift through t^6',trim(shifted-expected,6))

    correction = sum(sp.bernoulli(2*r)/(2*r*(2*r-1))*T**(2*r-1)
                     for r in range(1,4))
    coefficients = [1,sp.Rational(1,12),sp.Rational(1,288),
                    -sp.Rational(139,51840),-sp.Rational(571,2488320),
                    sp.Rational(163879,209018880)]
    expansion = sp.exp(correction).series(T,0,6).removeO().expand()
    for degree, expected_coefficient in enumerate(coefficients):
        check(f'Stirling exponential coefficient {degree}',
              expansion.coeff(T,degree)-expected_coefficient)

    # H(s,1/t)/t^s and the same expression at a+1, with symbolic s.
    N = 6
    raw = 1/(T*(S-1))+sp.Rational(1,2)
    shifted_h = binom_series(1-S,N+1)/(T*(S-1))
    shifted_h += sp.Rational(1,2)*binom_series(-S,N)
    for r in range(1,4):
        m = 2*r-1
        coefficient = sp.bernoulli(2*r)/sp.factorial(2*r)*sp.rf(S,m)
        raw += coefficient*T**m
        shifted_h += coefficient*T**m*binom_series(-S-m,N-m)
    residual = sp.expand(sp.cancel(raw-shifted_h-1))
    for power in range(-1,N+1):
        check(f'Hurwitz difference symbolic coefficient t^{power}',
              residual.coeff(T,power))

    for r in range(1,13):
        m = 2*r-1
        derivative = sp.diff(sp.rf(S,m),S).subs(S,0)
        check(f'Lerch coefficient r={r}',
              sp.bernoulli(2*r)/sp.factorial(2*r)*derivative
              - sp.bernoulli(2*r)/(2*r*(2*r-1)))
        check(f'Hurwitz finite-part coefficient r={r}',
              sp.bernoulli(2*r)/sp.factorial(2*r)*sp.rf(1,m)
              -sp.bernoulli(2*r)/(2*r))

    A = sp.Symbol('a')
    for m in range(0,13):
        special = -A**(m+1)/sp.Integer(m+1)+sp.Rational(1,2)*A**m
        for r in range(1,(m+1)//2+1):
            special += sp.bernoulli(2*r)/sp.factorial(2*r)*sp.rf(-m,2*r-1)*A**(m+1-2*r)
        check(f'Hurwitz Bernoulli polynomial m={m}',
              sp.expand(special+sp.bernoulli(m+1,A)/(m+1)))

    nmax=128
    one=[Fraction(0)]+[Fraction(1) for _ in range(nmax)]
    mob=[Fraction(0)]+[Fraction(int(sp.mobius(n))) for n in range(1,nmax+1)]
    inv=conv(one,mob,nmax)
    check('Mobius convolution through index 128',
          all(inv[n]==(1 if n==1 else 0) for n in range(1,nmax+1)))
    b=one.copy(); b[1]=Fraction(0)
    power=b.copy(); logarithm=[Fraction(0) for _ in range(nmax+1)]
    for k in range(1,int(math.log2(nmax))+1):
        factor=Fraction((-1)**(k+1),k)
        logarithm=[v+factor*p for v,p in zip(logarithm,power)]
        power=conv(power,b,nmax)
    for n in range(2,nmax+1):
        factors=sp.factorint(n)
        expected_coeff=Fraction(1,int(next(iter(factors.values())))) if len(factors)==1 else Fraction(0)
        check(f'Euler logarithm arithmetic coefficient n={n}',
              logarithm[n]==expected_coeff)

    z1,z2,z3,z4=sp.symbols('z1 z2 z3 z4')
    a,b,c,d=sp.symbols('a b c d')
    mat3=sp.Matrix([[1,1,1],[-a,-b,-c],[2*z1,2*z2,2*z3]])
    jac3=sp.expand(mat3.det())
    check('Mixed dilation Jacobian selected coefficient (3 rows)',
          jac3.coeff(z3)-2*(a-b))
    mat4=sp.Matrix([[1,1,1,1],[-a,-b,-c,-d],
                    [2*z1,2*z2,2*z3,2*z4],
                    [-4*a*z1,-4*b*z2,-4*c*z3,-4*d*z4]])
    selected=sp.expand(mat4.det()).coeff(z3,1).coeff(z4,1)
    check('Mixed dilation Jacobian selected coefficient (4 rows)',
          selected-8*(a-b)*(c-d), str(sp.factor(selected)))
    vandermonde=sp.Matrix([[1,1,1],[a,b,c],[a*a,b*b,c*c]]).det()
    check('Vandermonde coefficient identity',
          vandermonde-(b-a)*(c-a)*(c-b))

    gamma=sp.Symbol('gamma')
    local=sp.exp(-gamma*T+sp.pi**2/12*T*T).series(T,0,3).removeO()
    check('Finite Gamma epsilon coefficient',
          local.expand().coeff(T,2)-gamma**2/2-sp.pi**2/12)


if __name__ == '__main__':
    status='passed'
    error=None
    try:
        run()
    except Exception as exc:
        status='failed'
        error=f'{type(exc).__name__}: {exc}'
    output={
        'status':status,
        'python_version':platform.python_version(),
        'sympy_version':sp.__version__,
        'check_count':len(RESULTS),
        'passed_count':sum(bool(r['passed']) for r in RESULTS),
        'formal_proof_assistant_checked':False,
        'scope':'Finite exact symbolic and arithmetic checks only; not proofs of the surreal theorems.',
        'error':error,
        'checks':RESULTS,
    }
    outpath=Path(__file__).resolve().with_name('results.json')
    outpath.write_text(json.dumps(output,indent=2)+'\n',encoding='utf-8')
    print(f"{status}: {output['passed_count']}/{output['check_count']} checks; {outpath}")
    if error:
        raise SystemExit(error)
