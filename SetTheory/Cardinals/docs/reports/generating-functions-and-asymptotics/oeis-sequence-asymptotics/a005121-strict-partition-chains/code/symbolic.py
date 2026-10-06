#!/usr/bin/env python3
"""Optional exact SymPy construction for Report223; bounded fixed orders only.

Default/order cap: 4. The mathematical recipe is arbitrary-fixed-order; this
implementation cap prevents accidental symbolic expression blow-up. No process
settings are changed. All checks survive Python -O.
"""
import argparse
import sys
import sympy as s
from sympy.functions.combinatorial.numbers import stirling

k, L, t, i = s.symbols('k L t i')


def require_equal(a, b, label):
    if s.simplify(a - b) != 0:
        raise RuntimeError(label)


def configurations(e, j=3):
    if e == 0:
        yield {}
    elif j - 2 <= e:
        for m in range(e // (j - 2) + 1):
            for rest in configurations(e - m * (j - 2), j + 1):
                yield ({j: m, **rest} if m else rest)


def exp_coefficients(logs, order):
    out = [s.Integer(1)]
    for n in range(1, order + 1):
        out.append(s.expand(sum(r * logs[r] * out[n-r]
                                for r in range(1, n+1)) / n))
    return out


def kernel_coefficients(order):
    out = [s.Integer(0)] * (order + 1)
    for e in range(order + 1):
        ce = s.Integer(0)
        for config in configurations(e):
            d = sum((j-1)*m for j, m in config.items())
            ce += (2**d * s.ff(k, d) /
                   s.prod(s.factorial(m)*s.factorial(j)**m
                          for j, m in config.items()))
        logs = {r: s.expand((2*s.summation(i**r, (i, 0, k-1)) -
                            s.summation(i**r, (i, 0, 2*k-e-1)) +
                            (1+L/3)*k**r) / r)
                for r in range(1, order-e+1)}
        for r, coefficient in enumerate(exp_coefficients(logs, order-e)):
            out[e+r] += s.expand(ce * coefficient)
    result = [s.factor(value) for value in out]
    for j, value in enumerate(result):
        if s.Poly(value, k).degree() > 2*j:
            raise RuntimeError('kernel degree bound failed')
        if j:
            require_equal(value.subs(k, 0), 0, 'kernel constant failed')
    return result


def independent_fixed_deficit_checks(kernel):
    """Check all kernel polynomials by exact diagonal Stirling interpolation.

    A deficit-k Stirling polynomial has degree 2k. Ordinary Stirling rows give
    its values; Newton finite differences construct it without block defects.
    The proved degree bound in the article makes 2J+1 distinct k checks enough
    to verify a degree-2J kernel polynomial, though finite checks do not supply
    that theorem on their own.
    """
    J = len(kernel)-1
    x = s.Symbol('x')
    for fixed_k in range(1, 2*J+2):
        row = [1]
        values = []
        for n in range(2*fixed_k+3):
            if n:
                row = [0]+[(j*row[j] if j < len(row) else 0)+row[j-1]
                           for j in range(1, n+1)]
            values.append(row[n-fixed_k] if n >= fixed_k else 0)
        differences = values[:2*fixed_k+1]
        polynomial = s.Integer(0)
        for r in range(2*fixed_k+1):
            polynomial += differences[0]*s.ff(x, r)/s.factorial(r)
            differences = [b-a for a,b in zip(differences, differences[1:])]
        polynomial = s.Poly(s.expand(polynomial), x)
        for n in (2*fixed_k+1, 2*fixed_k+2):
            require_equal(polynomial.eval(n), values[n], 'Stirling diagonal extra node')
        numerator = [s.Integer(0)]*(J+1)
        for (power,), coefficient in polynomial.terms():
            degree = 2*fixed_k-power
            if degree <= J:
                numerator[degree] = 2**fixed_k*s.factorial(fixed_k)*coefficient
        # Multiply by the reciprocal squared falling-factorial factors.
        coefficients = numerator
        for h in range(1, fixed_k):
            coefficients = [s.expand(sum(coefficients[a]*(j-a+1)*h**(j-a)
                                         for a in range(j+1))) for j in range(J+1)]
        marked = [s.rf(1+L/3, j)*fixed_k**j/s.factorial(j) for j in range(J+1)]
        for j in range(J+1):
            calculated = sum(coefficients[a]*marked[j-a] for a in range(j+1))
            require_equal(calculated, kernel[j].subs(k, fixed_k),
                          'independent fixed-deficit kernel check')
    print('PASS independent Stirling-diagonal kernel checks through order', J)


def moment(poly):
    result = 0
    for (r,), coefficient in s.Poly(s.expand(poly), k).terms():
        result += coefficient if r == 0 else 2*coefficient*sum(
            stirling(r, h, kind=2)*L**h for h in range(1, r+1))
    return s.factor(result)


def corrections(order, kernel):
    coefficients = [s.Integer(1)]
    for m in range(1, order+1):
        unknown = s.Symbol('c')
        cs = coefficients + [unknown]
        residual = 0
        for j in range(m+1):
            for h in range(m+2-j):
                if j == 0 and h > 0:
                    continue
                a = m+1-j-h
                shift = s.Integer(1) if h == 0 else s.rf(j, h)*k**h/s.factorial(h)
                residual += cs[j]*shift*kernel[a]
        residual = moment(residual)
        require_equal(s.diff(residual, unknown), 2*m*L, 'triangular multiplier')
        value = s.factor(-residual.subs(unknown, 0)/(2*m*L))
        require_equal(residual.subs(unknown, value), 0, 'correction cancellation')
        s.Poly(value, L)  # exact polynomial membership, not Q(L) only
        coefficients.append(value)
    return coefficients


def check_inverse(order):
    V, beta, lam = s.symbols('V beta Lambda')
    ds = s.symbols('d1:'+str(order+1))
    vs = [V]
    for m in range(1, order+1):
        delta = sum(v*t**j for j, v in enumerate(vs))
        residual = lam*(delta-V)
        residual += sum(2*s.Rational((-1)**r, r*(r-1))*delta**r*t**(r-1)
                        for r in range(2, m+2))
        residual -= beta*sum(s.Rational((-1)**(r+1), r)*(t*delta)**r
                             for r in range(1, m+1))
        for j in range(1, m+1):
            residual += ds[j-1]*t**j*sum(
                (-1)**r*s.binomial(j+r-1, r)*(t*delta)**r
                for r in range(m-j+1))
        coefficient = s.expand(residual).coeff(t, m)
        value = s.factor(-coefficient/lam)
        require_equal(coefficient+lam*value, 0, 'inverse cancellation')
        vs.append(value)
    require_equal(vs[1], -(V*V-beta*V+ds[0])/lam, 'inverse v1')
    if order >= 2:
        expected = -((2*V-beta)*vs[1]-V**3/3+beta*V**2/2-ds[0]*V+ds[1])/lam
        require_equal(vs[2], expected, 'inverse v2')
    print('PASS formal inverse cancellation through order', order)


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if len(argv) > 2 or sum(map(len, argv)) > 32:
        raise ValueError('symbolic arguments exceed bound')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', choices=('1', '2', '3', '4'), default='4')
    order = int(parser.parse_args(argv).order)
    kernel = kernel_coefficients(order+1)
    independent_fixed_deficit_checks(kernel)
    require_equal(kernel[1], k*(L-k+1)/3, 'q1')
    require_equal(kernel[2], k*k*(L*L-2*L*k+5*L+k*k-6*k+5)/18, 'q2')
    require_equal(moment(kernel[1]), 0, 'q1 mean')
    require_equal(moment(kernel[2]), -L*L/3, 'q2 mean')
    cs = corrections(order, kernel)
    expected = [1, L/6, -L*(16*L**2+45*L-90)/3240,
                L**2*(10*L**2-81*L-270)/6480,
                L*(1792*L**5+32400*L**4+2358405*L**3-
                   1281420*L**2-8108100*L-408240)/146966400]
    for j, value in enumerate(cs):
        require_equal(value, expected[j], 'displayed coefficient')
        print('c'+str(j)+' =', value)
    logs = s.series(s.log(sum(value*t**j for j, value in enumerate(cs))),
                    t, 0, order+1).removeO()
    for j in range(1, order+1):
        ell = s.factor(s.expand(logs).coeff(t, j))
        print('ell'+str(j)+' =', ell)
    ell1 = L/6
    ell2 = -L*(8*L**2+45*L-45)/1620
    require_equal(s.expand(logs).coeff(t, 1), ell1, 'ell1')
    if order >= 2:
        require_equal(s.expand(logs).coeff(t, 2), ell2, 'ell2')
    # L(e^t)'=-1/2 and L(e^t)''=1/4 at t=0.
    Aq1, Aq2 = -1/L, 1/L**2
    require_equal(-Aq1/2, 1/(2*L), 'leading mean')
    require_equal(Aq2/4+Aq1/4, (1-L)/(4*L**2), 'leading variance')
    require_equal(-s.diff(ell1, L)/2, -s.Rational(1,12), 'mean 1/n')
    require_equal((s.diff(ell1,L,2)+s.diff(ell1,L))/4,
                  s.Rational(1,24), 'variance 1/n')
    require_equal(ell1+s.Rational(1,6), (1+L)/6, 'log coefficient d1')
    require_equal(ell2, -L*(16*L**2+90*L-90)/3240, 'log coefficient d2')
    print('PASS exact kernel, Touchard, correction, logarithm and cumulant identities')
    check_inverse(order)
    print('ALL SYMBOLIC LENGYEL CHECKS PASS')


if __name__ == '__main__':
    main()
