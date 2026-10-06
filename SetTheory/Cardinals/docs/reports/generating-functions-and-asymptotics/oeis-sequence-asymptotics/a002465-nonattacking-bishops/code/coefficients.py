"""Exact fixed-order saddle algebra. No numerical fitting is used.

The angular and affine engines intentionally share only SymPy and input validation.
Their amplitude construction, phase algebra, and Gaussian integration differ.
"""
from functools import lru_cache
import sympy as sp

r, x, d = sp.symbols('r x d')


def require_order(order):
    if isinstance(order, bool) or not isinstance(order, int) or order < 0:
        raise ValueError('order must be a nonnegative integer')


def angular_amplitudes(order):
    """Return P_0,...,P_order by logarithms and Touchard polynomials."""
    require_order(order)
    a, k = sp.symbols('a k', integer=True)
    logs = [sp.Integer(0)]
    for j in range(1, order + 1):
        logs.append(sp.expand(sp.summation(
            ((-1)**(j+1)*(2*d-2*k)**j + k**j)/sp.Integer(j), (k, 0, a-1))))
    qs = [sp.Integer(1)]
    for j in range(1, order + 1):
        qs.append(sp.expand(sum(k*logs[k]*qs[j-k] for k in range(1, j+1))/j))
    return [sp.expand(sum(c*sp.bell(m[0], x/2)
                         for m, c in sp.Poly(q, a).terms())) for q in qs]


def angular_coefficients(order):
    """Return (P, c), with c keyed by delta 0 and 1/2, to any fixed order.

    All operations are exact in Q(r); high order costs grow very rapidly.
    """
    require_order(order)
    U, V = sp.symbols('U V')
    P = angular_amplitudes(order)
    K = 2*order
    f = [0] + [sp.I**j*sp.bell(j, r)*(U**j+V**j)/(r*sp.factorial(j))
               for j in range(1, K+3)]
    ell = [sp.Integer(0)]
    for j in range(1, len(f)):
        ell.append(sp.expand(f[j]-sum(k*ell[k]*f[j-k] for k in range(1, j))/j))
    if sp.expand(ell[1]-sp.I*(U+V)) != 0:
        raise ArithmeticError('angular linear saddle term did not cancel')
    if sp.expand(ell[2]+(r*U**2-2*U*V+r*V**2)/2) != 0:
        raise ArithmeticError('angular quadratic saddle term mismatch')
    phase = [sp.Integer(0)] + ell[3:]
    G = [sp.Integer(1)]
    for j in range(1, K+1):
        G.append(sp.expand(sum(k*phase[k]*G[j-k] for k in range(1, j+1))/j))

    @lru_cache(None)
    def moment(a, b):
        if a < 0 or b < 0:
            raise ValueError('negative Gaussian moment index')
        if (a+b) % 2:
            return sp.Integer(0)
        if a == b == 0:
            return sp.Integer(1)
        if a:
            return ((a-1)*r/(r*r-1)*moment(a-2, b) if a >= 2 else 0) + (
                b/(r*r-1)*moment(a-1, b-1) if b else 0)
        return (b-1)*r/(r*r-1)*moment(0, b-2)

    def expect(poly):
        return sp.factor(sp.together(sum(c*moment(*m)
                    for m, c in sp.Poly(sp.expand(poly), U, V).terms())))

    result = {}
    for delta in (sp.Integer(0), sp.Rational(1, 2)):
        factors = []
        for dd, var in ((delta, U), (-delta, V)):
            co = [sp.Integer(0)]*(K+1)
            for j in range(order+1):
                p = P[j].subs(d, dd)
                for k in range(K-2*j+1):
                    co[2*j+k] += sp.I**k*var**k*p.subs(x, r)/sp.factorial(k)
                    p = sp.expand(x*(sp.diff(p, x)+p/2))
            factors.append(co)
        amp = [sp.expand(sum(factors[0][j]*factors[1][m-j]
                            for j in range(m+1))) for m in range(K+1)]
        result[str(delta)] = [expect(sum(G[k]*amp[2*j-k] for k in range(2*j+1)))
                              for j in range(order+1)]
    return P, result


def affine_coefficients(order):
    """Independent oracle: affine contours and independent Gaussian coordinates.

    P_j comes from finite-product interpolation, log from finite powers, exp
    from integer partitions, and moments from independent diagonal coordinates.
    The Jacobian 1/((1+i eps U)(1+i eps V)) is essential.
    """
    require_order(order)
    z, w = sp.symbols('z w')
    K = 2*order

    def add(a, b):
        out = list(a) + [sp.Integer(0)]*max(0, len(b)-len(a))
        for i, v in enumerate(b):
            out[i] += v
        return [sp.expand(v) for v in out]

    def mul(a, b, limit):
        out = [sp.Integer(0)]*(min(limit, len(a)+len(b)-2)+1)
        for i, v in enumerate(a):
            for j, vv in enumerate(b):
                if i+j <= limit:
                    out[i+j] += v*vv
        return [sp.expand(v) for v in out]

    def power(a, k, limit):
        out = [sp.Integer(1)]
        for _ in range(k):
            out = mul(out, a, limit)
        return out

    def partitions(total, minimum=1):
        if total == 0:
            yield ()
        for p in range(minimum, total+1):
            for rest in partitions(total-p, p):
                yield (p,) + rest

    def exp_coefficient(a, k):
        out = sp.Integer(0)
        for partition in partitions(k):
            term = sp.Integer(1)
            for j in set(partition):
                multiplicity = partition.count(j)
                term *= a[j]**multiplicity/sp.factorial(multiplicity)
            out += term
        return sp.expand(out)

    P = []
    for j in range(order+1):
        values = []
        for a in range(2*j+1):
            product = [sp.Integer(1)]
            for k in range(a):
                ratio = [sp.Integer(1)] + [k**s+(2*d-2*k)*k**(s-1)
                                           for s in range(1, j+1)]
                product = mul(product, ratio, j)
            values.append(product[j] if j < len(product) else sp.Integer(0))
        polynomial = sp.Integer(0)
        for k in range(len(values)):
            polynomial += values[0]*(x/2)**k/sp.factorial(k)
            values = [sp.expand(values[i+1]-values[i]) for i in range(len(values)-1)]
        P.append(sp.expand(polynomial))

    u, v = z+w, z-w
    fm = [sp.Integer(0)] + [sp.expand(sp.I**m*r**(m-1)*(u**m+v**m)/sp.factorial(m))
                            for m in range(1, K+3)]
    lf = [sp.Integer(0)]*(K+3)
    for j in range(1, K+3):
        lf = add(lf, [sp.expand(sp.Rational((-1)**(j+1), j)*a)
                      for a in power(fm, j, K+2)])
    fullphase = [sp.Integer(0)] + [sp.expand(lf[m] -
                  sp.Rational((-1)**(m+1), m)*sp.I**m*(u**m+v**m))
                  for m in range(1, K+3)]
    if fullphase[1] != 0 or sp.expand(fullphase[2]+(r-1)*z*z+(r+1)*w*w) != 0:
        raise ArithmeticError('affine saddle normalization mismatch')
    phase = [sp.Integer(0)] + fullphase[3:]
    G = [exp_coefficient(phase, k) for k in range(K+1)]

    def expect(poly):
        total = sp.Integer(0)
        for (a, b), c in sp.Poly(sp.expand(poly), z, w).terms():
            if a % 2 == 0 and b % 2 == 0:
                total += c*sp.factorial2(a-1)*sp.factorial2(b-1) / (
                    (2*(r-1))**(a//2)*(2*(r+1))**(b//2))
        return sp.factor(sp.together(total))

    result = {}
    for delta in (sp.Integer(0), sp.Rational(1, 2)):
        factors = []
        for var, dd in ((u, delta), (v, -delta)):
            A = [sp.Integer(0)]*(K+1)
            for j in range(order+1):
                limit = K-2*j
                p = P[j].subs(d, dd)
                pc = [sp.expand(sp.diff(p, x, k).subs(x, r)*(sp.I*r*var)**k/sp.factorial(k))
                      for k in range(limit+1)]
                ec = [(sp.I*r*var/2)**k/sp.factorial(k) for k in range(limit+1)]
                jac = [(-sp.I*var)**k for k in range(limit+1)]
                product = mul(mul(pc, ec, limit), jac, limit)
                A = add(A, [sp.Integer(0)]*(2*j)+product)
            factors.append(A)
        A = mul(*factors, K)
        result[str(delta)] = [expect(sum(G[k]*A[2*j-k] for k in range(2*j+1)))
                              for j in range(order+1)]
    return P, result


def log_coefficients(coefficients):
    """Exact coefficients of log(sum c_j u^j), with c_0=1."""
    if not coefficients or coefficients[0] != 1:
        raise ValueError('log series must have constant coefficient 1')
    ell = [sp.Integer(0)]
    for j in range(1, len(coefficients)):
        ell.append(sp.factor(coefficients[j] - sum(
            k*ell[k]*coefficients[j-k] for k in range(1, j))/j))
    return ell
