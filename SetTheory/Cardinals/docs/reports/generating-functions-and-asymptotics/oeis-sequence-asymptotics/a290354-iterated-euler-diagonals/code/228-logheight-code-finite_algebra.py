#!/usr/bin/env python3
"""Finite exact endpoint algebra and inverse identities, not remainder bounds."""
from fractions import Fraction as F
from math import factorial
from exact_euler import decimal_integer

MAX_COORDINATE_ORDER = 12
MAX_ENDPOINT_ORDER = 7
KNOWN_COORDINATE = [F(x) for x in ('-1/36', '1/540', '1/7776', '-71/435456',
    '8759/163296000', '31/20995200', '-183311/16460236800',
    '23721961/6207860736000', '293758693/117328567910400')]
KNOWN_RHO = {2: F(1,12), 3: F(17,1080), 4: F(13,3888),
    5: F(2071,2449440), 6: F(5131261,22044960000),
    7: F(261791507,3968092800000)}


def rational_string(value):
    value = F(value)
    numerator = decimal_integer(value.numerator)
    return numerator if value.denominator == 1 else numerator+'/'+decimal_integer(value.denominator)


def multiply(a, b, order):
    out = [F(0)]*(order+1)
    for i, x in enumerate(a[:order+1]):
        for j, y in enumerate(b[:order-i+1]):
            out[i+j] += x*y
    return out


def coordinate_coefficients(order=7):
    if isinstance(order, bool) or not isinstance(order, int) or not 0 <= order <= MAX_COORDINATE_ORDER:
        raise ValueError('coordinate order must be an integer from 0 to 12')
    degree = order+2
    g = [F(1, factorial(k+1)) for k in range(degree+1)]
    inverse = [F(1)]+[F(0)]*degree
    for k in range(1, degree+1):
        inverse[k] = -sum(g[j]*inverse[k-j] for j in range(1, k+1))
    logder = multiply([F(k+1)*g[k+1] for k in range(degree)], inverse, degree-1)
    logg = [F(0)]+[logder[k-1]/k for k in range(1, degree+1)]
    residual = [-2*inverse[k+1]+logg[k]/3 for k in range(degree)]
    residual[0] -= 1
    f = [F(0)]+g[:-1]
    power = [F(1)]+[F(0)]*degree
    result = []
    for j in range(1, order+1):
        power = multiply(power, f, degree)
        coefficient = -residual[j+1]/F(j, 2)
        result.append(coefficient)
        for k in range(degree):
            residual[k] += coefficient*(power[k]-(1 if k == j else 0))
    if any(residual[:order+2]):
        raise ArithmeticError('finite Abel residual did not vanish')
    return result


def endpoint_coefficients(order=7):
    """Factor Gamma(2-t/3)^-1; compute the remaining series over Q exactly.

    Each tuple r contributes degree D=sum(j+1)r_j and J=sum j*r_j,
    coefficient prod((-a_j*2**j)**r_j/r_j!), and denominator
    prod_(k=2)^(J+1)(k-t/3).  Only D<=order is enumerated.
    """
    if isinstance(order, bool) or not isinstance(order, int) or not 2 <= order <= MAX_ENDPOINT_ORDER:
        raise ValueError('endpoint order must be an integer from 2 to 7')
    a = coordinate_coefficients(order-1)
    terms = [(0, 0, F(1))]
    for j in range(1, order):
        extended = []
        for degree, weight, coefficient in terms:
            for r in range((order-degree)//(j+1)+1):
                extended.append((degree+(j+1)*r, weight+j*r,
                    coefficient*(-a[j-1]*2**j)**r/factorial(r)))
        terms = extended
    series = [F(0)]*(order+1)
    for degree, weight, coefficient in terms:
        inverse_product = [F(1)]+[F(0)]*(order-degree)
        for k in range(2, weight+2):
            factor = [F(1, k*(3*k)**q) for q in range(order-degree+1)]
            inverse_product = multiply(inverse_product, factor, order-degree)
        for q, value in enumerate(inverse_product):
            series[degree+q] += coefficient*value
    if series[0] != 1 or series[1] != 0:
        raise ArithmeticError('factored endpoint series normalization failed')
    v = series[:]
    v[0] -= 1
    power = [F(1)]+[F(0)]*order
    logarithm = [F(0)]*(order+1)
    for r in range(1, order+1):
        power = multiply(power, v, order)
        for q in range(order+1):
            logarithm[q] += F((-1)**(r+1), r)*power[q]
    rho = {j: logarithm[j]+F(1, j*3**j) for j in range(2, order+1)}
    for j, value in rho.items():
        if value != KNOWN_RHO[j]:
            raise ArithmeticError('endpoint rational coefficient mismatch at order '+str(j))
    return {
        'status': 'finite rational identities only; analytic remainders are proved in the report',
        'order': order,
        'phi_a_j': {str(j): rational_string(value) for j, value in enumerate(coordinate_coefficients(order), 1)},
        'log_density_rational_rho': {str(j): rational_string(value) for j, value in rho.items()},
        'convention': 'log(h(t)/2)=-t*log(t)/3+(1-EulerGamma-log(2))*t/3+sum_{j>=2}(rho_j-zeta(j)/(j*3**j))*t**j',
    }


def inverse_identity_check():
    """Exact symbolic reversion and reciprocal checks through the displayed orders."""
    import sympy as s
    x, tau = s.symbols('x tau')
    c = {j: s.Symbol('c'+str(j)) for j in range(2,7)}
    # u=tau+C(xu), beta=x*u.  C starts at order two, so a finite
    # number of substitutions determines every retained coefficient.
    u = tau
    for _ in range(7):
        u = s.series(tau+sum(c[j]*(x*u)**j for j in c), x, 0, 7).removeO().expand()
    beta = s.expand(x*u)
    reciprocal = s.series(1/(x*u), x, 0, 6).removeO().expand()
    residual = s.series(beta/x-sum(c[j]*beta**j for j in c)-tau, x, 0, 7).removeO().expand()
    if residual != 0:
        raise ArithmeticError('inverse residual through x**6 failed')
    expected_beta = tau*x+c[2]*tau**2*x**3+c[3]*tau**3*x**4+(2*c[2]**2*tau**3+c[4]*tau**4)*x**5
    expected_y = 1/(tau*x)-c[2]*x-c[3]*tau*x**2-(c[2]**2*tau+c[4]*tau**2)*x**3
    if s.series(beta-expected_beta, x, 0, 6).removeO() != 0:
        raise ArithmeticError('displayed beta signs and powers failed')
    if s.series(reciprocal-expected_y, x, 0, 4).removeO() != 0:
        raise ArithmeticError('displayed height signs and powers failed')
    reciprocal_residual = s.series(beta*reciprocal-1, x, 0, 7).removeO().expand()
    if reciprocal_residual != 0:
        raise ArithmeticError('reciprocal identity through x**6 failed')
    return {
        'status': 'finite symbolic identities only; no numerical or analytic error certificate',
        'conventions': {'x': '1/chi_n', 'tau': '-log(r)', 'chi_n': 'log(n)/3-K', 'beta': 'n/m'},
        'beta_through_x7': str(beta),
        'height_through_x5': str(reciprocal),
        'model_residual_through_x6': str(residual),
        'reciprocal_residual_through_x6': str(reciprocal_residual),
    }
