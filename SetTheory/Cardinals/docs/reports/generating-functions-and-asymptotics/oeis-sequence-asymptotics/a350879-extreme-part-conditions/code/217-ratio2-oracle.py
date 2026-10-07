"""Independent exact checks: Eulerian derivatives and product exponential.

The oracle shares only the Q5 arithmetic and elementary polynomial operations
with exact.py. It does not call its derivative, Bernoulli, exponent, radial,
Gaussian-moment, or partition-count routines.
"""
from fractions import Fraction
from math import comb, factorial
from exact import Q5, ZERO, ONE, natural, polynomial_add, polynomial_multiply, polynomial_scale


def eulerian_derivative(z, m):
    natural(m, 'derivative order')
    if m == 0:
        raise ValueError('the logarithmic zeroth derivative is not algebraic')
    row = [1]
    for n in range(1, m):
        row = [(k+1)*(row[k] if k < len(row) else 0)
               +(n-k)*(row[k-1] if k else 0) for k in range(n)]
    polynomial = sum((coefficient*z**i for i, coefficient in enumerate(row)), ZERO)
    return (-1)**m * z * polynomial / (1-z)**m


def bernoulli_number(n):
    natural(n)
    return sum((Fraction(sum((-1)**j*comb(k, j)*j**n for j in range(k+1)), k+1)
                for k in range(n+1)), Fraction(0))


def radial_oracle(order):
    natural(order)
    nmax = 2*order
    rho = Q5(Fraction(-1, 2), Fraction(1, 2))
    curvature = Q5(Fraction(-5, 2), Fraction(3, 2))
    exponent = [{} for _ in range(nmax+1)]
    def add(degree, ypower, value):
        exponent[degree] = polynomial_add(exponent[degree], {ypower: value})
    for d in range(1, nmax+1):
        m = d+2
        h = 2**m*eulerian_derivative(rho**2, m-1)-eulerian_derivative(rho, m-1)
        add(d, m, h/factorial(m))
        ell = (eulerian_derivative(rho, d)+2**d*eulerian_derivative(rho**2, d))/2
        add(d, d, (ell-(3 if d == 1 else 0))/factorial(d))
        for r in range(1, (d+2)//4+1):
            m = d-(4*r-2)
            derivative = 2**m*eulerian_derivative(rho**2, 2*r-1+m)-eulerian_derivative(rho, 2*r-1+m)
            add(d, m, derivative*bernoulli_number(2*r)/factorial(2*r)/factorial(m))
    # Form the product over d of exp(E_d(Y)*s^d), using its factorial series.
    result = [{0: ONE}]+[{} for _ in range(nmax)]
    for d in range(1, nmax+1):
        powers = [{0: ONE}]
        for m in range(1, nmax//d+1):
            powers.append(polynomial_scale(polynomial_multiply(powers[-1], exponent[d]), Fraction(1, m)))
        new = [{} for _ in range(nmax+1)]
        for j in range(nmax+1):
            for m, factor in enumerate(powers):
                if j+d*m > nmax:
                    break
                new[j+d*m] = polynomial_add(new[j+d*m], polynomial_multiply(result[j], factor))
        result = new
    coefficients = []
    for j in range(order+1):
        value = ZERO
        for power, coefficient in result[2*j].items():
            if power % 2 == 0:
                half = power//2
                moment = Fraction(factorial(2*half), 2**half*factorial(half))/curvature**half
                value += coefficient*moment
        coefficients.append(value)
    return coefficients


def direct_finite_products(max_n):
    """Independent coin-change DP, recomputed from scratch for each k."""
    natural(max_n, 'max_n')
    counts = [0]*(max_n+1)
    for k in range(1, max_n//3+1):
        bound = max_n-3*k
        product = [1]+[0]*bound
        for part in range(k, 2*k+1):
            for j in range(part, bound+1):
                product[j] += product[j-part]
        for j, coefficient in enumerate(product):
            counts[j+3*k] += coefficient
    return counts


def enumerate_partitions(max_n):
    """Enumerate integer partitions directly; use only for small max_n."""
    natural(max_n, 'max_n')
    counts = [0]*(max_n+1)
    def visit(remaining, minimum, first, last, total):
        if remaining == 0:
            if first and last == 2*first:
                counts[total] += 1
            return
        for part in range(minimum, remaining+1):
            visit(remaining-part, part, first or part, part, total)
    for n in range(max_n+1):
        visit(n, 1, 0, 0, n)
    return counts
