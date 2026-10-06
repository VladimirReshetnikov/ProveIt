"""Optional generic coefficient engine. Requires SymPy; never fits table values.

The requested order is finite but otherwise unrestricted. Expression swell
increases quickly with order; --order 3 is the tested inexpensive setting.
"""
import argparse
import json
from functools import lru_cache


def derive(order):
    try:
        import sympy as s
    except ImportError as error:
        raise RuntimeError("This optional check needs SymPy; install it in your chosen environment") from error
    if order < 1:
        raise ValueError("order must be positive")
    u, q, k, e = s.symbols("u q k e")
    left = s.symbols(f"l1:{order + 1}")
    right = s.symbols(f"r1:{order + 1}")
    degree = order + 1

    def mul(a, b, limit=degree):
        return [s.expand(sum(a[j] * b[i-j] for j in range(i+1))) for i in range(limit+1)]

    def inverse(a, limit=degree):
        if a[0] != 1:
            raise RuntimeError("Formal reciprocal requires constant coefficient 1")
        out = [s.Integer(1)]
        for i in range(1, limit+1):
            out.append(s.expand(-sum(a[j] * out[i-j] for j in range(1, i+1))))
        return out

    def branch(runs):
        g = [s.Integer(1)] + [s.Integer(0)] * degree
        for run in reversed(runs):
            denominator = [s.Integer(1), -run] + [-g[j-1] for j in range(2, degree+1)]
            g = inverse(denominator)
        return g

    gl, gr = branch(left), branch(right)
    moments = [s.expand(gl[j] + gr[j]) for j in range(1, order+1)]
    # Recursively solve y=1+(1-k)u+sum B_j*u^(j+1)*y^(-j).
    y = [s.Integer(1), 1-k] + [s.Integer(0)] * (degree-1)
    for r in range(2, degree+1):
        inv_y = inverse(y)
        inv_power = [s.Integer(1)] + [s.Integer(0)] * degree
        value = 0
        for j in range(1, min(order, r-1)+1):
            inv_power = mul(inv_power, inv_y)
            value += moments[j-1] * inv_power[r-j-1]
        y[r] = s.expand(value)
    # (log y)' = y'/y; divide by u and remove its constant 1-k.
    derivative = [(i+1)*y[i+1] for i in range(degree)] + [s.Integer(0)]
    log_derivative = mul(derivative, inverse(y))
    exponent = [s.Integer(0)] + [s.expand(log_derivative[j] / (j+1)) for j in range(1, order+1)]
    # If P=exp(E), then j P_j=sum_{i=1}^j i E_i P_(j-i).
    polynomials = [s.Integer(1)]
    for j in range(1, order+1):
        polynomials.append(s.expand(sum(i*exponent[i]*polynomials[j-i] for i in range(1,j+1))/j))
    f = (1-q)/(1-2*q)

    @lru_cache(None)
    def h(j):
        return q/(1-q) if j == 0 else s.cancel(q*s.diff(h(j-1), q))

    @lru_cache(None)
    def side(exponents):
        last = max([i+1 for i, value in enumerate(exponents) if value] + [0])
        out = f
        for power in exponents[:last]:
            out *= h(power)
        return s.cancel(out)

    @lru_cache(None)
    def moment(exponents):
        out = side(exponents[1:order+1]) * side(exponents[order+1:])
        for _ in range(exponents[0]):
            out = s.cancel(q*s.diff(out, q))
        return out

    from coefficient_certificates import CLAIMED, correction_polynomials
    explicit = correction_polynomials()
    results = []
    for j, polynomial in enumerate(polynomials):
        poly = s.Poly(polynomial, k, *left, *right)
        total = sum(coefficient*moment(exponents) for exponents, coefficient in poly.terms())
        coefficient = s.factor(s.cancel(total/f**2))
        checked = j <= 3
        if checked:
            expected = CLAIMED[j]
            claimed = sum(s.Rational(c.numerator, c.denominator)*q**i for i, c in enumerate(expected.p))
            claimed /= (1-q)**expected.a * (1-2*q)**expected.b
            if s.cancel(coefficient-claimed) != 0:
                raise RuntimeError(f"Generic derivation disagrees with c{j}")
            # Independently compare the pre-summation boundary polynomial.
            # Pad missing variables when order < 3; unused deeper variables vanish.
            old_variables = [k] + list(left) + [s.Integer(0)]*max(0,3-order)
            old_variables = old_variables[:4] + list(right) + [s.Integer(0)]*max(0,3-order)
            old_variables = old_variables[:7]
            expected_poly = sum(s.Rational(c.numerator,c.denominator)*s.prod(v**p for v,p in zip(old_variables, exps))
                                for exps,c in explicit[j].terms.items())
            if s.expand(polynomial-expected_poly) != 0:
                raise RuntimeError(f"Generic boundary polynomial P{j} mismatch")
        results.append({"order":j, "monomials":len(poly.terms()), "coefficient_q":str(coefficient),
                        "coefficient_e":str(s.factor(coefficient.subs(q,1/e))),
                        "decimal_50_digits":str(coefficient.subs(q,s.exp(-1)).evalf(50)),
                        "checked_against_displayed_formula":checked})
    return {"requested_order":order,"sympy_version":s.__version__,"coefficients":results}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--order", type=int, default=3)
    args = parser.parse_args()
    print(json.dumps(derive(args.order), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
