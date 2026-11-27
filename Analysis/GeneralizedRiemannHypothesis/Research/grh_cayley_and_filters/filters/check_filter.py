"""Exact all-ranks coefficient check and a high-precision three-frequency example.

Requires Python 3, SymPy and mpmath. Run python check_filter.py.
"""
import sympy as sp
import mpmath as mp


def euler_step(coefficients, slope, offset, rank):
    """Apply slope*z*d/dz+offset in the basis (z-1)^(rank-r)."""
    result = {}
    for r, value in coefficients.items():
        degree = rank - r
        result[r] = result.get(r, 0) + (slope * degree + offset) * value
        result[r + 1] = result.get(r + 1, 0) + slope * degree * value
    return {r: sp.factor(value) for r, value in result.items()}


def check_symbolic():
    n, y = sp.symbols("n y")
    coefficients = {0: sp.Integer(1)}
    denominator = 4 * (n * (n - 1) * (n - 2)) ** 2
    for _ in range(2):
        for slope, offset in [(1, 0), (-1, n), (2, -n)]:
            coefficients = euler_step(coefficients, slope, offset, n)
    harmonic_sum = sp.factor(sum(
        (-1)**r * sp.harmonic(r - 1) * coefficients[r] / denominator
        for r in range(1, 7)
    ))
    assert sp.factor(harmonic_sum + (n + 1)*(n + 2)/(120*(n - 1)*(n - 2))) == 0
    ratio = sp.series(y / sp.log(1 + y), y, 0, 5).removeO()
    term = -ratio**3 * (2 + y)**2 / 4 + ratio**2 * (1 + y) * (2 + y) / 2
    polynomial = sp.series(term, y, 0, 5).removeO()
    assert sp.expand(polynomial + y**2/6 + y**3/4 + 11*y**4/120) == 0
    constant = sp.factor(polynomial.subs(y, -1) - harmonic_sum)
    assert sp.factor(constant - n/(20*(n - 1)*(n - 2))) == 0
    print("Exact coefficient divided by pi^5 =", constant)


def check_variance_integrals():
    p, n = sp.symbols("p n")
    m3 = p*(1-p)*(2*p-1)/2
    m5 = p*(p-1)*(2*p-1)*(12*p*p-12*p+1)/24

    def integrated_variance(mean, rank, degree):
        return sp.factor(sum(
            sp.integrate((p*(1-p))**(r-1) * sp.diff(mean, p, r)**2,
                         (p, 0, 1)) / (sp.factorial(r)*sp.ff(rank, r))
            for r in range(1, degree+1)
        ))

    assert sp.factor(integrated_variance(m3, n, 3)-n/(20*(n-1)*(n-2))) == 0
    assert integrated_variance(m5, 5, 5) == sp.Rational(25, 6912)
    print("Variance integral for rank 5, coordinate 5, divided by pi^9 = 25/6912")


def test_four_atom_solution():
    """Solve independently for symmetric atoms at +/-inner and +/-outer."""
    mp.mp.dps = 90
    predicted = 3 * mp.pi**5 / 40
    print("Three frequencies (1-2t, 1-t, 1+3t)")
    print("t        (B-3pi)/(36 t^6)      ratio to prediction")
    for denominator in (20, 40, 80, 160, 320):
        t = mp.mpf(1) / denominator
        frequencies = [1-2*t, 1-t, 1+3*t]

        def constraints(outer, inner, p):
            return tuple(
                p*mp.cos(outer*w) + (1-p)*mp.cos(inner*w)
                for w in frequencies
            )
        solution = mp.findroot(
            constraints, (3*mp.pi/2, mp.pi/2, mp.mpf(1)/4),
            tol=mp.mpf('1e-75'),
        )
        outer, inner, p = solution
        assert outer > inner > 0 and 0 < p < 1
        assert max(abs(v) for v in constraints(outer, inner, p)) < mp.mpf('1e-65')
        observed = (2*outer - 3*mp.pi) / (36*t**6)
        print("1/"+str(denominator), mp.nstr(observed, 15), mp.nstr(observed / predicted, 15))
    assert abs(observed / predicted - 1) < mp.mpf('0.001')


if __name__ == "__main__":
    check_symbolic()
    check_variance_integrals()
    test_four_atom_solution()
