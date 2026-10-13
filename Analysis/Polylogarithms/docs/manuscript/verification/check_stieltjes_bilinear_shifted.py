"""Exact coefficient checks and noninterval bilinear quadrature diagnostics.

Run from any working directory.  All outputs remain beside this script.
The mathematical proof is in bilinear-findings.tex; numerical agreement
alone is not used to prove an identity or certify an error bound.
"""
import json
import pathlib
import mpmath as mp
import sympy as sp

mp.mp.dps = 40
tolerance = mp.mpf('1e-30')
T = sp.symbols('T')
zeta_symbols = {n: sp.Symbol('Z' + str(n)) for n in range(2, 10)}


def polynomial(m):
    return sp.Poly(sp.prod(T-r for r in range(2, m)) / sp.factorial(m-2), T)


coefficient_checks = []
for m in range(2, 9):
    R = polynomial(m)
    sample_checks = [R.eval(ell) == sp.binomial(ell-2, m-2)
                     for ell in range(2, m+3)]
    assert all(sample_checks)
    coefficient_checks.append({
        'm': m, 'R_m': str(R.as_expr()),
        'coefficients_in_ascending_order': [str(R.nth(j)) for j in range(m-1)],
        'binomial_samples_exact': all(sample_checks),
        'sample_ell_start': 2, 'sample_ell_end': m+2,
    })


integer_checks = []
for N, m, astr in [(1, 2, '1.25'), (2, 2, '0.75'), (2, 3, '1.25'),
                  (3, 4, '0.75'), (5, 3, '1.25'), (6, 7, '1.25')]:
    a = mp.mpf(astr)
    # Stable elementary x-integrand, independently of the t-space proof.
    f = lambda x: x**(m-1) * (-mp.log1p(a/x))**N / (x+a)**2
    direct = mp.quad(lambda t: 4*t**3*f(t**4), [0, 1]) + mp.quad(f, [1, 4, 16, mp.inf])
    R = polynomial(m)
    explicit = (-1)**N * mp.factorial(N) * a**(m-2) * sum(
        mp.mpf(str(R.nth(j).p))/int(R.nth(j).q)*(mp.zeta(N+1-j)-1)
        for j in range(m-1))
    formal = sp.factor((-1)**N * sp.factorial(N) * sum(
        R.nth(j) * (zeta_symbols[N+1-j]-1) for j in range(m-1)))
    row = {'N': N, 'm': m, 'a': astr,
           'exact_formula_after_dividing_by_a_power_m_minus_2': str(formal),
           'direct': mp.nstr(direct, 36), 'finite_zeta_formula': mp.nstr(explicit, 36),
           'absolute_error': mp.nstr(abs(direct-explicit), 8),
           'diagnostic_pass': bool(abs(direct-explicit) < tolerance)}
    print(row, flush=True)
    integer_checks.append(row)


def K(v, u, w, a, b):
    return (a**(v+w-1)/b**(1+w) * mp.beta(v+u+w, 2-v)
            * mp.hyp2f1(1+w, v+u+w, 2+u+w, 1-a/b))


hypergeometric_checks = []
for p, q, vs, astr, bstr in [(0, 0, '1', '1', '2'),
                            (1, 0, '1.25', '0.75', '1.25'),
                            (1, 1, '2.5', '0.75', '1.25')]:
    v, a, b = map(mp.mpf, (vs, astr, bstr))
    f = lambda x: (x**(v-1) * (-mp.log1p(a/x))**p * (-mp.log1p(b/x))**q
                   / ((x+a)*(x+b)))
    direct = mp.quad(lambda t: 4*t**3*f(t**4), [0, 1]) + mp.quad(f, [1, 4, 16, mp.inf])
    explicit = mp.diff(lambda u: mp.diff(lambda w: K(v, u, w, a, b), 0, q), 0, p)
    row = {'p': p, 'q': q, 'v': vs, 'a': astr, 'b': bstr,
           'direct': mp.nstr(direct, 36), 'hypergeometric': mp.nstr(explicit, 36),
           'absolute_error': mp.nstr(abs(direct-explicit), 8),
           'diagnostic_pass': bool(abs(direct-explicit) < tolerance),
           'uses_continuation_beyond_initial_generator_strip': bool(v >= 2)}
    print(row, flush=True)
    hypergeometric_checks.append(row)


# Independent exact check of the finite Laguerre Gram identities.
laguerre_checks = []
for m in range(7):
    for n in range(m, 7):
        product = sp.Poly(sp.laguerre(m, T) * sp.laguerre(n, T), T)
        integral = sum(product.nth(j)*sp.factorial(j) for j in range(product.degree()+1))
        assert integral == int(m == n)
        laguerre_checks.append({'m': m, 'n': n, 'exact_integral': str(integral), 'pass': True})


passed = all(row['diagnostic_pass'] for row in integer_checks+hypergeometric_checks)
payload = {
    'status': 'PASS' if passed else 'FAIL',
    'diagnostic_absolute_tolerance': str(tolerance),
    'precision': mp.mp.dps,
    'evidence_kind': 'exact finite rational identities and noninterval numerical diagnostics',
    'coefficient_checks': coefficient_checks,
    'integer_weight_checks': integer_checks,
    'hypergeometric_checks': hypergeometric_checks,
    'laguerre_orthogonality_checks': laguerre_checks,
}
pathlib.Path(__file__).with_suffix('.json').write_text(json.dumps(payload, indent=2)+'\n')
if not passed:
    raise SystemExit('FAIL: at least one numerical diagnostic exceeded tolerance')
print('PASS: 9 noninterval diagnostics, 7 exact coefficient polynomials, 28 exact Laguerre products', flush=True)
