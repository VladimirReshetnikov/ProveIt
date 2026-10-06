"""Formal inverse checks and explicitly non-certified numerical diagnostics."""
import sympy as sp
from coefficients import r, log_coefficients


def formal_inverse_checks(coefficients):
    """Check exact log-series and branch inverse algebra, retaining parity.

    The formal branch centers use fixed parity coefficients; the optional
    numerical diagnostic separately uses the cosine interpolation. These checks
    neither compute a remainder bound nor certify any integer threshold.
    """
    degree = min(len(coefficients['0']), len(coefficients['1/2']))-1
    logs = {p: log_coefficients(c) for p, c in coefficients.items()}
    for p, ell in logs.items():
        exp_series = [sp.Integer(1)]
        for j in range(1, degree+1):
            exp_series.append(sp.factor(sum(k*ell[k]*exp_series[j-k]
                                             for k in range(1, j+1))/j))
            if sp.cancel(exp_series[j]-coefficients[p][j]) != 0:
                raise ArithmeticError('log/exponential reconstruction mismatch')
    integer = sp.symbols('m', integer=True)
    for parity in (0, 1):
        if sp.simplify(sp.cos(sp.pi*(2*integer+parity))-(-1)**parity) != 0:
            raise ArithmeticError('cosine parity selector mismatch')
    if degree >= 1 and sp.cancel(logs['0'][1]-logs['1/2'][1]) != 0:
        raise ArithmeticError('unexpected first-order parity difference')
    if degree >= 2 and sp.cancel(logs['0'][2]-logs['1/2'][2]) != 0:
        raise ArithmeticError('unexpected second-order parity difference')
    if degree >= 3 and sp.cancel(logs['1/2'][3]-logs['0'][3]-r**3/(4*(r+1))) != 0:
        raise ArithmeticError('third-order log parity difference mismatch')

    # Let z=1/t, A=log(qt), and Ah=log(t)/2-gamma_0. L=t(A-1).
    # Expand log Gamma(t+s)+(t+s)log q+log b+sum ell_j/(t+s)^j-L.
    # Generic ell_j keep the independent inverse residual small and readable.
    z, A, h = sp.symbols('z A h', nonzero=True)
    ell1, ell2, ell3 = sp.symbols('ell1 ell2 ell3')
    ell = [0, ell1, ell2, ell3]
    J = min(3, degree)
    shift = h
    corrections = []
    def residual(s):
        # log(1+s*z) is needed one order beyond the target due to 1/z.
        logpart = sum((-1)**(k+1)*(s*z)**k/sp.Integer(k) for k in range(1, J+3))
        expression = A*(s-h)+(1/z+s-sp.Rational(1, 2))*logpart-s
        expression += sp.Rational(1, 12)*z/(1+s*z)
        if J >= 3:
            expression -= sp.Rational(1, 360)*z**3/(1+s*z)**3
        for j in range(1, J+1):
            expression += ell[j]*z**j/(1+s*z)**j
        return sp.series(expression, z, 0, J+1).removeO().expand()
    for j in range(1, J+1):
        a = sp.factor(-residual(shift).coeff(z, j)/A)
        corrections.append(a)
        shift += a*z**j
    final = residual(shift)
    for j in range(J+1):
        if sp.cancel(final.coeff(z, j)) != 0:
            raise ArithmeticError('formal inverse branch residual did not vanish')
    if J >= 1:
        expected = -((h*h-h)/2+sp.Rational(1, 12)+ell1)/A
        if sp.cancel(corrections[0]-expected) != 0:
            raise ArithmeticError('elementary inverse correction mismatch')
    parity_displacement = None
    if J >= 3:
        delta = sp.symbols('Delta')
        displacement = sp.factor(corrections[2].subs(ell3, ell3+delta)-corrections[2])
        if sp.cancel(displacement+delta/A) != 0:
            raise ArithmeticError('inverse branch parity displacement mismatch')
        parity_displacement = str(-r**3/(4*(r+1)*A))
    return {
        'status': 'PASS', 'kind': 'exact formal algebra, not a threshold certificate',
        'log_series': {p: [str(v) for v in c] for p, c in logs.items()},
        'cosine_selector_at_integers': ['1', '-1'],
        'branch_convention': 'x_p=t+h+sum(a_j(p)/t**j); A=log(q*t); A*h=log(t)/2-gamma_0',
        'branch_corrections_in_log_coefficients': [str(v) for v in corrections],
        'vanishing_residual_powers': list(range(J+1)),
        'odd_minus_even_branch_a3': parity_displacement,
        'rounding_scope': 'Use parity-adjusted two-sided ceilings and a proven error radius; no radius is certified here.'
    }


def numerical_diagnostics(coefficients, exact_values, precision=80):
    """High-precision non-interval arithmetic, not a numerical proof."""
    import mpmath as mp
    if isinstance(precision, bool) or not isinstance(precision, int) or precision < 40:
        raise ValueError('precision must be an integer of at least 40 decimal digits')
    if any(n < 2 for n in exact_values):
        raise ValueError('diagnostic board sizes must be at least 2')
    J = min(3, min(len(v) for v in coefficients.values())-1)
    logs = {p: log_coefficients(c[:J+1]) for p, c in coefficients.items()}
    with mp.workdps(precision):
        saddle = mp.findroot(lambda t: t/(1-mp.exp(-t))-2, (mp.mpf(1), mp.mpf(2)))
        if not 1 < saddle < 2:
            raise ArithmeticError('positive saddle solver left (1,2)')
        q = 2/(saddle*(2-saddle))
        b = mp.exp(saddle)/(2*mp.pi*mp.sqrt(saddle*saddle-1))
        def evaluate(expression):
            return mp.mpf(str(expression.subs(r, sp.Float(str(saddle), precision)).evalf(precision)))
        cs = {p: [evaluate(v) for v in values[:J+1]] for p, values in coefficients.items()}
        ls = {p: [evaluate(v) for v in values] for p, values in logs.items()}
        def phi(t):
            out = mp.log(b)+mp.loggamma(t)+t*mp.log(q)
            for j in range(1, J+1):
                avg = (ls['0'][j]+ls['1/2'][j])/2
                osc = (ls['0'][j]-ls['1/2'][j])*mp.cos(mp.pi*t)/2
                out += (avg+osc)/t**j
            return out
        def text(value):
            return mp.nstr(value, precision)
        rows = []
        for n, value in sorted(exact_values.items()):
            parity = '1/2' if n % 2 else '0'
            log_exact = mp.log(value)
            ratio = mp.mpf(value)/(b*mp.gamma(n)*q**n)
            truncation = sum(cs[parity][j]/mp.mpf(n)**j for j in range(J+1))
            root = mp.findroot(lambda t: phi(t)-log_exact, (mp.mpf(n)-mp.mpf('.1'), mp.mpf(n)+mp.mpf('.1')))
            root_residual = phi(root)-log_exact
            if abs(root_residual) > mp.power(10, -precision+20)*max(1, abs(log_exact)):
                raise ArithmeticError('numerical inverse solver residual is too large')
            rows.append({'n': n, 'parity': n%2,
                'normalized_ratio': text(ratio),
                'n_power_scaled_asymptotic_residual': text((ratio-truncation)*mp.mpf(n)**(J+1)),
                'n_power_scaled_log_residual': text((log_exact-phi(n))*mp.mpf(n)**(J+1)),
                'cosine_inverse_root': text(root),
                'inverse_root_minus_n': text(root-n),
                'scaled_inverse_root_minus_n': text((root-n)*mp.mpf(n)**(J+1)*mp.log(q*n)),
                'solver_log_residual': text(root_residual)})
        return {'status': 'COMPUTED', 'certified': False, 'decimal_digits': precision,
                'order': J, 'r': text(saddle), 'q': text(q), 'b': text(b),
                'interpretation': 'Diagnostics only. No rigorous interval, remainder constant, onset, or rounding guarantee.',
                'rows': rows}
