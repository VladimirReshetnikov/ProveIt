"""Direct local-subtraction diagnostics for the mixed Hurwitz product theorem."""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 85
records = []
for k, ell in ((2, 2), (3, 3), (2, 3), (2, 4)):
    coeff = {m: [(-1) ** j * mp.rf(m, j) * mp.zeta(m + j) / mp.factorial(j)
                 for j in range(110)] for m in {k, ell}}

    def ratio(m, r, x):
        if x < mp.mpf('0.125'):
            return mp.polyval(list(reversed(coeff[m][r:])), x)
        return (mp.zeta(m, 1 + x) - mp.polyval(list(reversed(coeff[m][:r])), x)) / x ** r

    def regular(x):
        return mp.zeta(k, 1 + x) * mp.zeta(ell, 1 + x) + ratio(ell, k, x) + ratio(k, ell, x)

    constant = -mp.mpf(1) / (k + ell - 1)
    constant += sum(coeff[ell][j] / (j - k + 1) for j in range(k - 1))
    constant += sum(coeff[k][j] / (j - ell + 1) for j in range(ell - 1))
    value = constant + mp.quad(regular, [0, mp.mpf('0.125'), mp.mpf('0.5'), 1])
    C = mp.binomial(k + ell - 2, k - 1)
    if (k - ell) % 2 == 0:
        target = (-1) ** k * C * ((2 * mp.harmonic(k + ell - 2) - mp.harmonic(k - 1)
                                  - mp.harmonic(ell - 1)) * mp.zeta(k + ell - 1)
                                  + 2 * mp.diff(mp.zeta, k + ell - 1))
    else:
        target = (-1) ** k * C * (mp.harmonic(ell - 1) - mp.harmonic(k - 1)) * mp.zeta(k + ell - 1)
    residual = abs(value - target)
    assert residual < mp.mpf('1e-75')
    records.append({'k': k, 'l': ell, 'coordinate_finite_part': mp.nstr(value, 80),
                    'closed_form': mp.nstr(target, 80), 'absolute_residual': mp.nstr(residual, 12),
                    'working_dps': mp.mp.dps, 'local_taylor_terms': 110})

# A genuinely different order-derivative test.  The logarithmic local
# terms are removed in the original coordinate before quadrature.
k = 2
c = [(-1) ** j * mp.rf(k, j) * mp.zeta(k + j) / mp.factorial(j)
     for j in range(115)]
d = [(-1) ** j * mp.rf(k, j) / mp.factorial(j)
     * ((mp.digamma(k + j) - mp.digamma(k)) * mp.zeta(k + j)
        + mp.zeta(k + j, derivative=1)) for j in range(115)]


def derivative_regular(x):
    if x == 0:
        return mp.zeta(k) * mp.zeta(k, derivative=1) + d[k]
    g = mp.zeta(k, 1 + x)
    h = mp.zeta(k, 1 + x, derivative=1)
    if x < mp.mpf('0.125'):
        dc_tail = mp.polyval(list(reversed(d[k:])), x)
        c_tail_minus_constant = x * mp.polyval(list(reversed(c[k + 1:])), x)
    else:
        dc_tail = (h - mp.polyval(list(reversed(d[:k])), x)) / x ** k
        c_tail_minus_constant = (g - mp.polyval(list(reversed(c[:k])), x)) / x ** k - c[k]
    return g * h + dc_tail - mp.log(x) * c_tail_minus_constant


local = mp.mpf(1) / (2 * k - 1) ** 2
local += sum(d[j] / (j - k + 1) + c[j] / (j - k + 1) ** 2
             for j in range(k - 1))
# The smooth quadrature removed -c[k]*log(x), whose ordinary integral is c[k].
derivative_value = local + c[k] + mp.quad(derivative_regular,
                                          [0, mp.mpf('0.125'), mp.mpf('0.5'), 1])
derivative_target = ((4 * mp.zeta(2) - 2) * mp.zeta(3)
                     + 3 * mp.zeta(3, derivative=1) + 3 * mp.zeta(3, derivative=2))
derivative_residual = abs(derivative_value - derivative_target)
assert derivative_residual < mp.mpf('1e-75')
derivative_record = {'k': k, 'spectral_derivative_orders': [0, 1],
                     'coordinate_finite_part': mp.nstr(derivative_value, 80),
                     'closed_form': mp.nstr(derivative_target, 80),
                     'absolute_residual': mp.nstr(derivative_residual, 12),
                     'working_dps': mp.mp.dps, 'local_taylor_terms': 115,
                     'method': 'Independent local subtraction of power-log terms followed by smooth quadrature.'}

out = Path(__file__).resolve().parents[1] / 'verification/hurwitz_products.json'
data = {'status': 'passed', 'diagnostics': records,
        'order_derivative_diagnostics': [derivative_record],
        'qualification': 'Floating-point local-subtraction quadrature, not interval enclosure.'}
out.write_text(json.dumps(data, indent=2) + '\n')
print(json.dumps(data, indent=2))
