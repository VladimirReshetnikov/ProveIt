"""Finite moment, remainder and continuous inverse diagnostics only."""
from math import comb
import mpmath as mp
from common import require


def run(counts, algebra):
    c, g = [list(map(int, counts[name])) for name in ('connected', 'all')]
    nmax = counts['terms']
    with mp.workdps(100):
        tau, nu, rho = [mp.mpf(algebra['constants'][key]) for key in ('tau', 'nu', 'rho')]
        a = mp.mpf(algebra['decimal_component_constants']['first_moment_correction'])
        moments = [sum(comb(n, j)*c[j]*g[n-j] for j in range(1, n+1)) for n in range(nmax+1)]
        moment_output = []
        for n in sorted(set(k for k in (30, 50, 100, 200, nmax) if k <= nmax)):
            mean = mp.mpf(moments[n])/g[n]
            f2 = mp.mpf(sum(comb(n, j)*c[j]*moments[n-j] for j in range(1, n+1)))/g[n]
            variance = f2+mean-mean**2
            require(1 <= mean <= n and variance >= 0, 'Invalid finite component moments')
            moment_output.append({'n': n, 'mean': str(mean), 'variance': str(variance),
                                  'scaled_mean_second': str(n*n*(mean-1-nu-a/n)),
                                  'scaled_variance_second': str(n*n*(variance-nu-a/n))})
        inverse_output, remainder_output = [], []
        for name, v in [('connected', '0'), ('all', '1')]:
            values = c if name == 'connected' else g
            A = mp.mpf(algebra['constants']['connected_A' if v == '0' else 'all_A'])
            coefficients = list(map(mp.mpf, algebra['decimal_coefficients_at_v'][v]))
            ell = list(map(mp.mpf, algebra['decimal_log_stirling_coefficients'][v]))
            for n in sorted(set(k for k in (30, 60, 100, 200, nmax) if 20 <= k <= nmax)):
                target = mp.log(values[n])
                x0 = target/mp.lambertw(target/(mp.e*rho))
                model = lambda x: x*(mp.log(x/rho)-1)-2*mp.log(x)+mp.log(A*mp.sqrt(2*mp.pi))+sum(ell[j-1]/x**j for j in range(1, 5))
                root = mp.findroot(lambda x: model(x)-target, (x0, x0+3))
                require(abs(model(root)-target) < mp.mpf('1e-85'), 'Continuous inverse root residual failed')
                require(values[n-1] < values[n], 'Exact threshold not strictly increasing')
                inverse_output.append({'sequence': name, 'target_exact_index': n, 'lambert_base': str(x0),
                                       'model_root': str(root), 'root_minus_n': str(root-n),
                                       'scaled_by_n5_log_n': str((root-n)*n**5*mp.log(n)),
                                       'naive_ceiling': int(mp.ceil(root)), 'exact_inverse': n,
                                       'model_equation_residual': str(abs(model(root)-target))})
                leading = A*mp.factorial(n)*rho**(-n)*mp.mpf(n)**(-mp.mpf(5)/2)
                ratio = mp.mpf(values[n])/leading
                remainder_output.append({'sequence': name, 'n': n, 'normalized_exact_count': str(ratio),
                                         'next_order_scaled_remainders_J0_through_J3': [str(n**(j+1)*(ratio-sum(coefficients[k]/mp.mpf(n)**k for k in range(j+1)))) for j in range(4)]})
        return {'status': 'DIAGNOSTICS ONLY: finite values do not prove convergence, certify an asymptotic remainder constant or establish any finite-input inverse bracket',
                'moment_diagnostics': moment_output, 'inverse_diagnostics': inverse_output, 'remainder_diagnostics': remainder_output,
                'failure_predicates': ['Finite moments lie in their elementary range', 'Continuous-root equation residual below 1e-85', 'Exact threshold counts strictly increasing at sampled indices'],
                'not_tested_or_certified': ['eventual convergence', 'a numerical remainder constant', 'a finite-n threshold', 'a rigorous decimal interval', 'a finite-input integer inverse enclosure']}
