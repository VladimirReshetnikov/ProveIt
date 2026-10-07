#!/usr/bin/env python3
"""Multiprecision finite diagnostics, deliberately separate from exact arithmetic."""
from __future__ import annotations
import bisect
from collections import defaultdict
import re
import sys
sys.dont_write_bytecode = True
import mpmath as mp
from check import CheckError, exact_keys, moments, require, weight, a_term

WARNING = 'Numerical finite diagnostics only; not asymptotic proofs, validated enclosures, effective onsets, or new general-p absolute coefficients'


def mp_rational(value):
    return mp.mpf(value.numerator)/value.denominator


def transfer_mp(weights, nmax):
    state = [mp.mpf(0)]*(nmax+1)
    state[0] = mp.mpf(1)
    out = [state[0]]
    for step in range(1, 2*nmax+1):
        nxt = [mp.mpf(0)]*(nmax+1)
        for h in range(step % 2, min(step, nmax)+1, 2):
            nxt[h] = (state[h-1] if h else 0)+(weights[h+1]*state[h+1] if h < nmax else 0)
        state = nxt
        if step % 2 == 0: out.append(state[0])
    return out


def I(p):
    p = mp.mpf(p)
    return mp.beta(1/p, mp.mpf('.5'))/p


def J(p, q=2):
    p, q = mp.mpf(p), mp.mpf(q)
    require(p > 0 and 1 < q < p+1, 'Coefficient outside bulk hypotheses')
    return I(p)**(q-1)*(q-1-p/2)/(p*(q-1))*mp.beta(1-(q-1)/p, mp.mpf('.5'))


def logF(p, n):
    p = mp.mpf(p)
    return mp.log(mp.sqrt(2*p/mp.pi)*I(p)**(-p/2))+n*mp.log(4/I(p)**p)+p*mp.loggamma(n+1)-mp.log(n)/2


def interpolate(values, x):
    n = int(mp.floor(x))
    require(0 <= n < len(values)-1, 'Interpolation outside computed range')
    return values[n]+(x-n)*(values[n+1]-values[n])


def inverse(values, target):
    # These examples have a strictly increasing tail starting at index 1.
    # The normalized bulk examples can decrease from index 0 to index 1.
    require(len(values) >= 3 and all(values[j] < values[j+1] for j in range(1,len(values)-1)), 'Inverse requires a strictly increasing tail')
    require(target > values[0] and values[1] <= target <= values[-1], 'Inverse target outside the tail or below the early prefix')
    j = bisect.bisect_right(values, target, lo=1)-1
    if values[j] == target: return mp.mpf(j)
    require(j < len(values)-1 and values[j+1] > values[j], 'Inverse needs a positive slope')
    return mp.mpf(j)+(target-values[j])/(values[j+1]-values[j])


def occupation_mp(weights, n):
    # Directed transfer: forward from 0; backward to 0 in the remaining length.
    forward = [[mp.mpf(0)]*(n+1) for _ in range(2*n+1)]
    back = [[mp.mpf(0)]*(n+1) for _ in range(2*n+1)]
    forward[0][0] = back[0][0] = mp.mpf(1)
    for t in range(1, 2*n+1):
        for h in range(t % 2, min(t, n)+1, 2):
            forward[t][h] = (forward[t-1][h-1] if h else 0)+(weights[h+1]*forward[t-1][h+1] if h < n else 0)
            back[t][h] = (weights[h]*back[t-1][h-1] if h else 0)+(back[t-1][h+1] if h < n else 0)
    z = forward[-1][0]
    return [mp.mpf(0)]+[mp.fsum(forward[t][h]*weights[h]*back[2*n-1-t][h-1]
                                       for t in range(2*n))/z for h in range(1, n+1)]


def diagnostic_results(nmax=256, dps=90):
    require(type(nmax) is int and 64 <= nmax <= 512, 'Diagnostic maximum must lie in 64..512')
    require(type(dps) is int and dps == 90, 'Release diagnostics use exactly 90 decimal digits')
    require(mp.__version__ == '1.3.0', 'Use pinned mpmath 1.3.0 for byte-identical diagnostics')
    with mp.workdps(dps):
        return _diagnostic_results(nmax, dps)


def _diagnostic_results(nmax, dps):
    counts = defaultdict(int)
    def check(condition, category):
        require(condition, 'Numerical predicate failed: '+category)
        counts[category] += 1
    def text(x):
        require(mp.isfinite(x), 'Nonfinite numerical output')
        return mp.nstr(x, 40)
    ns = sorted(set(n for n in (16, 32, 64, 128, 256, nmax) if n <= nmax))
    bases = {p: moments([h**p for h in range(nmax+1)], nmax) for p in range(1, 7)}
    regularization = []
    for ps, qs in (('0.5','1.2'), ('0.5','1.25'), ('0.5','1.4'), ('1','1.5'),
                   ('1.5','2'), ('2','2'), ('3','2'), ('3','3'), ('4','2')):
        p, q = mp.mpf(ps), mp.mpf(qs)
        H = 1/I(p)
        epsilon = H*mp.mpf('.00001')
        upper = mp.sqrt(1-(epsilon/H)**p)
        finite = H**(1-q)*(2/p)*mp.quad(lambda t: (1-t*t)**((1-q)/p-1), [0, upper])-epsilon**(1-q)/(q-1)
        z = (epsilon/H)**p
        bound = H**(-p)*epsilon**(p-q+1)/((p-q+1)*mp.sqrt(1-z)*(1+mp.sqrt(1-z)))
        check(abs(J(p,q)-finite) <= bound*mp.mpf('1.00000000001'), 'finite_regularization_bound_numeric')
        regularization.append({'p': ps, 'q': qs, 'J': text(J(p,q)), 'finite_cutoff_error': text(J(p,q)-finite),
                               'analytic_cutoff_bound_evaluated_numerically': text(bound)})
    check(J(2) == 0, 'numerical_quadratic_cancellation')
    check(abs(J(4)+mp.pi/4) < mp.mpf('1e-85'), 'numerical_quartic_constant')
    bulk, endpoint, critical, cumulative, polynomial = [], [], [], [], []
    bulk_logs, endpoint_logs, critical_logs = {}, {}, {}
    products = {}
    for p in range(2, 7):
        changed = moments([0]+[h**(p-2)*(4*h*h-1) for h in range(1, nmax+1)], nmax)
        logs = [mp.log(x)-n*mp.log(4) for n, x in enumerate(changed)]
        bulk_logs[p] = logs
        target = -J(p)/4
        bulk.append({'p': p, 'q': '2', 'b': '-1/4', 'P': text(2/mp.pi), 'target': text(target),
                     'rows': [{'n': n, 'scaled_log_ratio': text(n*(logs[n]-mp.log(bases[p][n])-mp.log(2/mp.pi)))} for n in ns]})
    for p in range(1, 6):
        weights = [h**p for h in range(nmax+1)]
        weights[1] = 2
        changed = moments(weights, nmax)
        logs = [mp.log(x) for x in changed]
        endpoint_logs[p] = logs
        endpoint.append({'p': p, 'P': '2', 'weight_change': 'lambda_1: 1 -> 2', 'target': text(2/(4/I(p)**p)),
                         'rows': [{'n': n, 'scaled_log_ratio': text(n**p*(logs[n]-mp.log(bases[p][n])-mp.log(2)))} for n in ns]})
    for p in range(1, 4):
        k = p+1
        changed = transfer_mp([mp.mpf(0)]+[mp.mpf(h)**p+mp.mpf(1)/h for h in range(1, nmax+1)], nmax)
        # Infinite product via finite logarithmic product plus a rapidly convergent zeta tail.
        M = 16
        logP = mp.fsum(mp.log1p(mp.mpf(h)**(-k)) for h in range(1, M+1))
        logP += mp.fsum((-1)**(j+1)*mp.zeta(k*j, M+1)/j for j in range(1, 121))
        roots = [-mp.exp(mp.j*mp.pi*(2*j+1)/k) for j in range(k)]
        gammaP = 1/mp.fprod(mp.gamma(1+c) for c in roots)
        check(abs(mp.log(gammaP)-logP) < mp.mpf('1e-80'), 'numerical_independent_product_routes')
        products[p] = logP
        critical_logs[p] = [mp.log(x) for x in changed]
        critical.append({'p': p, 'q': str(k), 'b': '1', 'P': text(mp.exp(logP)), 'target': text(2/(4/I(p)**p)),
                         'rows': [{'n': n, 'scaled_log_ratio': text(n**p*(critical_logs[p][n]-mp.log(bases[p][n])-logP)/mp.log(n))} for n in ns]})
    for p in (2, 3, 4, 5):
        weights = [mp.mpf(0)]+[mp.mpf(h)**p*mp_rational(a_term(h)/a_term(h-1)) for h in range(1, nmax+1)]
        changed = transfer_mp(weights, nmax)
        cumulative.append({'p': p, 'S': '0', 'A': '1/3', 'P': '1', 'target': text(-J(p)/3),
                           'rows': [{'n': n, 'scaled_log_ratio': text(n*(mp.log(changed[n])-mp.log(bases[p][n])))} for n in ns]})
    models = [('quadratic_h2_plus_1', 2, lambda h:h*h+1, 1, mp.sinh(mp.pi)/mp.pi, -mp.mpf(1)/8),
              ('quadratic_4h2_minus_1', 2, lambda h:4*h*h-1, 4, 2/mp.pi, -mp.mpf(1)/8),
              ('quartic_comparison', 4, lambda h:h*h*(4*h*h-1), 4, 2/mp.pi, -mp.mpf(1)/16),
              ('quartic_h2_plus_1_squared', 4, lambda h:(h*h+1)**2, 1, (mp.sinh(mp.pi)/mp.pi)**2, -(1+mp.pi)/16-mp.pi/2)]
    for name, p, law, kappa, P, target in models:
        values = moments([0]+[law(h) for h in range(1,nmax+1)], nmax)
        polynomial.append({'family': name, 'p': p, 'kappa': str(kappa), 'P': text(P), 'target': text(target),
                           'rows': [{'n': n, 'scaled_log_ratio': text(n*(mp.log(values[n])-n*mp.log(kappa)-mp.log(P)-logF(p,n)))} for n in ns]})
    zero_base_weights = [2*h*h for h in range(nmax+1)]
    zero_base = moments(zero_base_weights, nmax)
    zero_base_weights[1], zero_base_weights[2] = 3, 7
    zero_changed = moments(zero_base_weights, nmax)
    logs = lambda values:[mp.log(x) for x in values]
    inverse_models = [
        ('bulk', 3, logs(bases[3]), bulk_logs[3], mp.log(2/mp.pi), -J(3)/4, lambda x:1/x),
        ('bulk_D_zero', 2, logs(bases[2]), bulk_logs[2], mp.log(2/mp.pi), mp.mpf(0), lambda x:1/x),
        ('critical', 1, logs(bases[1]), critical_logs[1], products[1], mp.mpf(1), lambda x:mp.log(x)/x),
        ('endpoint', 2, logs(bases[2]), endpoint_logs[2], mp.log(2), 2/(4/I(2)**2), lambda x:x**(-2)),
        ('endpoint_D_zero', 2, logs(zero_base), logs(zero_changed), mp.log(mp.mpf(21)/16), mp.mpf(0), lambda x:x**(-2))]
    inverse_rows = []
    ins = sorted(set(n for n in (16, 32, 64, 128, nmax-1) if n < nmax))
    for name, p, base, changed, logP, D, scale in inverse_models:
        rows = []
        for n in ins:
            for theta in (mp.mpf(0), mp.mpf('.0000001'), mp.mpf('.37'), mp.mpf('.9999999')):
                x = n+theta
                logY = interpolate(base,x)+logP
                xt = inverse(changed,logY)
                residual = abs(interpolate(changed,xt)-logY)
                check(residual < mp.mpf('1e-75'), 'numerical_inverse_residual')
                first = next(j for j, value in enumerate(changed) if value >= logY)
                check(int(mp.ceil(xt)) == first, 'numerical_inverse_ceiling_vs_full_search')
                rows.append({'x': text(x), 'scaled_displacement': text((xt-x)*mp.log(x)/scale(x)),
                             'residual': text(residual), 'base_ceiling': int(mp.ceil(x)), 'changed_ceiling': int(mp.ceil(xt))})
            check(inverse(changed,changed[n]) == n, 'numerical_integer_index_inverse')
            check(next(j for j, value in enumerate(changed) if value >= changed[n]) == n, 'numerical_equality_threshold_search')
        inverse_rows.append({'regime': name, 'p': p, 'exact_base_interpolation': True, 'target': text(-D/p), 'rows': rows})
    occupation = []
    for p in (2,4):
        for n in (32,64):
            weights = [mp.mpf(0)]+[mp.mpf(h)**p for h in range(1,n+1)]
            occ = occupation_mp(weights,n)
            error = abs(mp.fsum(occ)-n)
            check(error < mp.mpf('1e-80'), 'numerical_occupation_mass')
            points = []
            for fraction in (mp.mpf('.3'), mp.mpf('.6'), mp.mpf('.8')):
                h = max(1,int(fraction*n/I(p)))
                U = (1-(I(p)*h/n)**p)**(-mp.mpf('.5'))
                points.append({'h': h, 'occupation': text(occ[h]), 'arch_density': text(U)})
            occupation.append({'p': p, 'n': n, 'mass_error': text(error), 'points': points})
    result = {'schema': 'report202-numerical-diagnostics-v1', 'warning': WARNING,
              'mpmath_version': mp.__version__, 'decimal_precision': dps, 'printed_significant_digits': 40,
              'nmax': nmax, 'numerical_predicate_counts': dict(sorted(counts.items())),
              'numerical_predicate_total': sum(counts.values()), 'regularization': regularization,
              'bulk': bulk, 'critical': critical, 'endpoint': endpoint, 'cumulative': cumulative,
              'polynomial_compositions': polynomial, 'inverse_displacement': inverse_rows,
              'local_occupation': occupation,
              'scalings': {'bulk': 'n log(Ztilde/(P Z)) for q=2', 'critical': 'n^p/log(n) log(Ztilde/(P Z))',
                          'endpoint': 'n^p log(Ztilde/(P Z))', 'cumulative': 'n log(Ztilde/Z), S=0',
                          'polynomial_compositions': 'n log(Z/(kappa^n P F_p))',
                          'inverse_displacement': '(xtilde-x) log(x)/s(x); target -D/p'},
              'cumulative_example': 'a_0=1; a_h=1+1/(3h)+(-1)^h/(4h^2); exp(f_h)=a_h/a_(h-1); even/odd h^2 f_h limits 1/6 and -5/6',
              'inverse_scope': 'Exact base log-linear interpolation at Y/P. No Lambert surrogate, effective onset, or unconditional single-ceiling rule'}
    validate_diagnostics(result)
    return result


def validate_diagnostics(data):
    exact_keys(data, ('schema', 'warning', 'mpmath_version', 'decimal_precision', 'printed_significant_digits', 'nmax',
                     'numerical_predicate_counts', 'numerical_predicate_total', 'regularization', 'bulk', 'critical',
                     'endpoint', 'cumulative', 'polynomial_compositions', 'inverse_displacement', 'local_occupation',
                     'scalings', 'cumulative_example', 'inverse_scope'), 'numerical diagnostics')
    require(data['schema'] == 'report202-numerical-diagnostics-v1' and data['warning'] == WARNING, 'Invalid numerical scope')
    require(data['mpmath_version'] == '1.3.0' and type(data['decimal_precision']) is int and data['decimal_precision'] == 90,
            'Invalid numerical environment')
    require(type(data['printed_significant_digits']) is int and data['printed_significant_digits'] == 40, 'Invalid printed precision')
    require(type(data['nmax']) is int and 64 <= data['nmax'] <= 512, 'Invalid numerical maximum')
    counts = data['numerical_predicate_counts']
    expected_keys = {'finite_regularization_bound_numeric', 'numerical_quadratic_cancellation', 'numerical_quartic_constant',
                     'numerical_independent_product_routes', 'numerical_inverse_residual', 'numerical_inverse_ceiling_vs_full_search',
                     'numerical_integer_index_inverse', 'numerical_equality_threshold_search', 'numerical_occupation_mass'}
    exact_keys(counts, expected_keys, 'numerical counts')
    require(all(type(x) is int and x > 0 for x in counts.values()), 'Invalid numerical count')
    require(type(data['numerical_predicate_total']) is int and data['numerical_predicate_total'] == sum(counts.values()), 'Numerical total mismatch')
    for key, length in (('regularization',9), ('bulk',5), ('critical',3), ('endpoint',5), ('cumulative',4),
                        ('polynomial_compositions',4), ('inverse_displacement',5), ('local_occupation',4)):
        require(type(data[key]) is list and len(data[key]) == length, 'Invalid numerical family: '+key)
    ns = sorted(set(n for n in (16,32,64,128,256,data['nmax']) if n <= data['nmax']))
    ins = sorted(set(n for n in (16,32,64,128,data['nmax']-1) if n < data['nmax']))
    units = 5*len(ins)
    expected_counts = {'finite_regularization_bound_numeric':9, 'numerical_quadratic_cancellation':1,
                       'numerical_quartic_constant':1, 'numerical_independent_product_routes':3,
                       'numerical_inverse_residual':4*units, 'numerical_inverse_ceiling_vs_full_search':4*units,
                       'numerical_integer_index_inverse':units, 'numerical_equality_threshold_search':units,
                       'numerical_occupation_mass':4}
    require(counts == expected_counts, 'Numerical inventory inconsistent with configuration')
    for key in ('bulk','critical','endpoint','cumulative','polynomial_compositions'):
        for family in data[key]:
            require(type(family) is dict and type(family.get('p')) is int, 'Malformed numerical family')
            rows = family.get('rows')
            require(type(rows) is list and [r.get('n') if type(r) is dict else None for r in rows] == ns,
                    'Numerical degree grid mismatch')
            for row in rows:
                exact_keys(row, ('n','scaled_log_ratio'), 'numerical convergence row')
                require(type(row['n']) is int, 'Numerical degree must be an integer')
    for family in data['inverse_displacement']:
        exact_keys(family, ('regime','p','exact_base_interpolation','target','rows'), 'inverse family')
        require(family['exact_base_interpolation'] is True and type(family['p']) is int, 'Invalid inverse normalization')
        require(type(family['rows']) is list and len(family['rows']) == 4*len(ins), 'Invalid inverse row count')
        for row in family['rows']:
            exact_keys(row, ('x','scaled_displacement','residual','base_ceiling','changed_ceiling'), 'inverse row')
            require(type(row['base_ceiling']) is int and type(row['changed_ceiling']) is int, 'Inverse ceilings must be integers')
    require([row['regime'] for row in data['inverse_displacement']] ==
            ['bulk','bulk_D_zero','critical','endpoint','endpoint_D_zero'], 'Inverse family order mismatch')
    for row in data['regularization']:
        exact_keys(row, ('p','q','J','finite_cutoff_error','analytic_cutoff_bound_evaluated_numerically'), 'regularization row')
    for row in data['local_occupation']:
        exact_keys(row, ('p','n','mass_error','points'), 'occupation row')
        require(type(row['p']) is int and type(row['n']) is int and type(row['points']) is list and len(row['points']) == 3,
                'Invalid occupation configuration')
        for point in row['points']:
            exact_keys(point, ('h','occupation','arch_density'), 'occupation point')
            require(type(point['h']) is int and 1 <= point['h'] <= row['n'], 'Invalid occupation height')
    # Only canonical finite decimal strings are admitted in numeric leaf fields.
    numeric_keys = {'J', 'finite_cutoff_error', 'analytic_cutoff_bound_evaluated_numerically', 'P', 'target',
                    'scaled_log_ratio', 'scaled_displacement', 'residual', 'mass_error', 'occupation', 'arch_density', 'x'}
    def visit(value):
        if type(value) is dict:
            for key, item in value.items():
                if key in numeric_keys:
                    require(type(item) is str and re.fullmatch(r'-?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:e[+-]?[0-9]+)?', item) is not None,
                            'Invalid finite numeric diagnostic')
                else: visit(item)
        elif type(value) is list:
            for item in value: visit(item)
    visit(data)
    return True
