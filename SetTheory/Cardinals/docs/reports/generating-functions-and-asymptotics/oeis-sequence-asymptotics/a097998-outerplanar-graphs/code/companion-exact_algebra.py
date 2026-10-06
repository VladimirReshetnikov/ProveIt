"""Exact QQ(tau) Gaussian-moment certificates through four corrections."""
from math import factorial
import json
import mpmath as mp
import sympy as sp
from common import ROOT, require

PRECISION = 100


def run():
    x = sp.symbols('x')
    p = 3*x**4-28*x**3+70*x**2-58*x+8
    require(sp.Poly(p, x).is_irreducible, 'Quartic must be irreducible over QQ')
    root = sp.CRootOf(p, 0)
    require(bool(root > sp.Rational(17076, 100000)), 'Wrong exact root: lower bound')
    require(bool(root < sp.Rational(17077, 100000)), 'Wrong exact root: upper bound')
    field = sp.QQ.algebraic_field(root)
    tau, zero, one = field.unit, field.zero, field.one
    degree = 10

    def mul(a, b, n):
        return [sum((a[j]*b[k-j] for j in range(max(0, k-len(b)+1), min(k, len(a)-1)+1)), zero) for k in range(n+1)]

    def exp0(a, n):
        require(a[0] == zero, 'Nonzero exponential constant')
        out = [one]
        for k in range(1, n+1):
            out.append(sum((j*a[j]*out[k-j] for j in range(1, min(k, len(a)-1)+1)), zero)/k)
        return out

    u = [tau/factorial(j) for j in range(degree+1)]
    square = mul(u, u, degree)
    rad = [one-6*u[0]+square[0]]+[-6*u[j]+square[j] for j in range(1, degree+1)]
    r0 = tau*(3-tau)/(8-5*tau)
    require(r0**2 == rad[0], 'Unsquared radical identity failed')
    r = [r0]
    for j in range(1, degree+1):
        r.append((rad[j]-sum((r[i]*r[j-i] for i in range(1, j)), zero))/(2*r0))
    k = [(one+5*u[0]-r[0])/8]+[(5*u[j]-r[j])/8 for j in range(1, degree+1)]
    kap = [k[j]*factorial(j) for j in range(degree+1)]
    require(kap[1] == one, 'Exact unsquared saddle equation failed')
    kp = [(j+1)*k[j+1] for j in range(degree)]
    qp = mul(u, [one-kp[0]]+[-a for a in kp[1:]], degree-1)
    q = [zero]+[qp[j]/(j+1) for j in range(degree)]
    require(q[0] == q[1] == qp[0] == zero, 'Q(t) must start at t^2')

    def saddle(v):
        exponent = [v*a for a in q[:9]]
        exponent[1] += one
        amplitude = mul(exp0(exponent, 8), [one+v*qp[0]]+[v*a for a in qp[1:9]], 8)
        result = []
        for j in range(5):
            total = zero
            for ell in range(2*j+1):
                def visit(phase, left, power, weight):
                    nonlocal total
                    if phase > 2*j+2:
                        if left != 0 or power % 2:
                            return
                        h = power//2
                        moment = factorial(2*h)//(2**h*factorial(h))
                        total += amplitude[ell]*weight*((-1)**h*moment)/kap[2]**h
                        return
                    for count in range(left//(phase-2)+1):
                        visit(phase+1, left-(phase-2)*count, power+phase*count, weight*k[phase]**count/factorial(count))
                visit(3, 2*j-ell, ell, one)
            result.append(total)
        return result

    values = {v: saddle(v) for v in range(9)}
    polynomials = []
    for j in range(5):
        # A priori degree <= 2j from the finite generator. Newton interpolation
        # from 2j+1 exact values therefore certifies the polynomial identically.
        row = [values[v][j] for v in range(2*j+1)]
        out = [zero]*(2*j+1)
        basis = [one]  # binomial(v,h)
        for h in range(2*j+1):
            for a, value in enumerate(basis):
                out[a] += row[0]*value
            row = [row[i+1]-row[i] for i in range(len(row)-1)]
            basis = mul(basis, [-h*one, one], h+1)
            basis = [a/(h+1) for a in basis]
        require(all(a == zero for a in out[j+1:]), 'Marked polynomial degree exceeds j')
        polynomials.append(out[:j+1])
    d = -one/(2*kap[2])+kap[3]/(2*kap[2]**2)+kap[4]/(8*kap[2]**2)-5*kap[3]**2/(24*kap[2]**3)
    t2 = tau*(one/kap[2]-kap[3]/(3*kap[2]**2))
    require(d == values[0][1], 'Closed d1 identity failed')
    require(polynomials[1] == [d, 5*tau/2], 'Marked d1 polynomial identity failed')
    require(polynomials[2] == [values[0][2], 7*tau*d/2-35*t2/8, 35*tau**2/8], 'Marked d2 polynomial identity failed')
    a, beta, gamma = 5*tau/2, 7*tau*d/2-35*t2/8, 35*tau**2/8
    mean2 = beta-d*a+2*gamma-a*a
    variance2 = mean2+2*gamma-a*a
    connectivity2 = a*a+d*a-beta-gamma
    require(mean2 == tau*d-35*t2/8+5*tau**2/2, 'Mean identity failed')
    require(variance2 == mean2+5*tau**2/2, 'Variance identity failed')
    require(connectivity2 == -tau*d+35*t2/8+15*tau**2/8, 'Connectivity identity failed')

    # Formal logarithm recurrence and independent explicit Stirling formulas.
    log_coefficients = {}
    for v in (0, 1):
        e = values[v]
        logs = [zero]
        for j in range(1, 5):
            logs.append(e[j]-sum((k1*logs[k1]*e[j-k1] for k1 in range(1, j)), zero)/j)
        logs[1] += one/12
        logs[3] -= one/360
        expected = [zero, e[1]+one/12, e[2]-e[1]**2/2,
                    e[3]-e[1]*e[2]+e[1]**3/3-one/360,
                    e[4]-e[1]*e[3]-e[2]**2/2+e[1]**2*e[2]-e[1]**4/4]
        require(logs == expected, 'Logarithm/Stirling identity failed')
        log_coefficients[str(v)] = logs[1:]

    def encode(value):
        descending = list(value.to_list())
        ascending = list(reversed(descending))+[sp.Rational(0)]*(4-len(descending))
        return [str(v) for v in ascending]

    with mp.workdps(PRECISION):
        tn = mp.findroot(lambda z: 3*z**4-28*z**3+70*z**2-58*z+8, (mp.mpf('.17076'), mp.mpf('.17077')))
        def evaluate(value):
            return sum(mp.mpf(c)*tn**j for j, c in enumerate(encode(value)))
        def decimal(value):
            return str(evaluate(value))
        b = lambda z: (1+5*z-mp.sqrt(1-6*z+z*z))/8
        nu = tn-tn*b(tn)+mp.quad(b, [0, tn])
        rho = tn*mp.exp(-b(tn))
        A = tn/mp.sqrt(2*mp.pi*evaluate(kap[2]))
        fixture = json.loads((ROOT / 'fixtures' / 'high_precision.json').read_text())
        errors = {}
        for v in range(3):
            error = max(abs(evaluate(z)-mp.mpf(f)) for z, f in zip(values[v], fixture['coefficients'][str(v)]))
            require(error < mp.mpf('1e-50'), 'Frozen coefficient comparison failed')
            errors[str(v)] = str(error)
        constants = {'tau': str(tn), 'rho': str(rho), 'nu': str(nu), 'connected_A': str(A), 'all_A': str(mp.exp(nu)*A)}
        constant_errors = {}
        for name, source in [('tau', 'tau'), ('rho', 'rho'), ('nu', 'nu'), ('connected_A', 'connected_constant'), ('all_A', 'all_constant')]:
            error = abs(mp.mpf(constants[name])-mp.mpf(fixture[source]))
            require(error < mp.mpf('1e-60'), 'Frozen constant comparison failed: '+name)
            constant_errors[name] = str(error)
        quantities = {'t2': t2, 'first_moment_correction': a, 'mean_second': mean2,
                      'variance_second': variance2, 'connectivity_second': connectivity2}
        result = {'field': {'minimal_polynomial_ascending': [8, -58, 70, -28, 3],
                         'root_interval': ['17076/100000', '17077/100000'],
                         'basis': ['1', 'tau', 'tau^2', 'tau^3'], 'irreducible': True},
                'precision_decimal_digits': PRECISION, 'constants': constants,
                'exact_kappa_0_through_10': [encode(z) for z in kap],
                'exact_d_polynomials_ascending_v': [[encode(a1) for a1 in row] for row in polynomials],
                'exact_coefficients_at_v': {str(v): [encode(z) for z in values[v]] for v in range(3)},
                'decimal_coefficients_at_v': {str(v): [decimal(z) for z in values[v]] for v in range(3)},
                'exact_log_stirling_coefficients': {v: [encode(z) for z in row] for v, row in log_coefficients.items()},
                'decimal_log_stirling_coefficients': {v: [decimal(z) for z in row] for v, row in log_coefficients.items()},
                'exact_component_constants': {name: encode(z) for name, z in quantities.items()},
                'decimal_component_constants': {name: decimal(z) for name, z in quantities.items()},
                'checks': {'unsquared_saddle': True, 'marker_degrees': [0, 1, 2, 3, 4],
                           'd1_d2_identities': True, 'moment_connectivity_identities': True, 'log_stirling_identities': True,
                           'max_frozen_coefficient_errors': errors, 'frozen_constant_errors': constant_errors},
                'numerical_status': 'Point-valued numerical cross-checks, not interval enclosures'}

    frozen = json.loads((ROOT / 'fixtures' / 'exact_certificates.json').read_text())
    actual = {key: value for key, value in result.items() if key.startswith('exact_') or key == 'field'}
    require(actual == frozen, 'Frozen exact algebraic certificate discrepancy')
    result['checks']['frozen_exact_certificates_match'] = True
    return result
