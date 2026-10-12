"""Independent numerical diagnostics for the compact logarithmic density.

The direct sums do not use the density identity.  The optional subtracted
sum removes its one asymptotic 1/x term before ordinary summation.
These checks are not interval certificates.
"""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 60


def run_case(a, beta, masses, repeated=False):
    a, beta = mp.mpf(a), mp.mpf(beta)
    masses = [mp.mpf(v) for v in masses]
    r = len(masses)
    coefficient = mp.fprod(v - beta for v in masses)
    edges = sorted(set([beta] + masses))

    def rho(t, flags):
        if repeated:
            y = mp.log((masses[0] - t) / (t - beta))
            return sum((-1)**h * mp.binomial(r, 2*h + 1)
                       * mp.pi**(2*h) * y**(r-2*h-1)
                       for h in range((r-1)//2 + 1))
        result = mp.mpc(1)
        for mass, flag in zip(masses, flags):
            result *= (mp.log(abs((mass-t)/(beta-t)))
                       - (mp.pi*1j if flag else 0))
        return -mp.im(result) / mp.pi

    def compact_integral(f):
        result = mp.mpf(0)
        for left, right in zip(edges, edges[1:]):
            middle = (left + right)/2
            flags = [middle < mass for mass in masses]
            # Endpoint logarithms are integrable; quadrature stays inside.
            result += mp.quad(lambda t: rho(t, flags)*f(t),
                              [left, middle, right])
        return result

    def q0(t):
        b = mp.sqrt(t)
        if b == 0:
            return mp.polygamma(1, a)
        return mp.re((mp.digamma(a+1j*b)-mp.digamma(a-1j*b))/(2j*b))

    def kernel(n):
        x = n+a
        return mp.fprod(mp.log1p((v-beta)/(x*x+beta)) for v in masses)

    direct_plain = mp.nsum(kernel, [0, mp.inf])
    integral_plain = compact_integral(q0)

    def subtracted(n):
        x = n+a
        return x**(2*r-1)*kernel(n)-coefficient/x

    # Summation acceleration applied to cancellation-prone summands can
    # invent a ~1e-9 error even at 60 digits. Use a finite head followed
    # by an independently convergent power expansion and Hurwitz tail.
    cutoff, order = 40, 32
    coefficients = [mp.mpf(1)] + [mp.mpf(0)]*order
    for mass in masses:
        local = [mp.mpf(0)] + [(-1)**(k+1)*(mass**k-beta**k)/k
                                   for k in range(1, order+1)]
        coefficients = [sum(coefficients[j]*local[k-j]
                            for j in range(k+1))
                        for k in range(order+1)]
    direct_subtracted = sum(subtracted(n) for n in range(cutoff))
    direct_subtracted += sum(coefficients[k]*mp.zeta(2*k-2*r+1, cutoff+a)
                             for k in range(r+1, order+1))
    radius = 1/(2*max(masses))
    majorant = mp.fprod(-mp.log1p(-mass*radius)-mp.log1p(-beta*radius)
                       for mass in masses)
    omitted_tail_bound = (majorant*radius**(-order-1)
                         *mp.zeta(2*order-2*r+3, cutoff+a)
                         /(1-1/(radius*(cutoff+a)**2)))
    integral_subtracted = (-1)**r * compact_integral(
        lambda t: t**(r-1)*(mp.re(mp.digamma(a+1j*mp.sqrt(t)))-mp.digamma(a)))
    moments = [compact_integral(lambda t, k=k: t**k) for k in range(r)]
    expected_moments = [mp.mpf(0)]*(r-1) + [(-1)**(r-1)*coefficient]
    return dict(a=str(a), beta=str(beta), masses=list(map(str, masses)),
                repeated=repeated,
                subtracted_direct_method=dict(cutoff=cutoff, power_terms=order,
                      description='Finite head plus convergent Hurwitz-zeta tail'),
                subtracted_tail_bound=mp.nstr(omitted_tail_bound, 8),
                direct_plain=mp.nstr(direct_plain, 55),
                integral_plain=mp.nstr(integral_plain, 55),
                plain_residual=mp.nstr(abs(direct_plain-integral_plain), 8),
                direct_subtracted=mp.nstr(direct_subtracted, 55),
                integral_subtracted=mp.nstr(integral_subtracted, 55),
                subtracted_residual=mp.nstr(abs(direct_subtracted-integral_subtracted), 8),
                moments=list(map(lambda v: mp.nstr(v, 55), moments)),
                moment_residuals=[mp.nstr(abs(u-v), 8)
                                  for u,v in zip(moments, expected_moments)])


if __name__ == '__main__':
    data = dict(working_digits=mp.mp.dps,
                status='Numerical diagnostics, not interval certificates',
                cases=[run_case('0.7','0.2',['0.8','1.4','2.1']),
                       run_case('1.25','0',['0.9','0.9','0.9'], repeated=True)])
    output = Path(__file__).resolve().parents[1] / 'data' / 'density_independent_checks.json'
    with open(output, 'w', encoding='utf-8') as handle:
        json.dump(data, handle, indent=2)
        handle.write('\n')
    print(json.dumps(data, indent=2))
