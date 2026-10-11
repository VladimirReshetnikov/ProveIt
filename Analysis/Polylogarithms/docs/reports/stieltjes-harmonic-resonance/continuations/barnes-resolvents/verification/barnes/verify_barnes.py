"""Independent numerical diagnostics for the Barnes resolvent identities.

The depth-two derivative and the published Fourier T_n sums are evaluated
separately, using their respective defining series and explicit zeta tails.
The resulting transform is compared with direct Barnes-G quadrature.
No calculation here is an interval certificate or a proof.
Run with Python 3 and mpmath; output is written beside this script.
"""
from functools import lru_cache
from pathlib import Path
import json
import time
import mpmath as mp

mp.mp.dps = 65
N, M, TERMS = 150, 360, 100
L = mp.log(2 * mp.pi)
started = time.time()


def order_derivative(s, q):
    return mp.diff(lambda u: mp.polylog(u, q), s)


@lru_cache(None)
def zeta_tail(s, derivative=0):
    if derivative:
        return mp.diff(lambda u: mp.zeta(u, M + 1), s)
    return mp.zeta(s, M + 1)


def independent_coefficients():
    """Compute D_n and T_n without using their claimed generating relation."""
    logs = [mp.mpf(0)] + [mp.log(m) for m in range(1, M + N + 1)]
    harmonic = [mp.mpf(0)]
    for k in range(1, TERMS):
        harmonic.append(harmonic[-1] + mp.mpf(1) / k)
    dtail = [2*zeta_tail(k+2, 1) + harmonic[k]*zeta_tail(k+2)
             for k in range(TERMS)]
    ttail = [-zeta_tail(2*k+2, 1) for k in range(TERMS)]
    ds, ts = [], []
    for n in range(1, N + 1):
        d = -mp.fsum((logs[m]+logs[m+n]) / (m*(m+n))
                     for m in range(1, M+1))
        # log(1+r)/(1+r) = sum_{k>=1} (-1)^{k+1} H_k r^k.
        d += mp.fsum((-n)**k * dtail[k] for k in range(TERMS))
        t = mp.fsum(logs[m]/(m*m-n*n) for m in range(1, M+1) if m != n)
        t += mp.fsum(n**(2*k) * ttail[k] for k in range(TERMS))
        ds.append(d)
        ts.append(t)
    return ds, ts


def series(q, values):
    return mp.fsum(q**n * value for n, value in enumerate(values, start=1))


def transform(z, dcoeff):
    eps = 1 if mp.im(z) > 0 else -1
    a = z + eps*mp.pi*1j
    q = (z-eps*mp.pi*1j)/a
    c = 2*eps*mp.pi*1j/a**2
    li1, li2 = mp.polylog(1,q), mp.polylog(2,q)
    d = series(q, dcoeff)
    acal = (d-order_derivative(2,q)-(mp.euler+L+1)*li2
            -li1*order_derivative(1,q))/(2*mp.pi**2)-li1/4
    scal = (order_derivative(1,q)-(mp.euler+2*L)*li1
            -(li2+li1**2)/2)/(2*mp.pi)
    mean = 2*mp.diff(mp.zeta,-1)-mp.mpf(1)/12-L/4
    return -mean/a+c*(acal+eps*1j*scal)/(2*q)


def quadrature(z):
    return mp.quad(lambda x: mp.log(mp.barnesg(x)) /
                   (mp.pi*mp.cot(mp.pi*x)-z),
                   [0, mp.mpf('.1'), mp.mpf('.5'), mp.mpf('.9'), 1])


def record(name, lhs, rhs, tolerance='1e-40'):
    error = abs(lhs-rhs)
    scaled = error/max(mp.mpf(1), abs(lhs), abs(rhs))
    passed = scaled < mp.mpf(tolerance)
    assert passed, (name, mp.nstr(scaled, 15))
    result = dict(name=name, lhs=mp.nstr(lhs,58), rhs=mp.nstr(rhs,58),
                  absolute_residual=mp.nstr(error,14),
                  scaled_residual=mp.nstr(scaled,14),
                  tolerance=tolerance, passed=passed)
    print(name, result['scaled_residual'], flush=True)
    return result


def main():
    dcoeff, tcoeff = independent_coefficients()
    checks = []
    for q in [mp.mpf('.5'), mp.mpc('.2','.15')]:
        rhs = (mp.polylog(1,q)*order_derivative(1,q)/2
               -series(q,dcoeff)/2+order_derivative(2,q)/4)
        checks.append(record('independent_D_T_relation_'+str(q), series(q,tcoeff), rhs))
    for z in [3j*mp.pi, mp.pi*(mp.mpf('.4')+mp.mpf('1.5')*1j), -3j*mp.pi]:
        checks.append(record('Barnes_G_resolvent_'+str(z), transform(z,dcoeff), quadrature(z)))
    rhs = (order_derivative(1,mp.mpf('.5'))-(mp.euler+2*L)*mp.log(2)
           -mp.pi**2/24-mp.log(2)**2/4)/(16*mp.pi**2)
    checks.append(record('real_component_at_three_pi', mp.re(quadrature(3j*mp.pi)), rhs,
                         tolerance='1e-58'))
    checks.append(record('removable_q_zero_real_component', mp.re(quadrature(1j*mp.pi)),
                         -(mp.euler+2*L+mp.mpf('.5'))/(8*mp.pi**2), tolerance='1e-58'))
    x = mp.mpf('.25')
    a, b = mp.log(mp.barnesg(x)), mp.log(mp.barnesg(1-x))
    pointwise_residual = a*a-((a+b)**2+(a-b)**2)/4
    # A deliberately nonzero residual, documenting the error being corrected.
    assert abs(pointwise_residual) > mp.mpf('.7')
    result = dict(kind='non_interval_numerical_diagnostics', precision_dps=mp.mp.dps,
                  mpmath_version=mp.__version__, elapsed_seconds=round(time.time()-started,3),
                  truncation=dict(outer_N=N, inner_M=M, tail_terms=TERMS),
                  checks=checks, all_passed=all(c['passed'] for c in checks),
                  mezo_equation7_pointwise_residual_at_quarter=mp.nstr(pointwise_residual,58),
                  interpretation='Exact proofs are in the article; decimal agreement is diagnostic.')
    Path(__file__).with_name('barnes_numeric.json').write_text(json.dumps(result,indent=2)+'\n')
    print('All',len(checks),'numerical comparisons passed.',flush=True)


if __name__ == '__main__':
    main()
