"""Independent ordinary-Taylor inversion and central-binomial transfer.

This computation consumes no Euler derivatives, saddle amplitudes or correction
coefficients until the final comparison. It is a formal/numerical cross-check,
not a separate analytic continuation or Delta-domain proof.
"""
from fractions import Fraction as F
from math import comb
import mpmath as mp
from common import require


def mul(a, b, n):
    return [sum(a[j]*b[k-j] for j in range(max(0, k-len(b)+1), min(k, len(a)-1)+1)) for k in range(n+1)]


def expser(a, n):
    out = [mp.exp(a[0])]
    for k in range(1, n+1):
        out.append(sum(j*a[j]*out[k-j] for j in range(1, min(k, len(a)-1)+1))/k)
    return out


def powerser(a, power, n):
    out = [a[0]**power]
    for k in range(1, n+1):
        out.append(sum(((power+1)*j-k)*a[j]*out[k-j] for j in range(1, min(k, len(a)-1)+1))/(k*a[0]))
    return out


def compose(a, y, n):
    out = [mp.mpf(0)]*(n+1)
    power = [mp.mpf(1)]+[mp.mpf(0)]*n
    for coefficient in a[:n+1]:
        out = [v+coefficient*w for v, w in zip(out, power)]
        power = mul(power, y, n)
    return out


def central_binomial_coefficients():
    # U_n=sqrt(pi*n)*binom(2n,n)/4^n satisfies
    # U_(n+1)/U_n=(1+x/2)/sqrt(1+x), x=1/n.
    # Solve U(x/(1+x))=U(x)*(1+x/2)/sqrt(1+x) recursively.
    h = [F(1)]
    for k in range(1, 6):
        h.append(h[-1]*(F(-1, 2)-k+1)/k)
    ratio = [h[0]]+[h[k]+h[k-1]/2 for k in range(1, 6)]
    out = [F(1)]
    for m in range(1, 5):
        residual = F(0)
        for j in range(m):
            degree = m+1-j
            left = (-1)**degree*comb(j+degree-1, degree) if j else 0
            residual += out[j]*(left-ratio[degree])
        out.append(residual/m)
    require(out == [F(1), F(-1, 8), F(1, 128), F(5, 1024), F(-21, 32768)], 'Central-binomial recurrence failed')
    return out


def compute():
    with mp.workdps(100):
        nmax = 13
        p = lambda z: 3*z**4-28*z**3+70*z*z-58*z+8
        tau = mp.findroot(p, (mp.mpf('.17076'), mp.mpf('.17077')))
        b = lambda z: (1+5*z-mp.sqrt(1-6*z+z*z))/8
        nu = tau-tau*b(tau)+mp.quad(b, [0, tau])
        r = [mp.sqrt(1-6*tau+tau*tau)]
        rad = [r[0]**2, 2*tau-6, mp.mpf(1)]+[mp.mpf(0)]*(nmax-2)
        for j in range(1, nmax+1):
            r.append((rad[j]-sum(r[k]*r[j-k] for k in range(1, j)))/(2*r[0]))
        bcoef = [b(tau), (5-r[1])/8]+[-r[j]/8 for j in range(2, nmax+1)]
        # y=T-tau, and z/rho=(1+y/tau)*exp(-(b(tau+y)-b(tau))).
        zratio = mul([mp.mpf(1), 1/tau], expser([mp.mpf(0)]+[-v for v in bcoef[1:]], nmax), nmax)
        require(abs(zratio[1]) < mp.mpf('1e-90'), 'Ordinary Taylor linear term failed')
        # X^2=y^2 F(y); physical branch y=-X F(y)^(-1/2).
        Fcoef = [-v for v in zratio[2:]]
        Gcoef = powerser(Fcoef, -mp.mpf(1)/2, 10)
        y = [mp.mpf(0)]*12
        for j in range(1, 10):
            y[j] = -compose(Gcoef, y, j-1)[j-1]
        T = [tau]+y[1:10]
        C = [nu, mp.mpf(0)]
        for j in range(2, 12):
            C.append(-mp.mpf(2)/j*sum(T[k] for k in range(j-2, -1, -2)))
        central_exact = central_binomial_coefficients()
        central = [mp.mpf(q.numerator)/q.denominator for q in central_exact]
        def transfer(ell, order):
            answer = central[:order+1]
            for r1 in range(ell+2):
                answer = mul(answer, [(mp.mpf(r1)+mp.mpf('.5'))**j for j in range(order+1)], order)
            return answer
        output = {}
        for label, v in [('0', 0), ('1', 1), ('2', 2), ('complex', mp.mpc('.5', '.3'))]:
            H = C if v == 0 else expser([v*q for q in C], 11)
            lead = H[3]/mp.gamma(-mp.mpf(3)/2)
            d = []
            for j in range(5):
                d.append(sum(H[2*ell+3]/mp.gamma(-mp.mpf(2*ell+3)/2)*transfer(ell, j-ell)[j-ell] for ell in range(j+1))/lead)
            output[label] = {'marker_real': str(mp.re(v)), 'marker_imag': str(mp.im(v)),
                             'coefficients_real': [str(mp.re(a)) for a in d],
                             'coefficients_imag': [str(mp.im(a)) for a in d],
                             'leading_real': str(mp.re(lead)), 'leading_imag': str(mp.im(lead))}
        return {'precision_decimal_digits': 100, 'central_binomial_coefficients': [str(q) for q in central_exact], 'series': output}


def run(algebra):
    result = compute()
    with mp.workdps(100):
        tau = mp.mpf(algebra['constants']['tau'])
        for label, record in result['series'].items():
            v = mp.mpc(record['marker_real'], record['marker_imag'])
            expected = []
            for row in algebra['exact_d_polynomials_ascending_v']:
                expected.append(sum(sum(mp.mpf(c)*tau**h for h, c in enumerate(coeff))*v**k for k, coeff in enumerate(row)))
            actual = [mp.mpc(a, b) for a, b in zip(record['coefficients_real'], record['coefficients_imag'])]
            error = max(abs(a-b) for a, b in zip(actual, expected))
            require(error < mp.mpf('1e-70'), 'Independent ordinary-Taylor comparison failed: '+label)
            record['max_difference_exact_algebra'] = str(error)
        for label, key in [('0', 'connected_A'), ('1', 'all_A')]:
            error = abs(mp.mpf(result['series'][label]['leading_real'])-mp.mpf(algebra['constants'][key]))
            require(error < mp.mpf('1e-90'), 'Independent leading amplitude mismatch')
    result['status'] = 'Independent finite formal/numerical coefficient check; no interval or Delta-domain certificate'
    return result
