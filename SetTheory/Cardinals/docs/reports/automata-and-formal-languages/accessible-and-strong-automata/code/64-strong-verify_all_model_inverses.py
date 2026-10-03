"""Smooth inverse checks for B, R, U and labeled L; no ceiling guarantee."""
from pathlib import Path
import json
import mpmath as mp
from generate_coefficients import mul, exp_series
from verify_exact_sectors import counts, unrooted
mp.mp.dps = 100
root = Path(__file__).parent
out = []
for k in (2, 3, 4):
    co = json.loads((root / f'coefficients_k{k}.json').read_text())
    d = k - 1
    v, rho = mp.mpf(co['v']), mp.mpf(co['rho'])
    c = 1 - k*rho
    beta = mp.exp(-d)/(rho*v**d)
    C = mp.sqrt(c/(2*mp.pi))
    alpha = list(map(mp.mpf, co['alpha']))
    J = len(alpha)-1
    logstirling = [mp.mpf(0)]*(J+1)
    for r in range(1, (J+1)//2+1):
        degree = 2*r-1
        if degree <= J:
            logstirling[degree] = mp.bernoulli(2*r)/(2*r*(2*r-1))
    labeled_alpha = mul(alpha, exp_series(logstirling, J), J)
    _, labeled = counts(k, 240)
    for n in (40, 80, 120, 240):
        u = unrooted(k, n, labeled)
        targets = {'B': mp.mpf(labeled[n])/mp.factorial(n),
                   'R': mp.mpf(labeled[n])/mp.factorial(n-1),
                   'U': mp.mpf(u.numerator)/u.denominator,
                   'L': mp.mpf(labeled[n])}
        for mode, target in targets.items():
            if mode == 'L':
                a, gamma, s, C0, coeff = k, beta/mp.e, mp.mpf(0), mp.sqrt(c), labeled_alpha
            else:
                a, gamma, s, C0, coeff = d, beta, mp.mpf('.5' if mode == 'R' else '-.5'), C, alpha
            y = mp.log(target)
            x = y/(a*mp.lambertw(gamma**(mp.mpf(1)/a)*y/a))
            lam = a*mp.log(x)+a+mp.log(gamma)
            A = s*mp.log(x)+mp.log(C0)
            delta0 = -A/lam
            delta1 = -(a*delta0**2/2+s*delta0+coeff[1])/(x*lam)
            def logmodel(z):
                return mp.log(C0)+z*mp.log(gamma)+(a*z+s)*mp.log(z)+mp.log(sum(t*z**(-j) for j,t in enumerate(coeff)))
            smooth = mp.findroot(lambda z: logmodel(z)-y, (x,x+1))
            e2, e5 = x+delta0+delta1-n, smooth-n
            assert abs(e2) < mp.mpf('.01')
            assert abs(e5) < abs(e2)
            out.append({'k': k, 'n': n, 'mode': mode,
                        'two_correction_error': mp.nstr(e2, 30),
                        'degree5_smooth_error': mp.nstr(e5, 30)})
(root/'all_model_inverse_validation.json').write_text(json.dumps(out,indent=2)+'\n')
print('Passed 48 smooth inverse checks across B, R, U, and labeled L.')
