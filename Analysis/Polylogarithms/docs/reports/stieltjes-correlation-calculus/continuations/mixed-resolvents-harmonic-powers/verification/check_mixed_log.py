#!/usr/bin/env python3
"""Independent audit of the proposed opposite-orientation mixed-log transform."""
from pathlib import Path
import json
import mpmath as mp

mp.mp.dps = 80
HERE = Path(__file__).resolve().parent

def Li_double(a, b, x, y, terms=420):
    # Outer decay is geometric for the calls below.  The inner partial
    # sum is updated independently of the Fourier-difference derivation.
    acc = mp.mpc(0)
    inner = mp.mpc(0)
    xp, yp = mp.mpc(1), mp.mpc(1)
    for n in range(1, terms+1):
        xp *= x
        acc += xp*inner/mp.mpf(n)**a
        yp *= y
        inner += yp/mp.mpf(n)**b
    return acc

def T2(x, y):
    if not x or not y:
        return mp.mpc(0)
    if x == 1 and y == 1:
        return 5*mp.zeta(4)/4
    if x == 1:
        # Partial fractions in k establish this independent specialization.
        return mp.zeta(2)*mp.polylog(2, y)-Li_double(3, 1, y, 1)-mp.polylog(4, y)
    return mp.polylog(3, x)*mp.polylog(1, x*y)-Li_double(1, 3, x*y, 1/y)

def P2(q, r):
    return T2(q, r)-T2(q, 1)-T2(1, r)+T2(1, 1)

def centered_log(t, q, epsilon):
    return (mp.log(2*mp.sin(mp.pi*t))+epsilon*mp.pi*1j*(t-mp.mpf('0.5'))
            -mp.log(1-q*mp.exp(epsilon*2*mp.pi*1j*t)))

def encode(z):
    z = mp.mpc(z)
    return {'real': mp.nstr(z.real, 55), 'imag': mp.nstr(z.imag, 55)}

checks = []
for q, r in [(mp.mpf('0.2'), mp.mpf('0.3')),
             (mp.mpc('0.2', '0.1'), mp.mpc('-0.15', '0.2')),
             (mp.mpf(0), mp.mpf(0))]:
    def kernel(t):
        return centered_log(t, q, 1)*centered_log(t, r, -1)
    integ = mp.quad(lambda t: -(t*t-t+mp.mpf(1)/6)*kernel(t)/2,
                    [0, mp.mpf('0.5'), 1])
    prediction = -(P2(q,r)+P2(r,q))/(4*mp.pi**2)
    meann = mp.quad(kernel, [0, mp.mpf('0.5'), 1])
    meanf = mp.polylog(2,q*r)-mp.polylog(2,q)-mp.polylog(2,r)+mp.zeta(2)
    assert abs(integ-prediction) < mp.mpf('1e-75')
    assert abs(meann-meanf) < mp.mpf('1e-75')
    checks.append({'q':encode(q),'r':encode(r),
                   'ordinary_zeta_minus_one_integral':encode(integ),
                   'spectral_prediction':encode(prediction),
                   'absolute_residual':mp.nstr(abs(integ-prediction),12),
                   'mean_residual':mp.nstr(abs(meann-meanf),12)})

report = {'status':'passed','working_dps':mp.mp.dps,
          'checks':checks,
          'scope':'Ordinary-domain quadrature and geometric-series diagnostics, not interval certificates.'}
(HERE/'mixed_log_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':'passed','cases':len(checks),
                  'largest_spectral_residual':max((c['absolute_residual'] for c in checks), key=mp.mpf),
                  'largest_mean_residual':max((c['mean_residual'] for c in checks), key=mp.mpf)},indent=2))
