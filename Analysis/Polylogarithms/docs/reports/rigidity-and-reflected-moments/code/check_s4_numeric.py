#!/usr/bin/env python3
"""Independent quadrature audit of S4; this is not the proof certificate."""
from pathlib import Path
import json
import mpmath as mp

mp.mp.dps = 70
partition = [0, mp.mpf('0.1'), 1]

def gaussian_double(a, b):
    integrand = lambda x: ((-mp.log(x)) ** (a - 1)
        * mp.im(1j * mp.polylog(b, 1j * x) / (1 - 1j * x)))
    return mp.quad(integrand, partition) / mp.factorial(a - 1)

s4 = mp.quad(lambda x: mp.log(x) ** 3 * mp.log(1 + x*x) / (1 + x*x),
             partition) / 6
g = {a: gaussian_double(a, 5-a) for a in (2, 3, 4)}
beta4 = mp.im(mp.polylog(4, 1j))
rhs = ((4*g[4] - 3*g[3] - 9*g[2])/7 + mp.pi**5/224
       - mp.mpf(27)/224 * mp.catalan * mp.zeta(3)
       - 2*beta4*mp.log(2))
result = {'working_decimal_digits': mp.mp.dps,
          'S4': mp.nstr(s4, 65),
          'right_hand_side': mp.nstr(rhs, 65),
          'absolute_residual': mp.nstr(abs(s4-rhs), 8),
          'role': 'numerical audit, not a proof'}
print(json.dumps(result, indent=2))

assert abs(s4-rhs) < mp.mpf('1e-60')
out = Path(__file__).resolve().parents[1] / 'results' / 'S4_numerical_audit.json'
out.write_text(json.dumps(result, indent=2) + '\n')
