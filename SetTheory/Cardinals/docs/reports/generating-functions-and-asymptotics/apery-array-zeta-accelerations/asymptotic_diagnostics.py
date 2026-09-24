#!/usr/bin/env python3
"""Optional high-precision diagnostics (mpmath); not used as a proof oracle."""
from pathlib import Path
import mpmath as mp
from verify_independent import T, U, F2, F3

mp.mp.dps = 420
phi=(1+mp.sqrt(5))/2
rho=phi**5
beta=3+2*mp.sqrt(2)
lam=beta**2

def mq(q):
    return mp.mpf(q.numerator)/q.denominator

lines=['ASYMPTOTIC DIAGNOSTICS', '420 decimal working digits; mpmath reference values.',
       'Ratios below are exact-array / leading-asymptotic, and true-error / leading-error.',
       'These diagnostics are NOT the rational certificates and are NOT a proof.', '',
       'family        k    N      array ratio       error ratio']
for family in ('zeta3','zeta2-super','zeta2-sub'):
    for k in (0,1,3):
        for n in (10,30,100):
            if family=='zeta3':
                predicted=beta**(k+1)*lam**n/(2**mp.mpf('2.25')*mp.pi**mp.mpf('1.5')*n**mp.mpf('1.5'))
                array=mp.mpf(T(n,n+k))
                error=mp.zeta(3)-mq(F3(n,n+k))
                error_prediction=4*mp.pi**3*lam**(-(2*n+k+1))
            else:
                sub=family=='zeta2-sub'
                shift=3*k if sub else 2*k
                predicted=phi**shift*rho**(n+mp.mpf('.5'))/(2*mp.pi*5**mp.mpf('.25')*n)
                x,y=(n+k,n) if sub else (n,n+k)
                array=mp.mpf(U(x,y))
                error=mp.zeta(2)-mq(F2(x,y))
                error_prediction=(-1)**x*4*mp.pi**2*phi**(-2*shift)*rho**(-(2*n+1))
            lines.append(f'{family:13s} {k:2d} {n:4d} {mp.nstr(array/predicted,12):>17s} '
                         f'{mp.nstr(error/error_prediction,12):>17s}')
lines += ['', 'Asymptotic decimal digits per added diagonal term:',
          'zeta(3): '+mp.nstr(2*mp.log10(lam),17),
          'zeta(2): '+mp.nstr(2*mp.log10(rho),17)]
text='\n'.join(lines)+'\n'
(Path(__file__).resolve().parent / 'data' / 'asymptotic_diagnostics.txt').write_text(text)
print(text)
