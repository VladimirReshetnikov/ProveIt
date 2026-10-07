#!/usr/bin/env python3
"""Fixed floating-point diagnostics, explicitly separate from exact receipts.

There is no interval arithmetic, certified finite-n asymptotic onset, or
certified rounding here. No sequence coefficient is fitted to numerical data.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
import argparse
import mpmath as mp
from common import emit, require
from exact_counts import A

def diagnostics():
    with mp.workdps(100):
        # This fixed product/sum cutoff is numerical, not an interval proof.
        J=80
        C=mp.fprod(1/(1-1/mp.factorial(j)) for j in range(2,J+1))
        D=lambda k:mp.fsum(mp.factorial(j)/(mp.factorial(j-k)*(mp.factorial(j)-1))
                           for j in range(max(2,k),J+1))
        H3=D(3)/3
        H4=D(4)/4+(D(2)/2)**2+mp.fsum((j*(j-1)/(2*(mp.factorial(j)-1)))**2 for j in range(2,J+1))
        H5=D(5)/5
        H6=2*D(6)/9+2*(D(3)/3)**2+2*mp.fsum((j*(j-1)*(j-2)/(3*(mp.factorial(j)-1)))**2 for j in range(3,J+1))
        I=[1,1]
        for n in range(2,10001):
            I.append(I[-1]+(n-1)*I[-2])
        shown=lambda value:mp.nstr(value,30)
        low=[]
        for n in (10,15,20):
            low.append({'n':n,'a_n_over_I_n':shown(mp.mpf(A[n])/I[n]),
                        'residual_after_C':shown(mp.mpf(A[n])/I[n]-C),
                        'residual_after_H3':shown(mp.mpf(A[n])/I[n]-C-C*H3*mp.mpf(I[n-3])/I[n])})
        cs=[mp.mpf(1),mp.mpf(7)/24,-mp.mpf(119)/1152,-mp.mpf(7933)/414720,
            mp.mpf(1967381)/39813120,-mp.mpf(57200419)/1337720832,mp.mpf(6340449533)/687970713600]
        rows=[]
        for n in (100,1000,10000):
            t=1/mp.sqrt(n)
            logbase=mp.mpf(n)/2*(mp.log(n)-1)+mp.sqrt(n)-mp.mpf(1)/4-mp.log(2)/2
            normalized=mp.exp(mp.log(I[n])-logbase)
            residuals={str(k):shown((normalized-mp.fsum(cs[j]*t**j for j in range(k+1)))/t**(k+1)) for k in (3,4,5)}
            s=3
            approx=1-s*t/2+3*s*s*t*t/8+(-7*s**3-6*s*s+7*s)*t**3/48+(25*s**4+56*s**3-28*s*s-56*s)*t**4/384
            ratio=mp.mpf(I[n-s])/I[n]*mp.mpf(n)**(mp.mpf(s)/2)
            c0=-mp.mpf(1)/4-mp.log(2)/2
            L=mp.log(I[n])-c0
            x=2*L/mp.lambertw(2*L/mp.e); ell=mp.log(x)
            inv=x-2*mp.sqrt(x)/ell+2/ell**2-2/ell**3-(mp.mpf(7)/(12*ell)+1/ell**3-mp.mpf(14)/(3*ell**4)+4/ell**5)/mp.sqrt(x)
            rows.append({'n':n,'involution_scaled_residuals_by_order':residuals,
                         'shift3_scaled_residual_order4':shown((ratio-approx)/t**5),
                         'centered_involution_inverse_error':shown(inv-n),
                         'scaled_inverse_error':shown((inv-n)*x*ell)})
        return {'scope':'Floating-point diagnostics only; not directed intervals, exact receipts, finite-n onset bounds, or inverse-rounding certificates.',
                'precision':100,'product_cutoff':J,'C':shown(C),
                'H':{str(k):shown(v) for k,v in ((3,H3),(4,H4),(5,H5),(6,H6))},
                'low_kostka_ratios':low,'involution_checks':rows}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    emit(diagnostics())

if __name__=='__main__':
    try:
        main()
    except (ValueError,RuntimeError,OSError,ArithmeticError) as exc:
        raise SystemExit(str(exc))
