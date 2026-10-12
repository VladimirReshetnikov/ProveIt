"""Reproduce a superseded diagnostic; discrepancies here are NOT theorem failures.

mpmath 1.3.0, 55 digits: very small order perturbations near integer orders
inside polylog do not yield the demanded derivative accuracy for these inputs.
Use verify_special.py's step-refined evaluation for the passing diagnostic.
"""
import mpmath as mp
mp.mp.dps=55
for m,a in [(2,(1+1/mp.sqrt(3))/2),(2,(1-1/mp.sqrt(3))/2),(3,mp.mpf('.5'))]:
    z=mp.exp(2j*mp.pi*a);zb=mp.conj(z)
    old=(mp.exp(-1j*mp.pi*m/2)*(mp.diff(lambda s:mp.polylog(s,z),m)-1j*mp.pi/2*mp.polylog(m,z))
         +mp.exp(1j*mp.pi*m/2)*(mp.diff(lambda s:mp.polylog(s,zb),m)+1j*mp.pi/2*mp.polylog(m,zb)))
    lhs=(-1)**m*mp.factorial(m-1)/(2*mp.pi)**m*old
    rhs=(-1)**(m-1)*mp.diff(lambda s:mp.zeta(s,a),1-m)
    print('m=',m,'a=',mp.nstr(a,12),'superseded absolute residual=',mp.nstr(abs(lhs-rhs),12))
