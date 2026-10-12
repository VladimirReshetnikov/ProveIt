#!/usr/bin/env python3
"""Direct Lambert sums versus Mellin contour transport, plus exact jet algebra."""
from pathlib import Path
import json
import mpmath as mp
import sympy as sp


def lambert(s,tau):
    return mp.fsum(mp.power(k,s-1)/mp.expm1(tau*k) for k in range(1,180))


def residue(s,tau,center):
    base=mp.zeta(2-s)/tau+mp.gamma(s)*mp.zeta(s)*mp.power(tau,-s)-mp.zeta(1-s)/2
    if center <= 0:
        M=-center//2
        base += mp.fsum(mp.bernoulli(2*j)/mp.factorial(2*j)*mp.zeta(2-2*j-s)*tau**(2*j-1) for j in range(1,M+2))
    return base


def transformed(s,tau):
    dual=4*mp.pi**2/tau
    def fun(t):
        w=mp.mpf('1.5')+1j*t
        return mp.gamma(w)*mp.zeta(w)*mp.zeta(w+1-s)*mp.cos(mp.pi*w/2)/mp.cos(mp.pi*(s-w)/2)*mp.power(dual,-w)
    # All test parameters are real, so conjugation halves the contour.
    value=mp.quad(lambda t: mp.re(fun(t)),[0,1,3,7,15,30,55,80])/mp.pi
    return mp.power(2*mp.pi/tau,s)*value


def main():
    mp.mp.dps=42
    rows=[]
    for center,delta,tau in [(0,'.13','3.1'),(-2,'-.11','4.3'),(-4,'.09','5.7'),(1,'.08','2.9')]:
        s=mp.mpf(center)+mp.mpf(delta); tau=mp.mpf(tau)
        lhs=lambert(s,tau); rhs=residue(s,tau,center)+transformed(s,tau)
        error=abs(lhs-rhs)
        assert error < mp.mpf('1e-29'), (center,error)
        rows.append({'center':center,'s':str(s),'tau':str(tau),'lhs':mp.nstr(lhs,35),'absolute_error':mp.nstr(error,8)})
        print('modular',center,mp.nstr(error,8),flush=True)
    # Known eta and Ramanujan specializations are independent boundary checks.
    tau=mp.mpf('3.7'); dual=4*mp.pi**2/tau
    eta_rhs=mp.zeta(2)/tau+mp.log(tau/(2*mp.pi))/2-tau/24+lambert(0,dual)
    assert abs(lambert(0,tau)-eta_rhs)<mp.mpf('1e-38')
    z3_rhs=mp.zeta(4)/tau-mp.zeta(3)/2*(1+(tau/(2*mp.pi))**2)+mp.zeta(2)*tau/12+tau**3/1440-(tau/(2*mp.pi))**2*lambert(-2,dual)
    assert abs(lambert(-2,tau)-z3_rhs)<mp.mpf('1e-38')

    # A new self-dual contour value, evaluated independently of the transport.
    def self_dual_integrand(t):
        w=mp.mpf('1.5')+1j*t
        return mp.gamma(w)*mp.zeta(w)*mp.zeta(w+1)*mp.tan(mp.pi*w/2)*(2*mp.pi)**(-w)
    contour_value=mp.quad(lambda t:mp.re(self_dual_integrand(t)),[0,1,3,7,15,30,55,80])/mp.pi
    closed_value=-mp.diff(mp.zeta,2)/mp.pi**2-mp.pi/8+mp.log(2*mp.pi)/6
    self_dual_error=abs(contour_value-closed_value)
    assert self_dual_error < mp.mpf('1e-35')

    x,u=sp.symbols('x u')
    p=sp.Integer(1); exact=0
    for j in range(9):
        direct=sp.series(1/(sp.cos(u)+x*sp.sin(u)),u,0,j+1).removeO().expand().coeff(u,j)*sp.factorial(j)
        assert sp.expand(p-direct)==0
        p=sp.expand(-(1+x*x)*sp.diff(p,x)-x*p); exact+=1
    out={'status':'passed','precision_digits':mp.mp.dps,'exact_kernel_assertions':exact,'classical_boundary_checks':2,'numerical_contour_comparisons':rows,'self_dual_contour':{'value':mp.nstr(contour_value,35),'absolute_error':mp.nstr(self_dual_error,10)},'contour_height':80,'note':'Floating-point diagnostics; no interval error certificate is claimed.'}
    dest=Path(__file__).resolve().parents[1]/'results'/'modular_transport.json'
    dest.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':'passed','exact_kernel_assertions':exact,'numerical_comparisons':len(rows)+3}))


if __name__=='__main__': main()
