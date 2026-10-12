#!/usr/bin/env python3
"""Exact contact-polynomial checks and independent finite lattice diagnostics.

The exact tests compare two coefficient constructions. Numerical cutoff tests
use finite sums of powers, not the Bernoulli-polynomial formula under test.
No floating-point result here is an interval certificate.
"""
from pathlib import Path
import json
import sympy as sp
import mpmath as mp


def main():
    u, x = sp.symbols('u x')
    assertions = 0
    for N in (0, 2, 4, 6, 8, 10):
        A = sp.prod(1-u/j for j in range(1, N+1))
        sinc_poly = sum((-1)**j*(sp.pi*u/2)**(2*j)/sp.factorial(2*j+1) for j in range(5))
        exp_poly = sum((-x*u)**j/sp.factorial(j) for j in range(9))
        direct = sp.expand(A*sinc_poly*exp_poly)
        exponent = -(x+sp.harmonic(N))*u
        exponent -= sum((sp.harmonic(N, r)+(sp.Rational(2)**(1-r)*sp.zeta(r) if r % 2 == 0 else 0))*u**r/r for r in range(2, 9))
        exponent = sp.expand(exponent)
        bell_coeff = [sp.Integer(1)]
        for n in range(1,9):
            bell_coeff.append(sp.expand(sum(r*exponent.coeff(u,r)*bell_coeff[n-r] for r in range(1,n+1))/n))
        bell = sum(bell_coeff[n]*u**n for n in range(9))
        for d in range(1, 10):
            assert sp.simplify(direct.coeff(u,d-1)-bell.coeff(u,d-1)) == 0
            assertions += 1
        b = sp.bernoulli(N+2)/sp.factorial(N+2)
        assert sp.expand(b*sp.rf(-N+u,N+1)-sp.bernoulli(N+2)*u*A/((N+1)*(N+2))) == 0
        assertions += 1

    mp.mp.dps = 55
    records = []
    a, h = mp.mpf('0.73'), mp.mpf('1.4')
    tau = 2*mp.pi/h
    z = mp.exp(-tau*a)
    # Work at nonzero real/complex u, where every component is directly defined.
    for eps in (mp.mpf('.12'), mp.mpf('-.08'), mp.mpc('.07','.04')):
        analytic = tau**(1+eps)*mp.rgamma(1+eps)*mp.polylog(-eps,z)
        errors=[]
        for K in (80, 160, 320):
            finite = mp.fsum((a+1j*h*n)**(-1-eps) for n in range(-K,K+1))
            contact = 2*mp.sin(mp.pi*eps/2)/(h*eps)*(h*K)**(-eps)
            error=abs(finite-analytic-contact)
            errors.append(error)
            records.append({'kind':'finite_power_cutoff','u':str(eps),'K':K,'absolute_error':mp.nstr(error,15)})
        assert errors[-1] < errors[0]/2

    # Directly compare Taylor jets of the finite sum with the predicted contact.
    # Differentiating powers explicitly avoids numerical derivatives of the sum.
    for d in (1,2,3,4,5):
        N=2
        beta=mp.bernoulli(N+2)/((N+1)*(N+2))
        Fcoeff=[mp.mpf(0)]*(d+1)
        poly=sp.Poly(sp.prod(1-u/j for j in range(1,N+1)),u)
        for j in range(1,min(N+1,d)+1):
            Fcoeff[j]=beta*mp.mpf(str(poly.nth(j-1)))
        exact_jet=mp.diff(lambda v: (mp.bernoulli(N+2)/mp.factorial(N+2))*mp.rf(-N+v,N+1)*tau**(1+v)*mp.rgamma(1+v)*mp.polylog(-v,z),0,d)
        errs=[]
        for K in (60,120,240):
            sums=[]
            for r in range(d):
                sums.append(mp.fsum((-mp.log(a+1j*h*n))**r/(a+1j*h*n) for n in range(-K,K+1)))
            partial=mp.factorial(d)*sum(Fcoeff[j]*sums[d-j]/mp.factorial(d-j) for j in range(1,d+1))
            def correction(v):
                sinc = mp.sin(mp.pi*v/2)/(mp.pi*v/2) if v else mp.mpf(1)
                return tau*beta/2*v*mp.fprod(1-v/j for j in range(1,N+1))*sinc*mp.exp(-v*mp.log(h*K))
            cjet=mp.diff(correction,0,d)
            residual=partial-exact_jet-cjet
            err=abs(residual)
            def first_omitted(v):
                return -beta*v*(1-v)*(1-v/2)/(h*K)*mp.exp(-v*mp.log(h*K))*(mp.sin(mp.pi*v/2)+2*a/h*mp.cos(mp.pi*v/2))
            next_jet=mp.diff(first_omitted,0,d)
            corrected=abs(residual-next_jet)
            # The leading error polynomial can cross zero, so its absolute
            # value need not decrease monotonically. Check its independently
            # derived next Euler--Maclaurin coefficient instead.
            def second_omitted(v):
                return beta*v*(1-v)*(1-v/2)*(1+v)/(h*K**2)*mp.exp(-v*mp.log(h*K))*((mp.mpf(1)/6-a*a/(h*h))*mp.sin(mp.pi*v/2)+a/h*mp.cos(mp.pi*v/2))
            second_jet=mp.diff(second_omitted,0,d)
            corrected_twice=abs(residual-next_jet-second_jet)
            assert corrected_twice < abs(second_jet)/10
            errs.append(err)
            records.append({'kind':'contact_jet','N':N,'d':d,'K':K,'absolute_error':mp.nstr(err,15),'after_next_term':mp.nstr(corrected,15),'after_second_term':mp.nstr(corrected_twice,15)})

    # A zero-mean Fourier filter has no contact; an Abel sum gives the target.
    for d in (1,2,3):
        target=mp.diff(lambda v: tau**(1+v)*mp.rgamma(1+v)*(2**(-v)*mp.polylog(-v,mp.sqrt(z))-mp.polylog(-v,z)),0,d-1)
        # 2*(spacing 2h lattice)-spacing h lattice for powers.
        errs=[]
        for K in (80,160,320):
            partial=mp.fsum((-1)**n*(-mp.log(a+1j*h*n))**(d-1)/(a+1j*h*n) for n in range(-K,K+1))
            errs.append(abs(partial-target))
        assert errs[-1] < errs[0]
        records.append({'kind':'alternating_no_contact','d':d,'K':320,'absolute_error':mp.nstr(errs[-1],15)})

    # Mutation controls: omitting sinc loses the cubic finite contact; replacing
    # H_N by -H_N loses the quadratic contact for N>0.
    assert sp.expand(sp.series(sp.sin(sp.pi*u/2)/(sp.pi*u/2),u,0,4).removeO()).coeff(u,2) == -sp.pi**2/24
    assert sp.harmonic(2) != -sp.harmonic(2)
    output={'exact_assertions':assertions,'mutation_controls':2,'numerical_diagnostics':records,'status':'passed','precision_digits':mp.mp.dps}
    out=Path(__file__).resolve().parents[1]/'results'/'lattice_contacts.json'
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({'status':'passed','exact_assertions':assertions,'numerical_diagnostics':len(records),'mutation_controls':2}))


if __name__ == '__main__':
    main()
