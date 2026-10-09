#!/usr/bin/env python3
"""Deterministic checks. Passing them is not a formal proof of asymptotics."""
from __future__ import annotations
import json
import time
from fractions import Fraction
from pathlib import Path
import mpmath as mp
import sympy as sp
from coefficients import saddle_coefficients, laplace_polynomials
from moments import (geometric_stats, geometric_moments, geometric_moments_exact,
                     finite_stats, finite_moment_exact, equal_weight_moment_exact,
                     solve_saddle, first_correction, log_saddle_carrier,
                     raw_moments_from_cumulants)


def run() -> dict:
    mp.mp.dps = 70
    checks: list[dict] = []
    def check(name, condition, detail=""):
        if not bool(condition):
            raise AssertionError(f"{name}: {detail}")
        checks.append({"name":name,"passed":True,"detail":str(detail)})
    started = time.time()
    rho, b, c = saddle_coefficients(3)
    expected = (sp.Rational(1,12)-1/(1+rho)+(b[3]/2+b[4]/8)/(1+rho)**2
                -5*b[3]**2/(24*(1+rho)**3))
    check("first_saddle_coefficient", sp.cancel(c[1]-expected)==0)
    for j in range(1,4):
        check(f"deterministic_cancellation_C{j}",
              sp.simplify(c[j].subs({rho:0,**{b[r]:sp.factorial(r-1) for r in b}}))==0)
    gammasub={b[r]:sp.factorial(r-1)*(1+rho) for r in b}
    check("gamma_calibration_C1",sp.simplify(c[1].subs(gammasub)-rho/(12*(1+rho)))==0)
    check("gamma_calibration_C2",sp.simplify(c[2].subs(gammasub)-rho**2/(288*(1+rho)**2))==0)
    gamma3=-rho*(139*rho**2+432*rho+432)/(51840*(1+rho)**3)
    check("gamma_calibration_C3",sp.simplify(c[3].subs(gammasub)-gamma3)==0)
    origin={rho:0,**{b[r]:sp.factorial(r-1) for r in b}}
    for var, target in [(rho,0),(b[3],0),(b[4],-sp.Rational(1,4)),
                        (b[5],sp.Rational(1,6)),(b[6],-sp.Rational(1,48))]:
        check(f"C2_gradient_{var}", sp.simplify(sp.diff(c[2],var).subs(origin)-target)==0)
    check("C3_gamma_linear",sp.diff(gamma3,rho).subs(rho,0)==-sp.Rational(1,120))
    v,k3,k4,n=sp.symbols('v k3 k4 n',positive=True)
    delta=(k4/(8*(n+v)**2)-5*k3**2/(24*(n+v)**3)
           -k3*(2*n-3*v)/(6*(n+v)**3)-3*v**2/(4*n*(n+v)**2)
           +5*v**3/(6*n*(n+v)**3))
    check("first_correction_two_forms",sp.cancel(c[1].subs({rho:v/n,b[3]:2+k3/n,b[4]:6+k4/n})/n-delta)==0)
    y,p=laplace_polynomials(5)
    check("P1",p[1]==-y**2/2)
    check("P2",p[2]==y**4/8-y**3/3)
    check("P3",p[3]==-y**6/48+y**5/6-y**4/4)
    h=sp.Symbol('h')
    direct=sp.series(sp.exp(-sum(y**(j+1)*h**j/sp.Integer(j+1) for j in range(1,6))),h,0,6).removeO()
    for j in range(6):
        check(f"laplace_coefficient_order_{j}",sp.expand(direct.coeff(h,j)-p[j])==0)
    qf=Fraction(1,2)
    exact=geometric_moments_exact(18,qf)
    check("dyadic_moment_1",exact[1]==Fraction(1,2))
    check("dyadic_moment_2",exact[2]==Fraction(5,18))
    check("dyadic_moment_3",exact[3]==Fraction(1,6))
    check("Fabius_one_quarter",exact[2]/(2*2)==Fraction(5,72))
    check("Fabius_one_eighth",exact[3]/(8*6)==Fraction(1,288))
    for q0 in [Fraction(1,5),Fraction(1,2),Fraction(4,5)]:
        exact=geometric_moments_exact(20,q0)
        numeric=geometric_moments(20,mp.mpf(q0.numerator)/q0.denominator)
        for j in [0,1,2,5,10,20]:
            target=mp.mpf(exact[j].numerator)/exact[j].denominator
            check(f"positive_recurrence_q{q0}_n{j}",abs(numeric[j]/target-1)<mp.mpf('1e-60'))
    for m in [1,2,3,5]:
        for j in [0,1,2,5,10]:
            a=[Fraction(1,m)]*m
            check(f"equal_weights_exact_m{m}_n{j}",finite_moment_exact(j,a)==equal_weight_moment_exact(j,m))
    for q in [mp.mpf('.2'),mp.mpf('.5'),mp.mpf('.9'),mp.mpf('.999')]:
        for t in [mp.mpf(2),mp.mpf(37),mp.mpf(500)]:
            st=geometric_stats(t,q,6)
            check(f"variance_bound_q{q}_t{t}",0<st.cumulants[2]<=st.cumulants[1]<=t/2)
            A=t*(1-q);delta=-mp.log(q)
            H=mp.log(A/(-mp.expm1(-A)))
            hh=1-A/mp.expm1(A)
            vv=1-A**2*mp.exp(A)/mp.expm1(A)**2
            check(f"mesh_mean_q{q}_t{t}", -mp.mpf('1e-55')<=st.cumulants[1]-H/delta<=hh+mp.mpf('1e-55'))
            check(f"mesh_variance_q{q}_t{t}",-mp.mpf('1e-55')<=st.cumulants[2]-(H-hh)/delta<=vv+mp.mpf('1e-55'))
    q=mp.mpf('.5');t=mp.mpf(23)
    st=geometric_stats(t,q,6)
    def logL(z):
        # Independent direct product; finite truncation has absolute log error < 2^-310.
        return mp.fsum(mp.log(-mp.expm1(-z*mp.power(q,j+1))/(z*mp.power(q,j+1))) for j in range(310))
    check("geometric_product_tail",abs(st.log_laplace-logL(t))<mp.mpf('1e-60'))
    for r in range(1,5):
        target=(-t)**r*mp.diff(logL,t,r)
        check(f"cumulant_derivative_{r}",abs(st.cumulants[r]-target)<mp.mpf('1e-55'))
    for q0 in ['.25','.5','.85','.99']:
        q=mp.mpf(q0); n=128
        t,st=solve_saddle(n,lambda x:geometric_stats(x,q,6))
        check(f"saddle_residual_q{q0}",n<t<2*n and abs(t-st.cumulants[1]-n)<mp.mpf('1e-50'))
        exact=geometric_moments(n,q)[-1]
        A=mp.exp(log_saddle_carrier(n,t,st)); delta=first_correction(n,st)
        check(f"numerical_corrected_saddle_q{q0}",abs(exact/(A*(1+delta))-1)<mp.mpf('0.0001'))
        s0=geometric_stats(n,q,6)
        ratio=exact/mp.exp(s0.log_laplace)
        check(f"global_crossover_bound_q{q0}",abs(ratio-mp.exp(-s0.cumulants[1]**2/(2*n)))<=15/mp.sqrt(n))
    result={"passed":len(checks),"failed":0,"precision_decimal_digits":mp.mp.dps,
            "elapsed_seconds":round(time.time()-started,3),
            "status":"symbolic identities, exact rational tests, and high-precision numerical diagnostics; no Lean or interval proof",
            "checks":checks}
    out=Path(__file__).resolve().parents[1]/'data'/'validation.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='checks'},indent=2))
    return result

if __name__=='__main__':
    run()
