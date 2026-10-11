#!/usr/bin/env python3
"""Independent exact audit and numerical diagnostics for one-sided jets.

The symbolic checks are exact identities. Numerical comparisons are ordinary
high-precision diagnostics, not proofs, rigorous error bounds, or interval
certificates. No companion verifier is imported. Run with Python, SymPy, and
mpmath; the complete results are written beside this file as verification.json.
"""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from math import factorial
from pathlib import Path
import json
import mpmath as mp
import sympy as sp

mp.mp.dps = 85
N = 12
Q = 64
SPECTRAL_N = 11
SPECTRAL_Q = 72
TOL = mp.mpf("1e-60")


def mm(v):
    return mp.mpf(v.numerator) / v.denominator if isinstance(v, F) else mp.mpf(v)


def exact_checks():
    counts = Counter()
    s, B, C, b, x, r, t, u = sp.symbols("s B C b x r t u", positive=True)
    delta = B-C

    def check(category, lhs, rhs=0):
        residual = sp.cancel(sp.expand(lhs-rhs))
        if residual != 0:
            residual = sp.simplify(residual)
        assert residual == 0, (category, residual)
        counts[category] += 1

    def h(k):
        return sp.expand((-1)**k * (
            sp.rf(2*s, k)*(B**k+C**k)/(2*sp.factorial(k))
            - sum(sp.rf(s, j)*sp.rf(s, k-j)*B**j*C**(k-j)
                  /(sp.factorial(j)*sp.factorial(k-j)) for j in range(k+1))))

    for k in range(9):
        hk = h(k)
        check("quadratic_coefficients", hk.subs(s, 0))
        check("quadratic_coefficients", sp.diff(hk, s).subs(s, 0))
        check("quadratic_coefficients", sp.diff(hk, s, k+1))
        if k < 2:
            check("quadratic_coefficients", hk)
    check("quadratic_coefficients", h(2), delta**2*s**2/2)
    check("quadratic_coefficients", sp.diff(h(3), s, 2).subs(s, 0), -delta**2*(B+C))
    check("quadratic_coefficients", sp.diff(h(3), s, 3).subs(s, 0), -3*delta**2*(B+C))

    # Compare the finite Pochhammer expression with an independently expanded
    # exponential of logarithm series, for symbolic masses and all spectral jets.
    logs = [sum((-1)**(j+1)*mass**j*t**j/sp.Integer(j) for j in range(1, 7))
            for mass in (B, C)]
    for m in range(2, 7):
        raw = sp.Poly(sp.expand(((-2)**m*(logs[0]**m+logs[1]**m)/2
                                -(-1)**m*(logs[0]+logs[1])**m)), t)
        for k in range(2, 7):
            check("independent_log_coefficient_jets", raw.coeff_monomial(t**k),
                  sp.diff(h(k), s, m).subs(s, 0))

    for rr in (2, 3, 4, 5):
        masses = sp.symbols("B0:"+str(rr))
        hk2 = (sp.rf(rr*s, 2)*sum(z*z for z in masses)/(2*rr)
               - sp.rf(s, 2)*sum(z*z for z in masses)/2
               - s*s*sum(masses[i]*masses[j] for i in range(rr) for j in range(i+1, rr)))
        variance = sum((masses[i]-masses[j])**2 for i in range(rr) for j in range(i+1, rr))
        check("general_mass_variance", hk2, variance*s*s/2)

    # The arbitrary positive slope rho covers 2r for quadratic products and 2
    # for a conjugate linear pair. Retaining m+1 is essential at a pole.
    rho = sp.symbols("rho", nonzero=True)
    for m in range(1, 9):
        As = sp.symbols("A0:"+str(m+2))
        gs = sp.symbols("g0:"+str(max(m-1, 1)))
        zs = sp.symbols("z0:"+str(m+1))
        hp = sum(As[j]*s**j/sp.factorial(j) for j in range(2, m+2))
        laurent = 1/(rho*s)+sum((-1)**ell*gs[ell]*(rho*s)**ell/sp.factorial(ell)
                               for ell in range(max(m-1, 0)))
        actual = sp.expand(hp*laurent).coeff(s, m)*sp.factorial(m)
        expected = As[m+1]/(rho*(m+1)) + sum(
            sp.binomial(m,j)*As[j]*(-rho)**(m-j)*gs[m-j] for j in range(2,m+1))
        check("resonant_Laurent_formula", actual, expected)
        regular = sum(zs[ell]*(rho*s)**ell/sp.factorial(ell) for ell in range(m+1))
        expected_regular = sum(sp.binomial(m,j)*As[j]*rho**(m-j)*zs[m-j]
                               for j in range(2,m+1))
        check("regular_product_formula", sp.expand(hp*regular).coeff(s,m)*sp.factorial(m),
              expected_regular)

    L, M, X = sp.symbols("L M X")
    check("explicit_signs", 2*(L**2+M**2)-(L+M)**2, (L-M)**2)
    check("explicit_signs", -(4*(L**3+M**3)-(L+M)**3), -3*(L+M)*(L-M)**2)
    dl = sum((-1)**(j+1)*(B**j-C**j)*t**j/sp.Integer(j) for j in range(1,7))
    square = sp.Poly(sp.expand(dl**2), t)
    check("explicit_signs", square.coeff_monomial(t**2), delta**2)
    check("explicit_signs", square.coeff_monomial(t**3), -delta**2*(B+C))
    check("explicit_signs", sp.diff(h(3),s,3).subs(s,0)/12, -delta**2*(B+C)/4)
    for m in range(2,9):
        um = sum(sp.binomial(m,j)*sp.diff(h(2),s,j).subs(s,0)*(-4*X)**(m-j)
                 for j in range(2,m+1))
        check("single_Stieltjes_coefficient", um,
              sp.binomial(m,2)*(-4)**(m-2)*delta**2*X**(m-2))

    # Exact rational partial fraction identity, followed by the constant
    # cancellation that produces (f(u)-f(t))/(t-u).
    check("digamma_kernel", x**3/((x*x+u)*(x*x+t))-1/x,
          (t*(x/(x*x+t)-1/x)-u*(x/(x*x+u)-1/x))/(t-u))
    p, Rt, Ru = sp.symbols("p Rt Ru")
    check("digamma_kernel", (t*(p-Rt)-u*(p-Ru))/(t-u)-p,
          (u*Ru-t*Rt)/(t-u))

    y = sp.symbols("y", positive=True)
    eps = sp.symbols("eps", positive=True)
    J2 = -y*sp.log(y)**2/(y-1)-2*sp.polylog(2,1-y)
    J3 = (-sp.log(y)**2/(2*(y-1)**2)+sp.log(y)**2/2+sp.polylog(2,1-y)
          -sp.log(y)/(y-1)+sp.log(y-1)-sp.log(y))
    for name, J, power in (("J2", J2, 2), ("J3", J3, 3)):
        deriv = sp.diff(J,y).subs(sp.polylog(1,1-y), -sp.log(y))
        check("dilogarithm_derivatives", deriv, sp.log(y)**2/(y-1)**power)
    J2series = sp.series(J2.subs(y,1+eps),eps,0,3).removeO().expand()
    J3series = sp.series(J3.subs(y,1+eps),eps,0,3).removeO().expand()
    check("primitive_normalization", J2series.coeff(eps,0))
    check("primitive_normalization", (J3series-sp.log(eps)).coeff(eps,0), -sp.Rational(3,2))
    dd = sp.symbols("delta", positive=True)
    yy = 1+dd/(x*x+C)
    # Keep log(y)^2 formal to make the chain-rule coefficient transparent.
    check("primitive_chain_rule", (-dd**2/(2*(yy-1)**3)+C*dd/(2*(yy-1)**2))*sp.diff(yy,x), x**3)
    # log x = (log(delta)-log(eps)+log(1-C*eps/delta))/2.
    phi_eps = (-dd**2*J3series/2+C*dd*J2series/2
               -dd**2*(sp.log(dd)-sp.log(eps)+sp.log(1-C*eps/dd))/2
               +dd**2*sp.log(dd)/2-3*dd**2/4)
    phi_series = sp.series(phi_eps,eps,0,2).removeO().expand()
    check("primitive_normalization", phi_series.coeff(eps,0))
    check("primitive_normalization", phi_series.coeff(eps,1)*dd,
          dd**2*(dd+2*C)/2)

    for n in range(8):
        g = sp.symbols("g")
        coeff = sp.factorial(n+1)*(-1)**(n+1)*g/sp.factorial(n)
        check("Stieltjes_anchored_primitive", (-1)**(n+1)*coeff/(n+1), g)

    for k in range(1,9):
        eta = sp.expand((-1)**k*b**(2*k)*(sp.rf(2*s,2*k)/sp.factorial(2*k)
                                         -sp.rf(s,k)/sp.factorial(k)))
        check("conjugate_linear_coefficients", eta.subs(s,0))
        check("conjugate_linear_coefficients", sp.diff(eta,s).subs(s,0))
        # This independent complex-binomial computation checks even-term sign.
        from_factors = ((-1)**(2*k)*(sp.I*b)**(2*k)*sp.rf(2*s,2*k)/sp.factorial(2*k)
                        -(-1)**k*b**(2*k)*sp.rf(s,k)/sp.factorial(k))
        check("conjugate_linear_coefficients", eta, from_factors)
        if k==1:
            check("conjugate_linear_coefficients", eta, -2*b*b*s*s)
    theta, v = sp.symbols("theta v", real=True)
    check("conjugate_linear_signs", 2*((v+sp.I*theta)**2+(v-sp.I*theta)**2)-(2*v)**2,
          -4*theta**2)
    check("conjugate_linear_signs", -4*b*b/(2*2), -b*b)
    z = sp.symbols("z")
    for d in range(9):
        check("finite_Hurwitz_binomial_identity",
              sum(sp.binomial(d,j)*(-z)**(d-j)*(x+z)**j for j in range(d+1)),x**d)
    return {"total":sum(counts.values()), "by_category":dict(counts)}


@lru_cache(maxsize=None)
def factor_coeffs(mass, max_power, jet):
    """Pochhammer coefficients via a rational recurrence, not the h formula."""
    out = [[F(0)]*(jet+1) for _ in range(max_power+1)]
    out[0][0] = F(1)
    for q in range(1,max_power+1):
        for j in range(jet+1):
            out[q][j] = -mass/F(q)*((q-1)*out[q-1][j]+(out[q-1][j-1] if j else 0))
    return tuple(tuple(row) for row in out)


@lru_cache(maxsize=None)
def product_coeffs(masses,max_power,jet):
    out = [[F(0)]*(jet+1) for _ in range(max_power+1)]
    out[0][0] = F(1)
    for mass in masses:
        fac = factor_coeffs(mass,max_power,jet)
        out = [[sum(out[v][ell]*fac[q-v][j-ell]
                    for v in range(q+1) for ell in range(j+1))
                for j in range(jet+1)] for q in range(max_power+1)]
    return out


@lru_cache(maxsize=None)
def zeta_derivative(nu,a,cut,order):
    return mp.zeta(nu,mm(a)+cut,derivative=order)


@lru_cache(maxsize=None)
def gamma_shift(order,a,cut):
    value = -mp.digamma(mm(a)) if order==0 else mp.stieltjes(order,mm(a))
    return value-mp.fsum(mp.log(n+mm(a))**order/(n+mm(a)) for n in range(cut))


def continued_tail_term(coeff,nu,slope,a,m,cut):
    if nu==1:
        assert coeff[0]==0
        return factorial(m)*(mm(coeff[m+1])/slope + mp.fsum(
            mm(coeff[j])*(-slope)**(m-j)*gamma_shift(m-j,a,cut)/factorial(m-j)
            for j in range(1,m+1) if coeff[j]))
    return factorial(m)*mp.fsum(
        mm(coeff[j])*slope**(m-j)*zeta_derivative(nu,a,cut,m-j)/factorial(m-j)
        for j in range(m+1) if coeff[j])


def spectral_jet(d,masses,a,m,cut=SPECTRAL_N,terms=SPECTRAL_Q):
    """Continue each individual spectrum before taking its normalized defect."""
    cc = product_coeffs(tuple(masses),terms,m+1)
    head = mp.fsum((n+mm(a))**d*(-mp.fsum(mp.log((n+mm(a))**2+mm(B))
                                               for B in masses))**m for n in range(cut))
    return head+mp.fsum(continued_tail_term(cc[q],2*q-d,2*len(masses),a,m,cut)
                       for q in range(terms+1))


@lru_cache(maxsize=None)
def direct_log_square_coeffs(B,C,terms):
    aa = [F(0)]+[(-1)**(j+1)*(B**j-C**j)/F(j) for j in range(1,terms+1)]
    ss = [F(0)]+[(-1)**(j+1)*(B**j+C**j)/F(j) for j in range(1,terms+1)]
    square = [sum(aa[j]*aa[q-j] for j in range(q+1)) for q in range(terms+1)]
    cubic = [sum(ss[j]*square[q-j] for j in range(q+1)) for q in range(terms+1)]
    return square,cubic


def ordinary_jet(d,B,C,a,m,cut=N,terms=Q):
    delta = mm(B-C)
    sq,cb = direct_log_square_coeffs(B,C,terms)
    if m==2:
        k = (d+1)//2
        def summand(n):
            x=n+mm(a)
            ll=mp.log1p(delta/(x*x+mm(C)))
            return x**d*ll*ll-mp.fsum(mm(sq[q])*x**(d-2*q) for q in range(2,k+1))
        ordinary = mp.fsum(summand(n) for n in range(cut)) + mp.fsum(
            mm(sq[q])*zeta_derivative(2*q-d,a,cut,0) for q in range(k+1,terms+1))
        if d==3:
            correction = -delta**2*mp.digamma(mm(a))
        elif d==5:
            correction = (delta**2*mp.zeta(-1,mm(a))-delta**2*mm(B+C)*gamma_shift(0,a,0)
                          -delta**2*mm(B+C)/4)
        else:
            raise ValueError(d)
    elif m==3 and d==3:
        def summand(n):
            x=n+mm(a)
            ll=mp.log1p(delta/(x*x+mm(C)))
            total=4*mp.log(x)+mp.log1p(mm(B)/(x*x))+mp.log1p(mm(C)/(x*x))
            return -3*x**3*total*ll**2+12*delta**2*mp.log(x)/x
        ordinary=mp.fsum(summand(n) for n in range(cut))+mp.fsum(
            12*mm(sq[q])*zeta_derivative(2*q-3,a,cut,1)
            -3*mm(cb[q])*zeta_derivative(2*q-3,a,cut,0) for q in range(3,terms+1))
        correction=-12*delta**2*gamma_shift(1,a,0)
    else:
        raise ValueError((d,m))
    return ordinary,correction


def antisymmetric_integral(fun,B,C):
    lo,hi=mm(C),mm(B)
    span=hi-lo
    return 2*span*mp.quad(lambda u:(fun(lo+span*u)-fun(hi-span*u))*mp.log((1-u)/u),
                         [0,mp.mpf("0.125"),mp.mpf("0.5")])


def digamma_integral(B,C,a):
    return antisymmetric_integral(lambda t:t*mp.re(mp.digamma(mm(a)+1j*mp.sqrt(t))),B,C)


def phi(x,B,C):
    delta=mm(B-C)
    y=1+delta/(x*x+mm(C))
    logy=mp.log(y)
    j2=-y*logy**2/(y-1)-2*mp.polylog(2,1-y)
    j3=(-logy**2/(2*(y-1)**2)+logy**2/2+mp.polylog(2,1-y)
        -logy/(y-1)+mp.log(y-1)-logy)
    return (-delta**2*j3/2+mm(C)*delta*j2/2-delta**2*mp.log(x)
            +delta**2*mp.log(delta)/2-3*delta**2/4)


def phi_sum(B,C,a,cut=N,terms=Q):
    # The head uses the proposed dilogarithmic expression. Its convergent tail
    # comes independently from integrating the elementary log-square series.
    sq,_=direct_log_square_coeffs(B,C,terms)
    return mp.fsum(phi(n+mm(a),B,C) for n in range(cut))+mp.fsum(
        mm(sq[q])/F(4-2*q)*zeta_derivative(2*q-4,a,cut,0) for q in range(3,terms+1))


def linear_real_jet(b,a,m,cut=SPECTRAL_N,terms=2*SPECTRAL_Q):
    cc=factor_coeffs(b,terms,m+1)
    head=mp.fsum(mp.re((n+mm(a))*(-mp.log(n+mm(a)+1j*mm(b)))**m) for n in range(cut))
    return head+mp.fsum(continued_tail_term(
        tuple((-1)**(q//2)*v for v in cc[q]),q-1,1,a,m,cut) for q in range(0,terms+1,2))


def linear_ordinary(b,a,cut=N,terms=Q):
    head=mp.fsum(-4*(n+mm(a))*mp.atan(mm(b)/(n+mm(a)))**2+4*mm(b)**2/(n+mm(a))
                 for n in range(cut))
    tail=mp.fsum(-4*mm((-1)**(q-1)*b**(2*q)*sum(
        F(1,(2*j+1)*(2*(q-1-j)+1)) for j in range(q)))
                *zeta_derivative(2*q-1,a,cut,0) for q in range(2,terms+1))
    return head+tail+4*mm(b)**2*mp.digamma(mm(a))


def ns(value,digits=60):
    return mp.nstr(value,digits)


def main():
    out={"precision_digits":mp.mp.dps,"ordinary_head_terms":N,"ordinary_tail_coefficients":Q,
         "spectral_head_terms":SPECTRAL_N,"spectral_tail_coefficients":SPECTRAL_Q,
         "comparison_tolerance":str(TOL),
         "interpretation":"Exact checks are symbolic identities. Numerical diagnostics are not proofs or interval certificates.",
         "exact_sympy_checks":exact_checks(),"spectral_checks":[],"primitive_checks":[],"linear_checks":[]}
    print("Exact SymPy checks:",out["exact_sympy_checks"],flush=True)
    errors=[]
    families=[("positive_masses",F(5,2),F(1,3),F(2,5)),
              ("zero_mass_large_ratio",F(9),F(0),F(1,3))]
    for name,B,C,a in families:
        for d,m in ((3,1),(3,2),(3,3),(5,2)):
            spectral=2**(m-1)*(spectral_jet(d,[B],a,m)+spectral_jet(d,[C],a,m))-spectral_jet(d,[B,C],a,m)
            if m==1:
                ordinary,correction=mp.mpf(0),mm(B-C)**2/8
            else:
                ordinary,correction=ordinary_jet(d,B,C,a,m)
            error=abs(spectral-ordinary-correction)
            row={"name":name,"weight_degree":d,"derivative_order":m,"a":str(a),"B":str(B),"C":str(C),
                 "spectral_defect":ns(spectral),"ordinary_remainder":ns(ordinary),"finite_correction":ns(correction),
                 "absolute_difference":ns(error,10)}
            assert error<TOL,row
            errors.append(error)
            if d==3 and m==2:
                integral=digamma_integral(B,C,a)
                integral_error=abs(integral-ordinary-correction)
                row["digamma_integral"]=ns(integral)
                row["digamma_absolute_difference"]=ns(integral_error,10)
                assert integral_error<TOL,row
                errors.append(integral_error)
            out["spectral_checks"].append(row)
            print("Completed",name,"d",d,"m",m,"error",ns(error,6),flush=True)

    primitive_cases=[(F(5,2),F(1,3),F(7,5),F(2,5)),(F(9),F(0),F(1,3),F(5,4))]
    for B,C,a,a0 in primitive_cases:
        series=(phi_sum(B,C,a)-phi_sum(B,C,a0)-mm(B-C)**2*(mp.loggamma(mm(a))-mp.loggamma(mm(a0))))
        # Integrate the independent digamma representation in the shift first;
        # only complex Gamma functions occur here, with no dilogarithms.
        integral=antisymmetric_integral(lambda t:t*mp.re(
            mp.loggamma(mm(a)+1j*mp.sqrt(t))-mp.loggamma(mm(a0)+1j*mp.sqrt(t))),B,C)
        error=abs(series-integral)
        row={"a":str(a),"a0":str(a0),"B":str(B),"C":str(C),
             "dilogarithm_Gamma_series":ns(series),"integrated_digamma_Gamma_quadrature":ns(integral),
             "absolute_difference":ns(error,10)}
        assert error<TOL,row
        errors.append(error)
        derivative_errors=[]
        for xx in (mp.mpf("0.2"),mp.mpf("1.7"),mp.mpf("19")):
            expected=xx**3*mp.log1p(mm(B-C)/(xx*xx+mm(C)))**2-mm(B-C)**2/xx
            derr=abs(mp.diff(lambda z:phi(z,B,C),xx)-expected)
            assert derr<TOL,(row,xx,derr)
            derivative_errors.append(derr)
            errors.append(derr)
        row["maximum_phi_derivative_difference"]=ns(max(derivative_errors),10)
        # The chosen constant yields Phi(x) ~ delta^2(B+C)/(2x^2).
        xx=mp.mpf("1e10")
        leading=mm(B-C)**2*mm(B+C)/2
        row["x_squared_Phi_at_1e10"]=ns(xx*xx*phi(xx,B,C),40)
        row["predicted_x_squared_Phi_limit"]=ns(leading,40)
        assert abs(xx*xx*phi(xx,B,C)-leading)<mp.mpf("1e-14")
        out["primitive_checks"].append(row)
        print("Completed primitive",str(a0),"to",str(a),"error",ns(error,6),flush=True)

    b,a=F(3,2),F(2,5)
    for m in (1,2):
        real_linear=linear_real_jet(b,a,m)
        spectral=2**m*real_linear-spectral_jet(1,[b*b],a,m)
        expected=-mm(b)**2 if m==1 else linear_ordinary(b,a)
        error=abs(spectral-expected)
        row={"b":str(b),"a":str(a),"derivative_order":m,"independent_linear_spectral_defect":ns(spectral),
             "stated_formula":ns(expected),"absolute_difference":ns(error,10)}
        assert error<TOL,row
        errors.append(error)
        shifted=mm(a)+1j*mm(b)
        closed_real=mp.re(mp.zeta(-1,shifted,derivative=m)
                         -1j*mm(b)*mp.zeta(0,shifted,derivative=m))
        finite_error=abs(real_linear-closed_real)
        assert finite_error<TOL,row
        errors.append(finite_error)
        row["real_linear_jet_finite_Hurwitz"]=ns(closed_real)
        row["finite_Hurwitz_absolute_difference"]=ns(finite_error,10)
        out["linear_checks"].append(row)
        print("Completed conjugate linear m",m,"error",ns(error,6),flush=True)
    out["numerical_comparisons_below_tolerance"]=len(errors)
    out["maximum_absolute_difference"]=ns(max(errors),10)
    out["all_checks_passed"]=True
    path=Path(__file__).with_name("verification.json")
    path.write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps(out,indent=2),flush=True)


if __name__=="__main__":
    main()
