"""Independent exact and numerical diagnostics for the Mellin continuation.

Only this script's result JSON is written; source reports are never touched.
No numerical residual is used as an analytic proof.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp
import sympy as sp


def exact_checks():
    x, u, n = sp.symbols("x u n")
    c = {j: sp.Symbol(f"c{j}") for j in range(2, 9)}
    trigamma = x**-2 + sum((j-1)*c[j]*x**(j-2) for j in range(2, 9))
    claims = []
    for power, expected in [
        (2, {4: 1, 3: 0, 2: 2*c[2], 1: 4*c[3]}),
        (3, {6: 1, 5: 0, 4: 3*c[2], 3: 6*c[3],
             2: 9*c[4]+3*c[2]**2, 1: 12*c[5]+12*c[2]*c[3]}),
    ]:
        expanded = sp.expand(trigamma**power)
        for j, value in expected.items():
            got = expanded.coeff(x, -j)
            assert sp.expand(got-value) == 0
            claims.append(f"principal_part_power_{power}_pole_{j}")
        changes = {j: sp.expand(sp.sympify(value).subs(
            {c[k]: c[k]+n**-k for k in c}, simultaneous=True)-value)
                   for j, value in expected.items()}
        if power == 2:
            assert changes[1] == 4/n**3
            assert changes[2] == 2/n**2
            claims += ["square_delta_simple", "square_delta_double"]
        else:
            assert sp.expand(changes[1]-12*(2/n**5+c[2]/n**3+c[3]/n**2)) == 0
            assert sp.expand(changes[2]-(12/n**4+6*c[2]/n**2)) == 0
            assert changes[3] == 6/n**3 and changes[4] == 3/n**2
            claims += ["cube_delta_simple", "cube_delta_double", "cube_delta_3_4"]
    p = 24+12*u+3*u*(u+1)+sp.Rational(1,2)*u*(u+1)*(u+2)
    assert sp.expand(p-(u**3+9*u**2+32*u+48)/2) == 0
    claims.append("cube_zeta_polynomial")
    L = sp.Symbol("L")
    for j in range(2, 10):
        for q in range(1, 6):
            lhs = (sp.rf(u,j-1)*sp.exp(-u*L)/sp.factorial(j-1)).series(u,0,q+1).removeO().coeff(u,q)
            product = sp.prod(1+u/k for k in range(1,j-1))
            rhs = (product*sp.exp(-u*L)).series(u,0,q).removeO().coeff(u,q-1)/(j-1)
            assert sp.simplify(lhs-rhs) == 0
            claims.append(f"coefficient_kernel_j{j}_q{q}")
    return {"assertions": len(claims), "all_passed": True, "claims": claims}


def numerical_checks(dps):
    mp.mp.dps = dps
    zeta = mp.zeta
    cut = mp.mpf(1)/16
    terms = max(45, dps)
    z = {k: zeta(k) for k in range(2, terms+8)}
    qcoeff = [(-1)**k*(k+1)*z[k+2] for k in range(terms+5)]
    qsq = [mp.fsum(qcoeff[k]*qcoeff[m-k] for k in range(m+1))
           for m in range(terms+3)]
    fcoeff = {
        "psi_square": [-2*(-1)**m*z[m+2] for m in range(terms)],
        "trigamma_square": [2*qcoeff[m+2] for m in range(terms)],
        "trigamma_cube": [3*qcoeff[m+4]+3*qsq[m+2] for m in range(terms)]
    }
    p10 = {"psi_square": 2*mp.euler,
           "trigamma_square": -4*z[3],
           "trigamma_cube": -12*(z[5]+z[2]*z[3])}

    def F(kind, x):
        if x < cut:
            return mp.polyval(list(reversed(fcoeff[kind])), x)
        if kind == "psi_square":
            return -2*(mp.digamma(1+x)+mp.euler)/x
        qx = mp.polygamma(1,1+x)
        if kind == "trigamma_square":
            return 2*(qx-z[2])/x**2+4*z[3]/x
        return (3*qx/x**4+3*qx**2/x**2-3*z[2]/x**4+6*z[3]/x**3
                -(9*z[4]+3*z[2]**2)/x**2-p10[kind]/x)

    def hinverse(kind, y):
        """h(1/y)/y^2, simplified before evaluation at small y."""
        if not y:
            if kind == "psi_square":
                return -mp.mpf(1)
            if kind == "trigamma_square":
                return -2*z[2]
            return -(9*z[4]+3*z[2]**2)
        xx = 1/y
        if kind == "psi_square":
            if y < mp.mpf(10)**(-(dps//3)):
                # Asymptotic series for psi(1+x)-log(x), with an error
                # far smaller than the working precision in the integral.
                return -1+y/6-y**3/60+y**5/126
            return -2*(mp.digamma(1+xx)-mp.log(xx))/y
        qx = mp.polygamma(1,1+xx)
        if kind == "trigamma_square":
            return 2*(qx-z[2])
        return 3*qx*y**2+3*qx**2-3*z[2]*y**2+6*z[3]*y-(9*z[4]+3*z[2]**2)

    def A(kind, u=0, log_power=0):
        # Integrate the local Taylor polynomial analytically, avoiding
        # tanh-sinh's slow endpoint convergence when Re(u) is close to 1.
        # This is still the independently derived spatial integral.
        def log_monomial(k):
            alpha=k+1-u
            return cut**alpha*mp.fsum(
                mp.binomial(log_power,j)*mp.log(cut)**(log_power-j)
                *(-1)**j*mp.factorial(j)/alpha**(j+1)
                for j in range(log_power+1))
        inner = mp.fsum(value*log_monomial(k)
                        for k,value in enumerate(fcoeff[kind]))
        inner += mp.quad(lambda x: x**(-u)*F(kind,x)*mp.log(x)**log_power,
                         [cut,mp.mpf(1)/4,1])
        outer = mp.quad(lambda y: y**u*hinverse(kind,y)*(-mp.log(y))**log_power,
                        [0,cut,mp.mpf(1)/4,1])
        return inner+outer

    def mellin_B(kind,u):
        polar = p10[kind]/u
        if kind == "psi_square":
            polar += 2/u**2
        return mp.sin(mp.pi*u)/mp.pi*(A(kind,u)-polar)

    zcache = {}
    def double_zeta(s,t,derivative=0):
        key = (str(s), t, derivative)
        if key in zcache:
            return zcache[key]
        psi = mp.digamma(s)
        trig = mp.polygamma(1,s)
        def kernel(v):
            if v > 10**4:
                return 0
            base = v**(s-1)*mp.polylog(t,mp.exp(-v))/mp.expm1(v)
            if derivative == 1:
                base *= mp.log(v)-psi
            elif derivative == 2:
                base *= (mp.log(v)-psi)**2-trig
            return base
        val = mp.quad(kernel,[0,1,5,20,mp.inf])/mp.gamma(s)
        zcache[key] = val
        return val

    def rhs(kind,u):
        if kind == "psi_square":
            return -2*zeta(1+u)
        if kind == "trigamma_square":
            return (4+2*u)*zeta(3+u)
        return ((u**3+9*u**2+32*u+48)/2*zeta(5+u)
                +6*(u+2)*(double_zeta(3+u,2)+z[2]*zeta(3+u))
                +12*(double_zeta(2+u,3)-z[3]*zeta(2+u)))

    records = []
    def record(name,lhs,rhsvalue):
        absolute = abs(lhs-rhsvalue)
        relative = absolute/max(mp.mpf(1),abs(rhsvalue))
        records.append({"name":name,"lhs":mp.nstr(lhs,dps),
                        "rhs":mp.nstr(rhsvalue,dps),
                        "absolute_residual":mp.nstr(absolute,10),
                        "relative_residual":mp.nstr(relative,10)})
        return relative

    max_relative = mp.mpf(0)
    for kind in fcoeff:
        for u in [mp.mpf("0.37"), mp.mpc("0.61","0.13")]:
            rel=record(f"mellin_{kind}_{u}",mellin_B(kind,u),rhs(kind,u))
            max_relative=max(max_relative,rel)

    # Higher coefficient evaluations use direct ordinary logarithmic
    # quadrature on the left, and differentiated spectral integrals on
    # the right.  No numerical differentiation of the left is used.
    rel=record("psi_square_log_moment",A("psi_square",log_power=1),
               mp.stieltjes(2)+mp.euler*mp.pi**2/3)
    max_relative=max(max_relative,rel)
    rel=record("trigamma_square_log_moment",A("trigamma_square",log_power=1),
               -2*zeta(3,derivative=2)-2*zeta(3,derivative=1)-2*mp.pi**2*z[3]/3)
    max_relative=max(max_relative,rel)
    B2cube=(12*zeta(5,derivative=2)+16*zeta(5,derivative=1)+mp.mpf(9)/2*z[5]
            +6*(double_zeta(3,2,2)+double_zeta(3,2,1))
            +6*z[2]*(zeta(3,derivative=2)+zeta(3,derivative=1))
            +6*double_zeta(2,3,2)-6*z[3]*zeta(2,derivative=2))
    rel=record("trigamma_cube_log_moment",A("trigamma_cube",log_power=1),
               -B2cube-2*mp.pi**2*(z[5]+z[2]*z[3]))
    max_relative=max(max_relative,rel)
    return {"working_decimal_digits":dps,"comparisons":len(records),
            "largest_relative_residual":mp.nstr(max_relative,12),
            "diagnostics_not_interval_proofs":True,"records":records}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--dps",type=int,default=50)
    parser.add_argument("--output",type=Path,default=Path(__file__).with_name("spectral_mellin_checks.json"))
    args=parser.parse_args()
    result={"exact":exact_checks(),"numerical":numerical_checks(args.dps)}
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"exact_assertions":result["exact"]["assertions"],
                      "comparisons":result["numerical"]["comparisons"],
                      "max_relative":result["numerical"]["largest_relative_residual"],
                      "output":str(args.output)},indent=2))


if __name__=="__main__":
    main()
