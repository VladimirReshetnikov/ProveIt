"""Optional exact symbolic audits of the displayed R1, R2, and constants.

Requires SymPy; no floating diagnostics or asymptotic remainder certification.
"""
import sys
sys.dont_write_bytecode = True
import json


def symbolic_checks():
    import sympy as S
    from exact_nested import check

    x, v, beta = S.symbols("x v beta", positive=True)
    ell, D, E = S.symbols("ell D E", real=True)
    # Taylor coefficients of the logarithm of the local saddle amplitude.
    # Phase correction: i*d*x^3/[v*(1+i*d*x/sqrt(v))].
    # Power amplitude: (1+i*d*x/sqrt(v))^(-beta).
    w = [S.Integer(0)]
    for r in range(1, 5):
        phase = S.I * x**3 / v * (-S.I*x/S.sqrt(v))**(r - 1)
        power = -beta * (-1)**(r + 1) * (S.I*x/S.sqrt(v))**r / r
        w.append(S.expand(phase + power))
    h = [S.Integer(1)]
    for r in range(1, 5):
        h.append(S.expand(sum(j*w[j]*h[r-j] for j in range(1,r+1))/r))

    def gaussian_expectation(polynomial):
        result = S.Integer(0)
        for (degree,), coefficient in S.Poly(S.expand(polynomial), x).terms():
            if degree % 2 == 0:
                k = degree // 2
                result += coefficient * S.factorial2(2*k-1) * v**S.Rational(k,2) / 2**k
        return S.factor(result)

    def equal(left, right, label):
        check(S.simplify(left-right) == 0, label)

    b1 = (1-4*(beta-1)**2)/(16*S.sqrt(v))
    b2 = (4*(beta-1)**2-1)*(4*(beta-1)**2-9)/(512*v)
    equal(gaussian_expectation(h[2]), b1, "unperturbed Gaussian order two")
    equal(gaussian_expectation(h[4]), b2, "unperturbed Gaussian order four")
    equal(gaussian_expectation(h[1]), 0, "odd Gaussian order one")
    equal(gaussian_expectation(h[3]), 0, "odd Gaussian order three")

    delta = S.symbols("delta")
    log_shift = S.I*delta*x/S.sqrt(v) + delta**2*x**2/(2*v)
    shifted_Q = S.expand((ell+log_shift)**2/2 + D*(ell+log_shift) + E)
    q = [shifted_Q.coeff(delta,j) for j in range(3)]
    Q = ell**2/2 + D*ell + E
    marked = gaussian_expectation(sum(q[j]*h[2-j] for j in range(3)))
    equal(marked, Q*b1-(ell+D)*S.diff(b1,beta)+S.diff(b1,beta,2)/2,
          "log-polynomial differentiation identity")
    cross = v*((1-4*(v-2)**2)*Q/16+(v-2)*(ell+D)/2-S.Rational(1,4))
    equal(v**S.Rational(3,2)*marked.subs(beta,v-1), cross, "R2 logarithmic cross term")

    A = S.Rational(1,2)-S.log(2)
    B = S.Rational(41,24)-S.zeta(2)/2-S.Rational(3,2)*S.log(3)
    B_direct = (-S.Rational(5,12)+S.Rational(3,2)+S.Rational(3,4)
                -S.Rational(3,2)*S.log(3)-S.zeta(2)/2-S.Rational(1,8))
    equal(B, B_direct, "B arithmetic from separately evaluated source pieces")
    B3 = S.Rational(49,12)-S.pi**2/4+S.zeta(3)/3-S.Rational(8,3)*S.log(4)
    B3_direct = (S.Rational(1,6)-S.Rational(13,18)+S.Rational(9,4)
                 +S.Rational(20,9)-S.Rational(8,3)*S.log(4)
                 +S.Rational(1,6)-S.Rational(3,2)*S.zeta(2)+S.zeta(3)/3)
    equal(B3, B3_direct, "B3 arithmetic from separately evaluated source pieces")
    Q_exact = ell**2/2+(S.log(2)-2)*ell+B+A**2/2
    equal((-ell+A)**2/2-S.Rational(3,2)*ell+B, Q_exact, "component U1 polynomial")
    Z = (-ell+A)**3/6+(-ell+A)*(-S.Rational(3,2)*ell+B)-S.Rational(8,3)*ell+B3
    local_log = [S.Integer(0), -ell+A, -S.Rational(3,2)*ell+B,
                 -S.Rational(8,3)*ell+B3]
    component_exp = [S.Integer(1)]
    for degree in range(1,4):
        component_exp.append(S.expand(sum(j*local_log[j]*component_exp[degree-j]
                                         for j in range(1,degree+1))/degree))
    equal(component_exp[2], Q_exact, "exponentiated component U1")
    equal(component_exp[3], Z, "exponentiated component U2")
    outer_order_two = v*component_exp[3] + (v*component_exp[2])**2/2
    equal(outer_order_two, v*Z+v**2*Q_exact**2/2, "outer amplitude order two")
    r1 = v**S.Rational(3,2)*Q_exact + b1.subs(beta,v)
    r2 = b2.subs(beta,v)+cross.subs({D:S.log(2)-2,E:B+A**2/2})+v**2*Z+v**3*Q_exact**2/2
    L = S.symbols("L", real=True)
    r1_L = S.expand(r1.subs(ell,(S.log(v)-L)/2))
    r2_L = S.expand(r2.subs(ell,(S.log(v)-L)/2))
    check(S.Poly(r1_L,L).degree() == 2, "R1 logarithmic degree")
    check(S.Poly(r2_L,L).degree() == 4, "R2 logarithmic degree")
    equal(r1_L.coeff(L,2), v**S.Rational(3,2)/8, "R1 leading logarithmic coefficient")
    equal(r2_L.coeff(L,4), v**3/128, "R2 leading logarithmic coefficient")

    u,c = S.symbols("u c", positive=True)
    logC = u*(c*A-1)+(S.Rational(1,4)-c*u/2)*S.log(c*u)-S.log(2*S.sqrt(S.pi))
    equal(S.diff(logC,u).subs(u,1), -S.Rational(3,4)-c*S.log(2)-c*S.log(c)/2,
          "constant term of mean")
    equal((S.diff(logC,u)+S.diff(logC,u,2)).subs(u,1),
          -1-c*(S.log(2)+S.Rational(1,2)+S.log(c)/2), "constant term of variance")
    ell_c = (S.log(c)-L)/2
    q_c = Q_exact.subs(ell,ell_c)
    qp_c = ell_c + S.log(2)-2
    m1_target = (c**S.Rational(3,2)*(S.Rational(3,2)*q_c+qp_c/2)
                 -S.Rational(3,8)*c**S.Rational(3,2)+S.sqrt(c)/4
                 +S.Rational(3,32)/S.sqrt(c))
    v1_target = (c**S.Rational(3,2)*(S.Rational(9,4)*q_c+S.Rational(3,2)*qp_c+S.Rational(1,4))
                 -S.Rational(9,16)*c**S.Rational(3,2)+S.sqrt(c)/8
                 -S.Rational(3,64)/S.sqrt(c))
    equal((v*S.diff(r1_L,v)).subs(v,c),m1_target,"explicit first mean correction M1")
    equal((v*S.diff(r1_L,v)+v**2*S.diff(r1_L,v,2)).subs(v,c),v1_target,
          "explicit first variance correction V1")
    return {"schema":"report167-symbolic-checks-v1", "status":"passed",
            "sympy_version":S.__version__,
            "checks":["Gaussian order two and four", "odd Gaussian cancellations",
                      "R2 logarithmic cross term", "B and B3 arithmetic decompositions",
                      "component U1/U2 and outer amplitude order two", "R1 and R2 degree and leading logarithmic coefficients",
                      "mean and variance constants", "explicit M1 and V1 correction polynomials"],
            "scope":"Exact symbolic identities for the finite displayed terms; not a proof of infinite-tail summation, analytic remainders, or historical priority."}


if __name__ == "__main__":
    try:
        result = symbolic_checks()
    except ImportError:
        print(json.dumps({"status":"missing-optional-dependency", "dependency":"sympy"},sort_keys=True))
        raise SystemExit(2)
    except Exception as error:
        print(json.dumps({"status":"failed", "error":str(error)},sort_keys=True))
        raise SystemExit(1)
    print(json.dumps(result,indent=2,sort_keys=True))
