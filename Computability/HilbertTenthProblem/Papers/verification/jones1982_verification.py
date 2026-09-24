#!/usr/bin/env python3
"""Reproducible algebraic and finite checks for the corrected Jones edition.

Requires Python 3.10+ and SymPy. No network, Wolfram kernel, or OCR is used.
Run: python jones1982_verification.py
Writes jones1982_verification_results.json in the same directory.
Self-contained (reads no article source).
These checks are not a formal verification of all the number-theoretic lemmas.
"""
from __future__ import annotations
from itertools import product
from math import comb, factorial, isqrt
from pathlib import Path
import json
import sympy as sp


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digitsum(n: int, base: int) -> int:
    if n < 0 or base < 2:
        raise ValueError("Nonnegative integer and integer base >= 2 required")
    result = 0
    while n:
        n, r = divmod(n, base)
        result += r
    return result


def carries(a: int, b: int, base: int) -> int:
    # Independent digit-by-digit algorithm, including propagation of carries.
    if min(a, b) < 0 or base < 2:
        raise ValueError("Invalid carry arguments")
    count = incoming = 0
    while a or b or incoming:
        a, da = divmod(a, base)
        b, db = divmod(b, base)
        incoming = int(da + db + incoming >= base)
        count += incoming
    return count


def valuation(n: int, p: int) -> int:
    require(n > 0 and p > 1, "Invalid valuation")
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


def check_carries() -> dict:
    count = 0
    for base in (2, 3, 5, 7):
        for a, b in product(range(40), repeat=2):
            expected = valuation(comb(a + b, a), base)
            require(carries(a, b, base) == expected, "Kummer identity failed")
            require((digitsum(a, base) + digitsum(b, base) - digitsum(a+b, base))
                    == (base-1)*expected, "Digit-sum identity failed")
            count += 1
    block_count = 0
    for n1, n2 in ((2, 2), (2, 4), (4, 8), (8, 4)):
        for s1, t1, s2, t2 in product(range(n1), range(n1), range(n2), range(n2)):
            require((carries(s1, t1, 2) == 0 and carries(s2, t2, 2) == 0)
                    == (carries(s1+n1*s2, t1+n1*t2, 2) == 0), "Packing failed")
            block_count += 1
    central_count = 0
    for n in (1, 2, 4, 8, 16):
        for s, t in product(range(n), repeat=2):
            r = s*(n*n-n)+(t+1)*(n*n-1)
            require(r == (s+t)*n*n+(n-1-s)*n+n-1-t, "R expansion failed")
            require((comb(2*r, r) % (n*n) == 0) == (carries(s, t, 2) == 0),
                    "Lemma 2.16 failed")
            central_count += 1
    return dict(kummer_cases=count, packing_cases=block_count,
                central_binomial_cases=central_count)


def check_mask() -> int:
    cases = 0
    for z, B, n, m, k in ((2, 16, 1, 1, 2), (2, 32, 1, 2, 3), (4, 32, 1, 1, 2)):
        mask = sum((B-z)*B**i for i in range(k))
        for ds in product(range(z), repeat=n+1):
            y = sum(d*z**i for i, d in enumerate(ds))
            intended = sum(d*B**i for i, d in enumerate(ds))
            for Y in range(z*B**m):
                rhs = (Y-y) % (B-z) == 0 and carries(Y, mask, 2) == 0
                require((Y == intended) == rhs, "Lemma 2.9 failed")
                cases += 1
    return cases


def check_coefficient_extraction() -> int:
    cases = 0
    for delta, nu in ((3, 1), (4, 1), (4, 2)):
        h = (delta+1)**(nu+1)
        indices = [v for v in product(range(delta+1), repeat=nu+1) if sum(v)<=delta]
        coefficients = {v: (-1)**sum(v)*(1+sum((j+1)*v[j] for j in range(nu+1))%3)
                        for v in indices}
        scaled = {}
        multinomial = {}
        for v in indices:
            den = factorial(delta-sum(v))
            for vi in v:
                den *= factorial(vi)
            multinomial[v] = factorial(delta)//den
            scaled[v] = den*coefficients[v]
        z = max(abs(p) for p in scaled.values()) + 2
        for values in product(range(1, 4), repeat=nu+1):
            cdelta = {}
            for v in indices:
                exponent = sum(v[j]*(delta+1)**j for j in range(nu+1))
                cdelta[exponent] = multinomial[v]*sp.prod(values[j]**v[j] for j in range(nu+1))
            d0 = {h-sum(v[j]*(delta+1)**j for j in range(nu+1)): p for v,p in scaled.items()}
            e = {h-sum(v[j]*(delta+1)**j for j in range(nu+1)): z+p for v,p in scaled.items()}
            target = factorial(delta)*sum(coefficients[v]*sp.prod(values[j]**v[j] for j in range(nu+1)) for v in indices)
            m5 = sum(a*d0.get(h-j, 0) for j,a in cdelta.items())
            u11 = sum(a*(e.get(h-j, 0)-z) for j,a in cdelta.items())
            require(m5 == target and u11 == target, "Coefficient extraction failed")
            cases += 1
    return cases


def quadratic_certificate() -> tuple[dict, dict]:
    """Reproduce the 36 retained + 22 auxiliary positive unknowns in section 5.

    x is included in total degree, whereas z,u,y,L,kappa are coefficients.
    L=(delta+1)^(nu+1), delta=4; kappa=2*(2*z)^(L+1).
    """
    retained = sp.symbols("B C1 D D1 E F G H I K M N P R S T U Y c e g h i j l m o s t w alpha Delta gamma lam phi eps")
    helpers = sp.symbols("LB b2 J1 AC1 c2 c4 slack8 Q2 Q3 Q4 c4Q3 Nsq MU PK tau YK slack21 AC Csq AE Fsq GH")
    B,C1,D,D1,E,F,G,H,I,K,M,N,P,R,S,T,U,Y,c,e,g,h,i,j,l,m,o,s,t,w,alpha,Delta,gamma,lam,phi,eps = retained
    LB,b2,J1,AC1,c2,c4,slack8,Q2,Q3,Q4,c4Q3,Nsq,MU,PK,tau,YK,slack21,AC,Csq,AE,Fsq,GH = helpers
    x,z,u,y,L,kappa = sp.symbols("x z u y L kappa")
    b=eps+x; A=M+MU; C=2*R+1+C1+phi; Q=1+LB-lam
    eqs: list[tuple[str,sp.Expr]] = []
    def eq(name: str, left: sp.Expr, right: sp.Expr) -> None:
        eqs.append((name, sp.expand(left-right)))
    eq("helper LB", LB, lam*B)
    eq("helper b2", b2, b*b)
    eq("D2", B, kappa*b2*b2)
    eq("helper J1", J1, 2*A*B-B*B-1)
    eq("helper AC1", AC1, A*C1)
    eq("D3", D1, Q+AC1-B*C1+alpha*J1)
    eq("D4", D1*D1, AC1*AC1-C1*C1+1)
    eq("D5", C1, L+Delta*(A-1))
    eq("D6", c, 1+x*B+g)
    eq("helper c2", c2, c*c)
    eq("helper c4", c4, c2*c2)
    eq("D8", e+2*z*b*l+2*z*B*c4+slack8, 2*z*Q)
    eq("D9", l, u+t*(B-2*z))
    eq("D10", e, y+m*(B-2*z))
    eq("helper Q2", Q2, Q*Q)
    eq("helper Q3", Q3, Q2*Q)
    eq("helper Q4", Q4, Q2*Q2)
    eq("helper c4Q3", c4Q3, c4*Q3)
    eq("D16 S", S, g+l*Q+e*Q2-4*z*z*c4Q3*lam-4*z*z*c4Q3*Q
        +4*z*c4Q3*e+2*z*LB*(Q3+Q4))
    eq("D16 T", T, Q-1-(b-1)*l+(LB-2*z*lam)*(Q+Q2)+2*z*B*Q4-4*z*Q4)
    eq("D17", N, 16*z*Q*Q4)
    eq("helper Nsq", Nsq, N*N)
    eq("D18", R, S*(Nsq-N)+(T+1)*(Nsq-1))
    eq("helper MU", MU, M*U)
    eq("D19", P, 2*M*MU)
    eq("helper PK", PK, P*K)
    eq("D20", tau*tau, PK*PK-K*K+1)
    eq("helper YK", YK, Y*K)
    eq("D21", 4*(C-YK)**2+slack21, K*K)
    eq("D22", K, R+1+h*(P-1))
    eq("D23", M, R*Y)
    eq("D26", U, Nsq*w)
    eq("D27", Y, Nsq*s)
    eq("helper AC", AC, A*C)
    eq("D30", D, b*w+AC-2*C+gamma*(4*A-5))
    eq("D31", I, D+o*F)
    eq("D32", D*D, AC*AC-C*C+1)
    eq("helper Csq", Csq, C*C)
    eq("D33", E, i*Csq)
    eq("helper AE", AE, A*E)
    eq("helper Fsq", Fsq, F*F)
    eq("D34", Fsq, AE*AE-E*E+1)
    eq("D35", G, A+Fsq*(Fsq-A))
    eq("D36", H, 2*R+1+j*C)
    eq("helper GH", GH, G*H)
    eq("D37", I*I, GH*GH-H*H+1)
    unknowns = retained+helpers
    require(len(unknowns)==58 and len(set(unknowns))==58, "Variable count failed")
    degrees = {name: int(sp.Poly(poly,*unknowns,x).total_degree()) for name,poly in eqs}
    require(max(degrees.values())==2, "Nonquadratic equation in certificate")
    # A sum of real squares vanishes exactly when each residual vanishes.
    # The nonzero leading quadratic part of the b2 equation makes the sum degree four.
    require(sp.Poly(dict(eqs)["helper b2"],*unknowns,x).total_degree()==2,
            "Quartic sum-of-squares witness missing")
    # Independently verify the two nontrivial substituted packing expressions.
    q4 = {LB:lam*B,Q2:Q**2,Q3:Q**3,Q4:Q**4,c4Q3:c4*Q**3}
    targetS = g+(l+e*Q)*Q+(-2*c4*(z*(lam+Q)-e)+B*lam*(1+Q))*2*z*Q**3
    targetT = Q-1-(b-1)*l+(B-2*z)*lam*(1+Q)*Q+(B-2)*Q*2*z*Q**3
    # Simultaneous substitutions need a final LB substitution in the Q expressions.
    S_formula = S-dict(eqs)["D16 S"]
    T_formula = T-dict(eqs)["D16 T"]
    for lhs,rhs in ((S_formula,targetS),(T_formula,targetT)):
        difference = (lhs.subs(q4, simultaneous=True)-rhs).subs(LB,lam*B)
        require(sp.expand(difference)==0, "Quadratic packing substitution failed")
    report = dict(retained_unknowns=len(retained), auxiliary_unknowns=len(helpers),
                  total_unknowns=len(unknowns), quadratic_equations=len(eqs),
                  maximum_degree_including_x=max(degrees.values()),
                  sum_of_squares_degree=4, degrees=degrees,
                  retained_names=[str(v) for v in retained],
                  helper_names=[str(v) for v in helpers])
    formulas = {name: str(poly) for name,poly in eqs}
    return report, formulas


def symbolic_checks() -> dict:
    b,q,g,e,l,z,lam,theta,x,n,r,s,w = sp.symbols("b q g e l z lam theta x n r s w")
    c=1+x*b**5+g
    s3=2*(e-z*lam)*c**4+lam*b**5*(1+q**4)
    packed_s=g+(e+l*q**2)*q**3+s3*q**7
    packed_t=q**3-1-(b-1)*l+theta*lam*q**3+(b**5-2)*q**8
    corrected_r=(g+e*q**3+l*q**5+s3*q**7)*(n*n-n)+(q**3-b*l+l+theta*lam*q**3+(b**5-2)*q**8)*(n*n-1)
    require(sp.expand(corrected_r-(packed_s*(n*n-n)+(packed_t+1)*(n*n-1)))==0,
            "Theorem 2/3 r packing failed")
    P=2*(r*n*n*s)**2*(n*n*w)
    require(sp.expand(P-2*w*s*s*r*r*n**6)==0, "Theorem 3 p failed")
    a,b0,x0=sp.symbols("a b0 x0")
    # Product identity and positive-square criterion, no floating point.
    product_expr=sp.prod(x0+sgn*sp.sqrt(a)+tgn*sp.sqrt(b0)
                         for sgn,tgn in product((-1,1), repeat=2))
    require(sp.expand(product_expr-(x0**4-2*(a+b0)*x0*x0+(a-b0)**2))==0,
            "Four-sign product identity failed")
    sqcases=0
    for aa,bb in product(range(1,80),repeat=2):
        square_pair = isqrt(aa)**2==aa and isqrt(bb)**2==bb
        exists=any(xx**4-2*(aa+bb)*xx*xx+(aa-bb)**2==0 for xx in range(1,2*isqrt(79)+2))
        require(square_pair==exists, "Positive square-combining example failed")
        sqcases+=1
    degree=47216*5**58+9728
    return dict(theorem_r_identity=True,theorem_p_identity=True,
                square_product_identity=True,square_pair_cases=sqcases,
                exact_degree_expression=str(degree), degree_scientific=f"{degree:.9e}")


def main() -> None:
    report = {"scope":"Algebraic identities, finite tests and quadratic-degree certificate; not a formal proof of universality.",
              "sympy_version":sp.__version__}
    report["carries"] = check_carries()
    report["mask_cases"] = check_mask()
    report["coefficient_extraction_cases"] = check_coefficient_extraction()
    report["symbolic_checks"] = symbolic_checks()
    report["quadratic_certificate"], equations = quadratic_certificate()
    report["quadratic_residuals"] = equations
    dest=Path(__file__).resolve().with_name("jones1982_verification_results.json")
    dest.write_text(json.dumps(report,ensure_ascii=False,indent=2)+"\n",encoding="utf-8",newline="\n")
    print(json.dumps({k:v for k,v in report.items() if k not in ("quadratic_residuals","quadratic_certificate")},indent=2))
    print("Quadratic certificate:",report["quadratic_certificate"]["total_unknowns"],"unknowns;",
          report["quadratic_certificate"]["quadratic_equations"],"equations; maximum degree 2; sum of squares degree 4.")
    print("Wrote",dest.name)

if __name__ == "__main__":
    main()
