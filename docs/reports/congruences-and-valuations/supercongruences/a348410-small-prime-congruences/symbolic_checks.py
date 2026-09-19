#!/usr/bin/env python3
"""Optional SymPy/mpmath checks: algebraic identities and saddle asymptotics.

Run after installing sympy and mpmath. All symbolic identity checks are exact;
only the explicitly labelled asymptotic comparison uses decimal arithmetic.
"""
from __future__ import annotations
import csv
from pathlib import Path
import sympy as sp
import mpmath as mp
from verify import diagonal, require


def gaussian_coefficient(order: int, kappas: dict[int, sp.Expr]) -> sp.Expr:
    """Finite Gaussian/Bell sum in the asymptotic theorem of the article."""
    total = sp.S.Zero
    largest = 2*order+2

    def visit(k: int, remaining: int, degree: int, factor: sp.Expr) -> None:
        nonlocal total
        if k > largest:
            if remaining == 0:
                require(degree % 2 == 0,"Gaussian moment must be even")
                moment = sp.factorial2(degree-1) if degree else sp.S.One
                total += (-1)**(degree//2)*moment*factor/kappas[2]**(degree//2)
            return
        for multiplicity in range(remaining//(k-2)+1):
            visit(k+1,remaining-(k-2)*multiplicity,degree+k*multiplicity,
                  factor*kappas[k]**multiplicity /
                  (sp.factorial(multiplicity)*sp.factorial(k)**multiplicity))

    visit(3,2*order,0,sp.S.One)
    return sp.radsimp(sp.simplify(total))


def main() -> None:
    root = Path(__file__).resolve().parent
    (root/"data").mkdir(exist_ok=True)
    x,z,h = sp.symbols("x z h")
    alpha,beta,n = sp.symbols("alpha beta n",integer=True)
    phi = 1/((1-x)*(1-x*x))
    V = 2*x/(1-x)-x/(1+x)
    require(sp.cancel(x*sp.diff(phi,x)/phi-V)==0,"logarithmic derivative")
    parametrized_h = (1-x*x)/(1-x-4*x*x)
    equation = z*z*(4*h-1)**4+z*h*(107*h**3-107*h*h+36*h-4)+32*h**3*(1-h)
    substitution = equation.subs({h:parametrized_h,z:x*(1-x)**2*(1+x)})
    require(sp.cancel(substitution)==0,"quartic parametrization")
    resultant = sp.resultant(z-x*(1-x)**2*(1+x),
                            h*(1-x-4*x*x)-(1-x*x),x)
    require(sp.expand(resultant-equation)==0,"resultant identity")
    # Exact truncated coefficient check, separate from the parametrization.
    series = sum(diagonal(j)*z**j for j in range(21))
    require(sp.series(equation.subs(h,series),z,0,21).removeO().expand()==0,
            "quartic power-series check")

    tau=(sp.sqrt(17)-1)/8
    rho=(51*sp.sqrt(17)-107)/512
    growth=(107+51*sp.sqrt(17))/64
    require(sp.simplify(tau*(1-tau)**2*(1+tau)-rho)==0,"rho")
    require(sp.simplify(rho*growth-1)==0,"growth reciprocal")
    kappas={}
    current=V
    for j in range(1,7):
        kappas[j]=sp.radsimp(sp.simplify(current.subs(x,tau)))
        current=sp.factor(x*sp.diff(current,x))
    require(kappas[1]==1,"saddle equation")
    c1=gaussian_coefficient(1,kappas)
    c2=gaussian_coefficient(2,kappas)
    stated_c1=(-1683+95*sp.sqrt(17))/9248
    stated_c2=(119821-28605*sp.sqrt(17))/5030912
    require(sp.simplify(c1-stated_c1)==0,"c1 identity")
    require(sp.simplify(c2-stated_c2)==0,"c2 identity")
    require(sp.simplify(1/(2*kappas[2])-(3+5/sp.sqrt(17))/16)==0,
            "leading amplitude identity")

    mp.mp.dps=90
    root17=mp.sqrt(17)
    lam=(107+51*root17)/64
    k2=(51-5*root17)/16
    cc1=(-1683+95*root17)/9248
    cc2=(119821-28605*root17)/5030912
    rows=[]
    for nn in [10,25,50,100,250,500,1000]:
        exact=mp.mpf(diagonal(nn))
        leading=lam**nn/mp.sqrt(2*mp.pi*k2*nn)
        norm=exact/leading
        rows.append({"n":nn,"normalized_ratio":mp.nstr(norm,22),
                     "relative_error_leading":mp.nstr(leading/exact-1,15),
                     "relative_error_through_c1":mp.nstr(leading*(1+cc1/nn)/exact-1,15),
                     "relative_error_through_c2":mp.nstr(leading*(1+cc1/nn+cc2/nn**2)/exact-1,15),
                     "n_cubed_residual":mp.nstr(nn**3*(norm-1-cc1/nn-cc2/nn**2),15)})
    with (root/"data"/"asymptotic_checks.csv").open("w",newline="",encoding="utf-8") as handle:
        writer=csv.DictWriter(handle,fieldnames=list(rows[0]))
        writer.writeheader();writer.writerows(rows)
    lines=["Symbolic checks: PASS",f"SymPy version: {sp.__version__}",
           f"mpmath version: {mp.__version__}","",
           "Verified logarithmic derivative, resultant, quartic parametrization,",
           "quartic power series through degree 20, saddle point, growth constant,",
           "Gaussian/Bell formulas for c1 and c2, and the leading amplitude.","",
           f"c1 = {c1}",f"c2 = {c2}",f"growth constant = {mp.nstr(lam,24)}",
           "", "Asymptotic comparisons use 90 decimal digits; they are not proofs."]
    (root/"symbolic_report.txt").write_text("\n".join(lines)+"\n",encoding="utf-8")
    print("\n".join(lines))


if __name__=="__main__":
    main()
