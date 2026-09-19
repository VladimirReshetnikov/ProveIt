#!/usr/bin/env python3
"""Optional independent rational-function certificates (requires SymPy).

Run: python code/symbolic_checks.py
The all-degree proofs are in article.tex; these identities can also be checked
by hand after clearing denominators with constant term 1.
"""
from __future__ import annotations
import json
from pathlib import Path
import sympy as sp

x = sp.symbols("x")
M = x/(1-x)


def canonical(expr, p: int):
    n, d = sp.fraction(sp.cancel(expr))
    return sp.cancel(sp.Poly(n,x,modulus=p).as_expr() /
                     sp.Poly(d,x,modulus=p).as_expr(), modulus=p)


def trace(expr, p: int):
    return canonical(sum(expr.subs(x, x/(1-j*x)) for j in range(p)), p)


def orientation(r: int, s: int, p: int):
    if not sp.isprime(p):
        raise ValueError("p must be prime")
    if r % p == 1 and s % p == 0:
        r, s = s, r
    if r % p != 0 or s % p != 1:
        raise ValueError("residues of r,s must be 0,1 in some order")
    return r//p, (s-1)//p


def solve_linearized(r: int, s: int, p: int, residual):
    """Solve (I-DT_M)h=residual over F_p(x), for residual=O(x^3)."""
    alpha, beta = orientation(r,s,p)
    C = canonical(alpha*x + beta*M, p)
    d = canonical(residual/(M**2*(1-x)), p)
    w = canonical(d+C*trace(d,p)/(1-trace(C,p)),p)
    return canonical(M**2*w,p)


def first_correction(r: int, s: int, p: int):
    """Return H with F_{r,s}=M+pH modulo p^2; H is an F_p rational function."""
    alpha, beta = orientation(r,s,p)
    return canonical(x**3*(alpha*(1-x)+beta)*(1-x**(p-1)) /
        ((1-x)**3*(1-x**(p-1)+(alpha+beta)*x**p)), p)


def variation(h, k: int, p: int):
    """Direct chain-rule derivative of the k-fold iterate at M."""
    return canonical(sum((1-(j+1)*x)**2*h.subs(x,x/(1-j*x)) /
                         (1-k*x)**2 for j in range(k)),p)


def main():
    results = {"sympy":sp.__version__, "identities":{}}
    r,s,c = sp.symbols("r s c")
    Mc = x/(1-c*x)
    residual = Mc-x-c*x**2/((1-r*c*x)*(1-s*c*x))
    expected = (-c**2*(r+s-1)*x**3+c**3*r*s*x**4)/(
                  (1-c*x)*(1-r*c*x)*(1-s*c*x))
    assert sp.cancel(residual-expected) == 0
    results["identities"]["universal_Mobius_residual"] = True
    H2=x**3/(1+x**3)
    H5=x**3*(2-x)*(1-x**4)/((1-x)**3*(1-x**4+2*x**5))
    for p, explicit in ((2,H2),(5,H5)):
        R=canonical((10//p)*x**3*(1-3*x)/((1-x)*(1-5*x)*(1-6*x)),p)
        solved=solve_linearized(5,6,p,R)
        closed=first_correction(5,6,p)
        assert canonical(solved-explicit,p)==0
        assert canonical(closed-explicit,p)==0
        lhs=canonical(explicit-x/(1-6*x)*variation(explicit,5,p)
                               -x/(1-5*x)*variation(explicit,6,p),p)
        assert canonical(lhs-R,p)==0
        assert canonical(trace(x,p)+x**p/(1-x**(p-1)),p)==0
        results["identities"][f"correction_mod_{p*p}"] = True
        results["identities"][f"direct_chain_rule_certificate_p{p}"] = True
        results["identities"][f"trace_identity_p{p}"] = True
    # Neighbor A396798: the first nonzero correction is 4H modulo 8.
    h=x**4/(1-x)**3
    R=canonical((2*x**3-5*x**4)/((1-x)*(1-4*x)*(1-5*x)),2)
    assert canonical(solve_linearized(4,5,2,R)-h,2)==0
    assert variation(h,2,2)==0
    results["identities"]["A396798_mod8_and_iterates"] = True
    results["status"]="ALL SYMBOLIC IDENTITIES PASSED"
    path=Path(__file__).resolve().parents[1]/"data"/"symbolic_verification.json"
    path.write_text(json.dumps(results,indent=2)+"\n")
    print(json.dumps(results,indent=2))

if __name__=="__main__":
    main()
