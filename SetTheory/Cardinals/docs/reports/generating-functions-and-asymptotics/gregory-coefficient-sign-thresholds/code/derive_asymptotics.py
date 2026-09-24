#!/usr/bin/env python3
"""Derive the formal expansion of log Gr(m) from exact gamma moments.

Requires SymPy. Zk is a formal symbol for zeta(k); d=1-EulerGamma.
This symbolic calculation is an algebra check, not a substitute for the
uniform estimates and positivity-propagation proof in the article.
"""
from __future__ import annotations
import argparse
from pathlib import Path
import sympy as sp


def derive(corrections: int) -> str:
    if corrections < 1:
        raise ValueError("corrections must be positive")
    K = corrections + 1
    s, c, d = sp.symbols("s c d")
    zetas = {k: sp.Symbol(f"Z{k}") for k in range(2, 2*K+1)}
    # q(1+z) = -z exp(d*z + sum_{k>=2} ((-1)^(k+1)-Zk)*z^k/k).
    exponent = [sp.Integer(0), d] + [
        (sp.Integer(-1)**(k+1)-zetas[k])/k for k in range(2, 2*K)]
    exp_coeff = [sp.Integer(1)]
    for k in range(1, 2*K):
        exp_coeff.append(sp.expand(sum(j*exponent[j]*exp_coeff[k-j]
                                      for j in range(1, k+1))/k))
    q_coeff = [sp.Integer(0)] + [-v for v in exp_coeff]
    phi = sp.Integer(0)
    for j in range(1, 2*K+1):
        moment = sum(
            sp.binomial(j, k)*(-1)**(j-k)
            * sp.prod(1+i*s for i in range(k))/(1+c*s)**k
            for k in range(j+1))
        moment = sp.series(moment, s, 0, K+1).removeO().expand()
        phi += q_coeff[j]*moment
    poly = sp.Poly(sp.expand(phi), s)
    P = {k: sp.factor(poly.coeff_monomial(s**k)) for k in range(1, K+1)}
    assert sp.expand(P[1] - c + d) == 0
    assert sp.expand(P[2].subs(c,d)-zetas[2]-zetas[3]) == 0
    lines = ["s=1/m; d=1-EulerGamma; Zk=zeta(k).", "", "Moment polynomials:"]
    lines += [f"P{k}(c) = {P[k]}" for k in range(1, K+1)]
    solution = d
    results = {}
    for k in range(1, corrections+1):
        candidate = sp.Symbol(f"c{k}")
        expr = sum(P[j].subs(c,solution+candidate*s**k)*s**(j-1)
                   for j in range(1,k+2))
        residual = sp.series(expr,s,0,k+1).removeO().expand().coeff(s,k)
        value = sp.factor(sp.solve(residual,candidate)[0])
        assert not value.has(d), "EulerGamma must cancel after the constant shift"
        results[k] = value
        solution += value*s**k
    assert sp.expand(results[1]+zetas[2]+zetas[3]) == 0
    if corrections >= 2:
        expected = (zetas[2]**2+zetas[2]*zetas[3]+zetas[2]-zetas[3]
                    -5*zetas[4]-3*zetas[5])
        assert sp.expand(results[2]-expected) == 0
    lines += ["", "log Gr(m) ~ m+d+sum_{j>=1} cj/m^j:"]
    lines += [f"c{k} = {value}" for k,value in results.items()]
    numeric = {d: 1-sp.EulerGamma} | {symbol: sp.zeta(k) for k,symbol in zetas.items()}
    lines += ["", f"exp(d) = {sp.N(sp.exp(1-sp.EulerGamma),30)}"]
    lines += [f"c{k} numerically = {sp.N(value.subs(numeric),30)}"
              for k,value in results.items()]
    lines += ["", "PASS symbolic identities and cancellation checks."]
    return "\n".join(lines)+"\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corrections",type=int,default=3)
    parser.add_argument("--output",type=Path)
    args = parser.parse_args()
    text = derive(args.corrections)
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(text,encoding="utf-8")
    print(text,end="")


if __name__ == "__main__":
    main()
