#!/usr/bin/env python3
"""Exact, reproducible checks for the corrected Jones--Sato--Wada--Wiens article.

Requires Python 3.10+ and SymPy. Run from any directory:
    python jones1976_verify_mathematics.py
Reads the current source.

This is a collection of symbolic identities and finite regression tests, NOT a
machine-checked proof of the whole paper. It reads the actual corrected LaTeX
for the fourteen residuals and the equations of Theorem 2.12. The narrow parser
is intended only for this trusted accompanying mathematical source.
"""
from __future__ import annotations

import argparse
import json
import math
import platform
import re
import sys
from fractions import Fraction as Q
from pathlib import Path
from typing import Any

try:
    import sympy as sp
    from sympy.parsing.sympy_parser import (
        convert_xor, implicit_multiplication_application, parse_expr,
        standard_transformations,
    )
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc

VARIABLES = sp.symbols("a:z")
LOCAL = dict(zip("abcdefghijklmnopqrstuvwxyz", VARIABLES))
TRANSFORMS = standard_transformations + (implicit_multiplication_application, convert_xor)


def parse_polynomial_fragment(text: str) -> sp.Expr:
    """Parse only the elementary integer-polynomial LaTeX used in these displays."""
    for command in (r"\left", r"\right", r"\quad"):
        text = text.replace(command, "")
    text = text.replace(r"\cdot", "*").replace("{", "(").replace("}", ")")
    text = text.strip().rstrip(",.").strip()
    if not re.fullmatch(r"[a-z0-9+*^()\s\-]+", text):
        raise ValueError(f"Unsupported polynomial fragment: {text!r}")
    expression = parse_expr(text, local_dict=LOCAL, transformations=TRANSFORMS)
    if not expression.free_symbols <= set(VARIABLES):
        raise ValueError(f"Unexpected symbols in {text!r}")
    return expression


def source_polynomials(tex: str) -> tuple[list[sp.Expr], list[sp.Expr]]:
    # Display (1) does not begin with the unprinted name prefix "P(a,b,\ldots,z)="
    # (76-R4-04), so anchor on its first line.
    start = tex.index(r"(k+2)\bigl\{1")
    stop = tex.index(r"\end{equation}", start)
    fragments = re.findall(r"&-\[(.*)\]\^2", tex[start:stop])
    if len(fragments) != 14:
        raise ValueError(f"Expected fourteen polynomial residuals; found {len(fragments)}")
    residuals = [parse_polynomial_fragment(t) for t in fragments]

    start = tex.index(r"\statement{Theorem 2.12.}")
    start = tex.index(r"\begin{align*}", start)
    stop = tex.index(r"\end{align*}", start)
    rows = re.findall(r"&\\text\{\((\d+)\)\}\\quad\s*(.*)", tex[start:stop])
    if [int(label) for label, _ in rows] != list(range(1, 15)):
        raise ValueError("Theorem 2.12 must contain equations (1)--(14) in order")
    equations = []
    for _, row in rows:
        row = row.rstrip("\\").strip().rstrip(",.")
        left, right = row.split("=")
        equations.append(parse_polynomial_fragment(right) - parse_polynomial_fragment(left))
    return residuals, equations


def pell(a: int, n: int) -> tuple[int, int]:
    if a < 1 or n < 0:
        raise ValueError("Require a >= 1 and n >= 0")
    x, y = 1, 0
    for _ in range(n):
        x, y = a*x + (a*a-1)*y, x+a*y
    return x, y


def proper_subtraction(a: int, b: int) -> int:
    return max(a-b, 0)


def run_checks(article: Path) -> dict[str, Any]:
    tex = article.read_text(encoding="utf-8")
    residuals, equations = source_polynomials(tex)
    k = LOCAL["k"]
    shifted = [sp.expand(e.subs(k, k+1)) for e in equations]
    mapping = []
    for residual in residuals:
        matches = [i+1 for i, e in enumerate(shifted)
                   if sp.expand(residual-e) == 0 or sp.expand(residual+e) == 0]
        assert len(matches) == 1, matches
        mapping.append(matches[0])
    assert sorted(mapping) == list(range(1, 15))
    polynomial = (k+2)*(1-sp.Add(*(e**2 for e in residuals)))
    expanded = sp.Poly(polynomial, *VARIABLES)
    assert expanded.total_degree() == 25
    assert len(polynomial.free_symbols) == 26
    assert len(expanded.terms()) == 917
    witness = dict(zip("abcdefghijklmnopqrstuvwxyz",
        [0,1,0,0,0,6,0,1,1,1,0,0,0,0,1,1,0,0,0,1,1,1,1,1,1,1]))
    assert polynomial.subs({LOCAL[t]: v for t,v in witness.items()}) == -76
    checks: list[dict[str, Any]] = [{
        "name": "Source-level polynomial identity",
        "status": "PASS", "residuals": 14,
        "polynomial_residual_to_theorem_equation": mapping,
        "total_degree": 25, "variables": 26, "expanded_nonzero_monomials": 917,
        "negative_value": -76, "negative_value_witness": witness,
    }]

    cases = 0
    for a in range(1, 21):
        for n in range(31):
            x,y = pell(a,n)
            x1,y1 = pell(a,n+1)
            x2,y2 = pell(a,n+2)
            assert x*x-(a*a-1)*y*y == 1
            assert x2 == 2*a*x1-x and y2 == 2*a*y1-y
            assert (2*a-1)**n <= y1 <= (2*a)**n
            assert y == n if a == 1 else (y-n) % (a-1) == 0
            cases += 1
    checks.append(dict(name="Pell identity, both recurrences, Lemmas 2.1--2.2",
                       status="PASS", cases=cases, ranges="1<=a<=20, 0<=n<=30"))

    cases = 0
    for a in range(1,11):
        for p in range(16):
            for n in range(13):
                x,y = pell(a,n)
                modulus = 2*a*p-p*p-1
                rhs = p**n+y*(a-p)
                assert (x-rhs) % modulus == 0 if modulus else x == rhs
                if 0 < p**n < a:
                    assert rhs <= x
                cases += 1
    checks.append(dict(name="Lemma 2.4, including the degenerate modulus",
                       status="PASS", cases=cases,
                       ranges="1<=a<=10, 0<=p<=15, 0<=n<=12; 0^0=1"))

    cases = 0
    max_index = 0
    for e in range(1,9):
        for t in range(1,6):
            a = e+1
            x,y = 1,0
            for j in range(1,10001):
                x,y = a*x+(a*a-1)*y, x+a*y
                if y % (e*t) == 0:
                    n = y//e-1
                    assert (n+1) % t == 0
                    assert e**3*(e+2)*(n+1)**2+1 == x*x
                    if e >= 2:
                        assert e-1+e**(e-2) <= n
                    max_index = max(max_index,j)
                    break
            else:
                raise AssertionError(f"Search limit reached for e={e}, t={t}")
            cases += 1
    checks.append(dict(name="Lemma 2.3 divisibility-compatible Pell witnesses",
                       status="PASS", cases=cases, ranges="1<=e<=8, 1<=t<=5",
                       largest_index_used=max_index))

    cases = 0
    for k0 in range(1,7):
        for delta_n in (0,1,3):
            n = (2*k0)**k0+delta_n
            for delta_p in (1,2):
                p = n**k0+delta_p
                # Modular exponentiation avoids constructing (p+1)^n in full.
                rem = pow(p+1,n,p**(k0+1))
                binomial_sum = sum(math.comb(n,i)*p**i for i in range(k0+1))
                assert rem == binomial_sum and rem > 0
                numerator = (n+1)**k0*p**k0
                assert math.factorial(k0)*rem < numerator < (math.factorial(k0)+1)*rem
                cases += 1
    checks.append(dict(name="Lemma 2.10 exact factorial bounds and remainder",
                       status="PASS", cases=cases,
                       ranges="1<=k<=6, n=(2k)^k+{0,1,3}, p=n^k+{1,2}"))

    cases = 0
    for q in range(1,31):
        for j in range(10):
            alpha = Q(j,10*q)
            assert 1-q*alpha <= (1-alpha)**q
            cases += 1
        for j in range(1,31):
            beta = 2*q+Q(j,3)
            assert (beta/(beta-1))**q <= 1+Q(2*q,1)/beta
            cases += 1
    for j in range(11):
        alpha = Q(j,20)
        assert 1/(1-alpha) <= 1+2*alpha
        cases += 1
    for n in range(1,13):
        for delta in range(1,5):
            M = n+delta
            for x in range(4):
                assert 1-Q(n,M) < (1-Q(1,2*M*(x+1)))**n
                cases += 1
    for n in range(1,21):
        for k0 in range(n):
            for offset in (1,17):
                x = 8*2**n+offset
                value = Q((x+1)**n,x**k0)
                floor = value.numerator//value.denominator
                assert 0 <= value-floor < Q(1,8)
                assert floor % x == math.comb(n,k0) % x
                assert math.comb(n,k0) < value
                cases += 1
    for k0 in range(1,31):
        for delta in (0,1,17):
            n = max(k0,2*(k0-1)**2+1)+delta
            assert Q(n**k0,math.comb(n,k0)) <= math.factorial(k0)*(1+Q(2*(k0-1)**2,n))
            cases += 1
    for a in range(1,101):
        assert a*(1+Q(1,10*a))**4 < a+Q(1,2)
        assert a*(1-Q(1,4*a))**2 > a-Q(1,2)
        cases += 2
    checks.append(dict(name="Elementary bounds (Lemmas 2.7, 2.8, 3.1--3.6)",
                       status="PASS", cases=cases, arithmetic="exact rational"))

    # Prefix sums are computed from factorials, not from a prime-recognition oracle.
    max_n = 100
    limit = max_n*max_n
    prefixes = []
    cumulative = 0
    fac = 1
    for j in range(limit+1):
        if j >= 2:
            fac *= j-1
        rem = 1 if j == 0 else (fac % j)**2 % j
        cumulative += rem
        prefixes.append(cumulative)
    sieve = [True]*(limit+1)
    sieve[0] = sieve[1] = False
    for p in range(2,math.isqrt(limit)+1):
        if sieve[p]:
            for m in range(p*p,limit+1,p):
                sieve[m] = False
    primes = [p for p,v in enumerate(sieve) if v]
    values = []
    for n in range(1,max_n+1):
        value = sum(proper_subtraction(1,proper_subtraction(prefixes[i],n))
                    for i in range(n*n+1))
        assert value == primes[n-1], (n,value,primes[n-1])
        values.append(value)
    for x in range(1001):
        lhs = 1 if x == 0 else 0
        assert lhs == proper_subtraction(1,x) == (abs(1-x)+1-x)//2
        assert lhs == 1-1%(1+x) == 1-int(x>0) == 1//(1+x)
    checks.append(dict(name="Corrected nth-prime formula and six zero-tests",
                       status="PASS", prime_cases=max_n, last_prime=values[-1],
                       zero_test_cases=1001, first_ten=values[:10]))

    C,K,L,R,W,X,S = sp.symbols("C K L R W X S")
    beta = R/((C/(K*L)-(W+1)*X)*(1-R/C)**2*L)
    den = (C-(W+1)*X*K*L)*(C-R)**2
    num = R*K*C**2
    assert sp.cancel(beta-num/den) == 0
    assert sp.cancel(den**2*(4*(beta-(S+1))**2-1)
                     -(4*(num-(S+1)*den)**2-den**2)) == 0
    N,F,B = sp.symbols("N F B")
    w = (F-B)/X-1
    assert sp.expand(16*N*X*(w+2)+1-(16*N*(F-B+X)+1)) == 0
    T = sp.symbols("T")
    factor = ((2*T-1)**2-1)*(N+1)**2*(X+1)**2*4+1
    assert sp.expand(factor-(16*T*(T-1)*(N+1)**2*(X+1)**2+1)) == 0
    checks.append(dict(name="Denominator clearing, corrected equation (23), equation (24)",
                       status="PASS", identities=4,
                       domain_note="Original denominators must be nonzero. Cleared strict inequality excludes denominator zero."))

    # Counterchecks of the two printed strict inequalities at k=1.
    assert Q(3,2) == 1/Q(2,3)
    assert 5 == math.prod(range(5,5-1,-1))
    checks.append(dict(name="Printed strict-inequality boundary counterexamples",
                       status="PASS", counterexamples=2,
                       details="Lemma 2.10 comparison: 3/2 = 3/2. Theorem 3.9 estimate: 5 = 5."))

    return dict(
        result="ALL CHECKS PASSED",
        python=platform.python_version(), sympy=sp.__version__, article=article.name,
        scope="Exact symbolic checks plus finite regression tests; not a formal proof of the whole article.",
        not_independently_reconstructed=[
            "The historical 87-addition/multiplication checking circuit",
            "The unexpanded 19-/42-/16-variable constructions mentioned in the introduction",
            "The complete relation-combining polynomials and historical degree counts 148864, 13376, 6848, 13697",
            "A formal proof of every existence statement or cited external theorem",
        ], checks=checks,
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--article", type=Path,
                        default=Path(__file__).resolve().parents[1] / "1976" / "jones1976_corrected.tex")
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().with_name("jones1976_verify_mathematics_results.json"))
    args = parser.parse_args()
    try:
        result = run_checks(args.article)
    except (OSError, ValueError, AssertionError) as exc:
        raise SystemExit(f"Verification failed: {exc}") from exc
    args.output.write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n",encoding="utf-8",newline="\n")
    lines = [result["result"], f"Python {result['python']}; SymPy {result['sympy']}",result["scope"],""]
    for test in result["checks"]:
        lines.append(f"PASS: {test['name']}")
        for key,value in test.items():
            if key not in ("name","status"):
                lines.append(f"  {key}: {value}")
    lines += ["", "Not independently reconstructed:"]
    lines += ["  "+x for x in result["not_independently_reconstructed"]]
    report = "\n".join(lines)+"\n"
    args.output.with_suffix(".txt").write_text(report,encoding="utf-8",newline="\n")
    print(report)


if __name__ == "__main__":
    main()
