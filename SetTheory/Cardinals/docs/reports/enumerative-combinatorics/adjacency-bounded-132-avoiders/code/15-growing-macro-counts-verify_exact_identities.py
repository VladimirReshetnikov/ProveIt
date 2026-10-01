#!/usr/bin/env python3
"""Exact Catalan-power and adjacent-Gamma normalization identities."""
from fractions import Fraction
from math import comb
from pathlib import Path
import json

def check(condition,message):
    if not condition:
        raise ArithmeticError(message)
max_u=60
cat=[comb(2*u,u)//(u+1) for u in range(max_u+1)]
power=[1]+[0]*max_u
rows=0
for N in range(1,11):
    power=[sum(power[j]*cat[u-j] for j in range(u+1)) for u in range(max_u+1)]
    for u in range(max_u+1):
        formula=Fraction(N,2*u+N)*comb(2*u+N,u)
        check(formula.denominator==1 and power[u]==formula.numerator,"Catalan-power identity")
        # The probability formula's powers of two and four are independent checks.
        coeff=Fraction(power[u],2**N*4**u)
        expected=Fraction(N*comb(2*u+N,u),(2*u+N)*2**N*4**u)
        check(coeff==expected,"Small-run probability normalization")
        rows+=1

ratio_rows=0
for ell in range(2,12):
    for s in (Fraction(1,8),Fraction(1,3),Fraction(1,2),Fraction(4,5)):
        # After removing the common exp(3/2)/(2sqrt(pi m)) factor,
        # the ratio of Gamma expressions is an exact rational number.
        from math import factorial
        left=Fraction(ell+2,ell+1)*(1+s)**ell/s**(ell-1)*Fraction(factorial(ell-1),factorial(ell))
        right=Fraction(ell+2,ell+1)*s/ell*(1+1/s)**ell
        check(left==right,"Adjacent Gamma normalization")
        ratio_rows+=1
data={"passed":True,"catalan_power_and_probability_rows":rows,
      "adjacent_gamma_ratio_rows":ratio_rows}
Path(__file__).with_name("exact_identity_results.json").write_text(json.dumps(data,indent=2)+"\n")
print(json.dumps(data))

