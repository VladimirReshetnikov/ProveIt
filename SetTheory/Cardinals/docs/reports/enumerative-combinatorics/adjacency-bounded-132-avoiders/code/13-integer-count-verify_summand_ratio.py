#!/usr/bin/env python3
"""Exact rational regression for the adjacent Gamma-summand ratio."""
from fractions import Fraction
from math import factorial
import json
from pathlib import Path

count=0
for ell in range(1,21):
    for a in range(1,11):
        s=Fraction(a,7)
        first=(ell+1)*s**(ell-1)/(2**ell*factorial(ell-1))
        second=(ell+2)*(s+1)**ell/(2**(ell+1)*factorial(ell))
        ratio=Fraction(ell+2,ell+1)*s/(2*ell)*(1+1/s)**ell
        assert second/first==ratio
        count+=1
result={'status':'passed','arithmetic':'exact rational','checks':count,
        'scope':'Adjacent-summand identity after removing the common exponential and square-root factors; no asymptotic extrapolation.'}
Path(__file__).with_name('summand_ratio_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,sort_keys=True))
