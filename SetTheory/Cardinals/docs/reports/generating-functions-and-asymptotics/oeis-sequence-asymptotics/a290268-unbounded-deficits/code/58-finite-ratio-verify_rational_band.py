#!/usr/bin/env python3
"""Exact rational Taylor certificate that kappa_c > 1/36."""
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import json
x=Q(74,25)
def S(n):
    return sum(((-1)**j*x**(2*j+1)/factorial(2*j+1) for j in range(n+1)),Q(0))
def C(n):
    return sum(((-1)**j*x**(2*j)/factorial(2*j) for j in range(n+1)),Q(0))
# All omitted Taylor terms decrease: for the sine tail the first
# denominator ratio is 12*13; for cosine it is 11*12 (at n=5).
# Thus S_5 < sin x < S_6 and C_5 < cos x < C_6.
if not (x*x<Q(12*13) and x*x<Q(11*12)):
    raise RuntimeError('Alternating tail monotonicity was not verified')
K_lower=S(5)/x-2*C(6)-2
F_lower=(2*x*x-1)*S(5)+x*C(5)
if not K_lower>Q(1,36):
    raise RuntimeError('Saddle parameter did not exceed 1/36')
if not F_lower>0:
    raise RuntimeError('Positive curvature branch was not verified')
# The standard bounds 31/10 < pi < 22/7 locate x in (3pi/4,pi).
if not (x>Q(3,4)*Q(22,7) and x<Q(31,10)):
    raise RuntimeError('Trigonometric branch interval was not verified')
certificate={
    't':str(x),'target_ratio':'1/36',
    'K_lower':str(K_lower),'K_lower_minus_1_over_36':str(K_lower-Q(1,36)),
    'F_lower':str(F_lower),
    'sine_lower_partial_sum':'sum_{j=0}^5 (-1)^j t^(2j+1)/(2j+1)!',
    'cosine_lower_partial_sum':'sum_{j=0}^5 (-1)^j t^(2j)/(2j)!',
    'cosine_upper_partial_sum':'sum_{j=0}^6 (-1)^j t^(2j)/(2j)!',
    'conclusion':'t0 < 74/25 < tc and 1/36 < K(74/25) < kappa_c'
}
Path(__file__).with_name('rational_band_certificate.json').write_text(json.dumps(certificate,indent=2)+'\n')
print(certificate['conclusion'])
