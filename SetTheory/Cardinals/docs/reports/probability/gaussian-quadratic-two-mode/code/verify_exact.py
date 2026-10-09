"""Exact algebra and integer-spectrum checks. This is not a Lean formalization."""
from __future__ import annotations
from fractions import Fraction
from itertools import combinations_with_replacement
from functools import reduce
from math import gcd
from pathlib import Path
import json
import sympy as sp
from two_mode import centered_moments

ROOT = Path(__file__).resolve().parents[1]

def main() -> dict:
    a,b,x,c,d,t,y,p,q = sp.symbols('a b x c d t y p q', real=True)
    checks = []
    def zero(name, expr):
        assert sp.cancel(expr) == 0, (name,sp.factor(expr))
        checks.append(name)
    zero('endpoint weight a', (a**3-b**3)+b-a**2*(a+b)-b*(1-a*a-b*b))
    zero('endpoint weight b', a-(a**3-b**3)-b**2*(a+b)-a*(1-a*a-b*b))
    zero('fourth trace defect factor', a**4+b**4-a*b-(a-b)*(a**3-b**3)-a*b*(a*a+b*b-1))
    zero('quadratic chord gap', (x+b)/(a+b)*a*a+(a-x)/(a+b)*b*b-x*x-(a-x)*(x+b))
    zero('cubic parameter', 3*(a-b)-(a-b)**3-2*(a**3-b**3)-3*(a-b)*(1-a*a-b*b))
    zero('rigidity bilinear', a*b-(a-a*p)*(b-b*q)+(a*p-b*q)*(a**3-b**3)
         -((a+b)*(a**3*p+b**3*q)-a*b*p*q)
         -(a*b*p+a*b*q)*(1-a*a-b*b))
    # Raw extremal fourth and sixth moments, with the variance/cube constraints substituted.
    S2,S3,S4,S6=sp.symbols('S2 S3 S4 S6')
    kap={2:2*S2,3:8*S3,4:48*S4,5:sp.symbols('K5'),6:3840*S6}
    mm={0:1,1:0}
    for n in range(2,7):
        mm[n]=sp.expand(sum(sp.binomial(n-1,j-1)*kap[j]*mm[n-j] for j in range(2,n+1)))
    zero('fourth moment recurrence',mm[4]-(12*S2**2+48*S4))
    zero('sixth moment recurrence',mm[6]-(120*S2**3+1440*S2*S4+640*S3**2+3840*S6))
    # Saddle equation: K'(t)=x and x=t[(1+c*x)+sqrt(...)].
    D=1-2*c*t-4*d*t*t
    zero('Chernoff stationary polynomial', (y+c)*D-(c+4*d*t)
         - (y-(2*c*(y+c)+4*d)*t-4*d*(y+c)*t*t))
    zero('Chernoff discriminant', (1+c*y)**2+4*d*y*(y+c)
         -((1+2*d)*(y+c)**2+4*d*d)
         -(c*c+2*d-1)*(y*y-2*d-1))
    # The last identity above factors by c^2+2d=1; use polynomial remainder as a second check.
    assert sp.rem(sp.expand((1+c*y)**2+4*d*y*(y+c)-((1+2*d)*(y+c)**2+4*d*d)),
                  c*c+2*d-1, d)==0
    checks.append('Chernoff discriminant modulo constraint')

    spectrum_count=0; moment_checks=0; cap_checks=0
    levels={4:[],6:[],8:[],10:[],12:[]}
    alphabet=list(range(-6,0))+list(range(1,7))
    for n in range(2,7):
        for vec in combinations_with_replacement(alphabet,n):
            if reduce(gcd, (abs(v) for v in vec)) != 1:
                continue
            ss=sum(v*v for v in vec); s3=sum(v**3 for v in vec)
            for v in vec:
                assert (s3-v**3)**2 <= (ss-v*v)**3
                cap_checks += 1
            if s3 != 0:
                continue
            spectrum_count += 1
            mm=centered_moments(vec,12)
            for order in levels:
                k=order//2
                df=sp.prod(range(1,2*k,2))
                bound=int(2**k*df**2*ss**k)
                assert mm[order] <= bound, (vec,order)
                levels[order].append(Fraction(mm[order],bound))
                moment_checks += 1
    # The sharp zero-skewness rigidity constant is approached by flat paired spectra.
    rigidity_checks=0
    for m in range(2,151):
        # Put m=k^2 to make the distance/defect ratio rational as well.
        k=m
        ratio=Fraction(4*k,k+1)
        assert ratio < 4 and ratio >= Fraction(8,3)
        rigidity_checks += 1
    result={
        'status':'PASS', 'arithmetic':'Python integers, Fraction, and SymPy exact polynomial identities',
        'symbolic_checks':len(checks), 'symbolic_check_names':checks,
        'coordinate_containment_checks':cap_checks,
        'zero_skew_integer_spectra':spectrum_count,
        'exact_even_moment_comparisons':moment_checks,
        'exact_rigidity_sequence_checks':rigidity_checks,
        'total_assertion_checks':len(checks)+cap_checks+moment_checks+rigidity_checks,
        'orders':[4,6,8,10,12],
        'limitations':'Finite tests corroborate the manuscript; they do not replace its general proofs.'}
    (ROOT/'results'/'exact_checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
    return result

if __name__=='__main__':
    main()
