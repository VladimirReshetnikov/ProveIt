#!/usr/bin/env python3
"""Exact rational residual enclosure for the unproved S6 conjecture.

Uses only Python's standard library. Euler sums are computed exactly with a
common integer denominator. Every truncation tail is bounded analytically.
A residual interval containing zero does NOT prove the conjectured equality.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import lcm
from pathlib import Path
import argparse
import json

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,default=Path(__file__).with_name('s6_rational_certificate.json'),
                    help='Destination JSON file (default: beside this script).')
cli=parser.parse_args()

N=900
DIGITS=280
COEFFICIENTS=[485683200,-665395200,-36864000,401080320,
              -258247,11750400,109347840,971366400]
NAMES=['S6','g61','g43','g25','pi^7','G*zeta(5)','beta(4)*zeta(3)','beta(6)*log(2)']

# Every denominator in the N input terms divides a power of this integer.
LCM=1
for j in range(1,2*N+1):
    LCM=lcm(LCM,j)
TWO=1<<N
TAILS=[]
remaining=TWO-1
binomial=1
for n in range(N):
    TAILS.append(remaining)
    binomial=binomial*(N-n)//(n+1)
    remaining-=binomial
assert remaining==0


def harmonic_euler(a,b,q):
    """L=sum (-1)^n H_{q*n}^{(b)}/(2n+1)^a lies in [E-R,E]."""
    h_scaled=0
    previous=0
    numerator=0
    for n in range(N):
        for j in range(previous+1,q*n+1):
            h_scaled+=(LCM//j)**b
        previous=q*n
        term=h_scaled*(LCM//(2*n+1))**a*TAILS[n]
        numerator+=term if n%2==0 else -term
    E=F(numerator,TWO*LCM**(a+b))
    c1=sum((F(1,j**b) for j in range(1,q+1)),F(0))/3**a
    R=(N+1)*c1/TWO
    return (E-R,E),E,R

@lru_cache(None)
def elementary_euler(s,d):
    """sum (-1)^n/(d*n+1)^s lies in [E,E+2^-N], d=1 or2."""
    numerator=0
    for n in range(N):
        term=(LCM//(d*n+1))**s*TAILS[n]
        numerator+=term if n%2==0 else -term
    E=F(numerator,TWO*LCM**s)
    return E,E+F(1,TWO)

def scale(I,c):
    c=F(c)
    return (c*I[0],c*I[1]) if c>=0 else (c*I[1],c*I[0])
def add(A,B):return A[0]+B[0],A[1]+B[1]
def multiply(A,B):
    vals=[a*b for a in A for b in B]
    return min(vals),max(vals)
def power(A,k):
    out=(F(1),F(1))
    for _ in range(k):out=multiply(out,A)
    return out

def arctan_inverse(q,terms):
    value=sum((F((-1)**n,(2*n+1)*q**(2*n+1)) for n in range(terms)),F(0))
    next_term=F(1,(2*terms+1)*q**(2*terms+1))
    return (value,value+next_term) if terms%2==0 else (value-next_term,value)

def fixed_integer(k,digits):
    sign='-' if k<0 else ''
    raw=str(abs(k)).rjust(digits+1,'0')
    return sign+raw[:-digits]+'.'+raw[-digits:]
def decimal_interval(I):
    scale10=10**DIGITS
    lower=(I[0].numerator*scale10)//I[0].denominator
    upper=-((-I[1].numerator*scale10)//I[1].denominator)
    return {'lower':fixed_integer(lower,DIGITS),'upper':fixed_integer(upper,DIGITS),
            'decimal_places':DIGITS,'rounding':'outward; endpoints are exact finite decimals'}

intervals=[]
nonclassical=[]
for name,args in zip(NAMES[:4],[(6,1,1),(6,1,2),(4,3,2),(2,5,2)]):
    interval,E,R=harmonic_euler(*args)
    intervals.append(interval)
    nonclassical.append({'name':name,'a_b_q':list(args),'interval':decimal_interval(interval),
                         'tail_bound_numerator':str(R.numerator),'tail_bound_denominator':str(R.denominator)})
    print('Certified',name,flush=True)
pi_interval=add(scale(arctan_inverse(5,240),16),scale(arctan_inverse(239,80),-4))
G=elementary_euler(2,2)
zeta3=scale(elementary_euler(3,1),F(4,3))
zeta5=scale(elementary_euler(5,1),F(16,15))
beta4=elementary_euler(4,2)
beta6=elementary_euler(6,2)
log2=elementary_euler(1,1)
intervals.extend([power(pi_interval,7),multiply(G,zeta5),multiply(beta4,zeta3),multiply(beta6,log2)])
residual=(F(0),F(0))
for c,I in zip(COEFFICIENTS,intervals):residual=add(residual,scale(I,c))
assert residual[0]<=0<=residual[1], 'Candidate is excluded by the certified intervals.'
absolute=max(abs(residual[0]),abs(residual[1]))
digits_bound=0
while absolute<F(1,10**(digits_bound+1)):
    digits_bound+=1
assert digits_bound>=260
assert -F(1,10**260)<residual[0]<=residual[1]<F(1,10**260)
report={
 'claim':'Certified numerical enclosure only; the S6 identity remains unproved',
 'euler_terms':N,'coefficients':COEFFICIENTS,'ordered_basket':NAMES,
 'nonclassical_values':nonclassical,
 'basket_intervals':dict(zip(NAMES,map(decimal_interval,intervals))),
 'integer_normalized_residual_interval':decimal_interval(residual),
 'residual_interval_contains_zero':True,
 'rigorous_absolute_residual_upper_bound':f'1e-{digits_bound}',
 'harmonic_euler_bound':'0 <= E_N - L <= (N+1)*2^(-N)*H_q^(b)/3^a',
 'elementary_euler_bound':'0 <= L - E_N <= 2^(-N)',
 'pi_bound':'16 atan(1/5) - 4 atan(1/239), alternating-series remainder bounds, 240 and 80 terms',
 'arithmetic':'All computations exact fractions and integers; decimal intervals rounded outward'
}
output=cli.output
output.parent.mkdir(parents=True,exist_ok=True)
output.write_text(json.dumps(report,indent=2)+'\n')
print(f'Certified integer residual contains zero and has absolute value < 1e-{digits_bound}.')
print(output)
