"""Numerical diagnostics for the new polynomial-subtracted identities.

Two independent cutoff/expansion settings are recorded.  These diagnostics
are not interval certificates; the all-index proof is algebraic and analytic.
"""
from pathlib import Path
from math import comb
import json
import mpmath as mp
import sympy as s

mp.mp.dps=110

def coeffs(d,J):
    b=[s.bernoulli(2*j,s.Rational(1,2)) for j in range(J+1)]
    h=[s.S.One]+[s.S.Zero]*J
    for _ in range(d):
        h=[sum(h[k]*b[j-k] for k in range(j+1)) for j in range(J+1)]
    return [mp.mpf(str(s.numer(x)))/mp.mpf(str(s.denom(x))) for x in h]

def evaluate(d,poly,N,J):
    h=coeffs(d,J)
    total=mp.mpf(0)
    for n in range(N):
        x=mp.mpf(n)+mp.mpf('0.5')
        p=sum(mp.mpf(c)*x**m for m,c in poly.items())
        subtraction=sum(mp.mpf(c)*h[j]*x**(m-d-2*j)
                        for m,c in poly.items() for j in range(max(0,(m-d)//2+1)))
        total+=p*mp.polygamma(1,n+1)**d-subtraction
    for m,c in poly.items():
        for j in range(max(0,(m-d)//2+1),J+1):
            total+=mp.mpf(c)*h[j]*mp.zeta(d+2*j-m,mp.mpf(N)+mp.mpf('0.5'))
    return total

def main():
    z=mp.zeta
    Q5=4*z(2)*z(3)-10*z(5)
    Q7=51*z(3)*z(4)+10*z(2)*z(5)-mp.mpf(301)/4*z(7)
    tasks=[(5,{1:195,3:4056,5:11568,7:5376},
            -748*z(2)+7884*z(3)-5380*z(4)+171*z(6)-748),
           (5,{1:23,3:232,5:240},
            80*Q5-20*z(2)+1140*z(3)-560*z(4)-57*z(6)-20),
           (6,{0:35,2:3360,4:29792,6:50176,8:16128},
            9184*Q5-64*Q7-2928*z(2)+111216*z(3)-55368*z(4)-9576*z(6)-2928)]
    records=[]
    for d,poly,target in tasks:
        rec={'power':d,'polynomial':poly,'target':mp.nstr(target,100),'diagnostics':[]}
        for N,J in [(128,40),(256,56)]:
            value=evaluate(d,poly,N,J)
            error=abs(value-target)
            assert error<mp.mpf('1e-70'),(d,N,J,error)
            rec['diagnostics'].append({'head_terms':N,'asymptotic_order':J,
                'value':mp.nstr(value,100),'absolute_residual':mp.nstr(error,12)})
        records.append(rec)
        print('power',d,'value',mp.nstr(target,45),'residuals',
              [v['absolute_residual'] for v in rec['diagnostics']])
    Path(__file__).with_name('allpowers_numerics.json').write_text(json.dumps({
        'status':'PASS','working_decimal_digits':mp.mp.dps,
        'qualification':'Numerical diagnostics, not interval certificates.','checks':records},indent=2)+'\n')

if __name__=='__main__':main()
