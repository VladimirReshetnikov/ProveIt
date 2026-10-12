#!/usr/bin/env python3
"""A small pure-integer upper bound for the inherited retained-entry norms."""
from math import factorial,comb,prod
from fractions import Fraction
from pathlib import Path
import json
import sys
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)

def polymul(p,q):
    r=[0]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q):r[i+j]+=x*y
    return r

def newton_coefficients(a,i):
    rows=[]
    for j in range(2*i+2):
        p=[-2*a+2*i+2-j,2]
        for r in range(2*i):p=polymul(p,[-4*a+4*i+2-j-r,4])
        rows.append(p)
    out={}
    for h in range(1,2*i+2,2):
        coeff=[sum((-1)**(h-j)*comb(h,j)*rows[j][k] for j in range(h+1))
               for k in range(2*i+2)]
        assert all(c%factorial(h)==0 for c in coeff)
        out[h]=[c//factorial(h) for c in coeff]
    return out

def get_bound(a):
    # Each pair (c,s) denotes the polynomial s*b+c.
    J=[(-2*a+2*i+v,2) for i in range(a) for v in [1,2]]
    E=[(-2*a+2+2*l+r,2) for i in range(a) for l in range(a)
                         for r in range(1,max(0,2*i-4*l-1)+1)]
    norm=lambda factors:prod(abs(c)+abs(s) for c,s in factors)
    values=[]
    for i in range(a):
        dc=newton_coefficients(a,i)
        Ji=J[:];Ji.remove((-2*a+2*i+1,2));Ji.remove((-2*a+2*i+2,2))
        row=[]
        for l in range(a):
            Fs=[pair for r in range(2*l) for pair in
                 [(-2*a+2*i-r,2),(-2*a+2*i+3+r,2)]]
            value=2*(factorial(2*a)//factorial(2*l+1))*norm(J)*norm(E)*norm(Fs)
            diff=1+4*l-2*i
            Ef=E[:]
            if diff>=0:
                Ef += [(-2*a+2*i-2*l+1+r,2) for r in range(1,diff+1)]
            else:
                for r in range(1,-diff+1):Ef.remove((-2*a+2+2*l+r,2))
            common=(factorial(2*a)//factorial(2*l+2))*norm(Ji)*norm(Ef)
            for h,d in dc.items():
                Nf=[(-2*a+2*i-2*l+1-r,2) for r in range(h)]
                value += common*sum(abs(c) for c in d)*norm(Nf)
            row.append(value)
        values.append(row)
    Ebound=max(map(max,values))
    K=factorial(a)*Ebound**a
    kap=Fraction(factorial(a)*factorial(2*a)**a,prod(factorial(2*l+2) for l in range(a)))
    points=[Fraction(1,j*j) for j in range(1,a+1)]
    V=prod((points[j]-points[i])**2 for i in range(a) for j in range(i+1,a))
    L=4*(a-1)**2;chi=2*a*a-6*a+2
    C=Fraction(K*8**(a-1+max(chi,0))*2**L,kap*4**a*V*factorial(a)**(4*a-2))
    B=max(4*a+10,L,16*factorial(a))
    initial=B
    while C.numerator*B**L*(8*factorial(a))**(2*B)>=C.denominator*factorial(2*B-4*a+2):B+=1
    # Stronger exact inequality useful for a compact report of the certificate.
    num=C.numerator*B**L*(8*factorial(a))**(2*B)
    den=C.denominator*factorial(2*B-4*a+2)
    excess_bits=den.bit_length()-num.bit_length()-1
    assert num*2**max(excess_bits,0)<den
    return {'a':a,'smaller_order':2*a,'entry_norm_upper_bound':str(Ebound),
      'entry_norm_bound_matrix':[[str(v) for v in row] for row in values],
      'e':len(E),'g':6*a*a-4*a+a*len(E),'kappa':str(kap),'V':str(V),
      'L':L,'chi':chi,'C':str(C),'initial_B':initial,'proved_B':B,
      'bound_strictly_below_2_to_minus':max(excess_bits,0),
      'proof_method':'factor norm product and exact integer inequality',
      'all_checks_passed':True}

if __name__=='__main__':
    a=int(sys.argv[1]) if len(sys.argv)>1 else 6
    result=get_bound(a)
    Path(__file__).with_name(f'coefficient_norm_bound_a{a}.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['C','entry_norm_bound_matrix']},indent=2))
