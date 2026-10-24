#!/usr/bin/env python3
"""Independently authored exact arithmetic regressions; not a universal proof."""
import json, math
from fractions import Fraction
from pathlib import Path

def pell(a,k):
    X,Z=1,0
    for _ in range(k): X,Z=a*X+(a*a-1)*Z,X+a*Z
    return X,Z

count=0
for S in range(1,9):
 for T in range(1,9):
    n=S+T; e=2*n+4; X,z=pell(e+3,e+2)
    assert z%(e+2)==0
    y=z//(e+2)-1; x=2*(y+1)
    assert X*X==(e+2)**3*(e+4)*(y+1)**2+1
    assert x>128*2**n
    rho=Fraction((x+1)**n,x**S); Q=rho.numerator//rho.denominator
    Y=Q if Q%2 else Q+1
    M=128*(n+1)*(x+1)*(Y+1); A=M*(x+1)
    C=pell(A,n+1)[1];K=pell(M,T+1)[1];L=pell(M*x,S+1)[1]
    sig=Fraction(C,K*L); eps=Fraction(n,2*M)
    assert abs(sig-rho)<=sig*eps/(1-eps)<Fraction(1,128)
    assert abs(sig-Y)<Fraction(1,8) if (S&T)==0 else abs(sig-Y)>=Fraction(1,8)
    assert (K-(T+1))%(M-1)==0 and (L-(S+1))%(M*x-1)==0
    assert (2*M-1)**2>2*A and M-1>=2*n+1
    count+=1
# Independent degree propagation. Multiplication adds; additions take max.
d={'n':1,'x':1,'Y':1,'C':1}
d['M']=d['n']+d['x']+d['Y'];d['A']=d['M']+d['x']
d['K']=1+d['M'];d['L']=1+d['M']+d['x']
d['D']=2*d['A']+2*d['C'];d['E']=1+d['D']+2*d['C']
d['F']=2*d['A']+2*d['E'];d['G']=2*d['F']
d['H12']=d['F']+1+d['C'];d['I12']=2*d['G']+2*d['H12']
d['P12']=2*(d['D']+d['F']+d['I12'])
d['H13']=2;d['I13']=2*d['G']+2*d['H13'];d['P13']=2*(d['D']+d['F']+d['I13'])
assert d['P12']==504 and d['P13']==368
# Toy congruence-compression checks independent of astronomical certificates.
congruences=0
for C in range(3,15):
 for B in range(2,C+1):
  for t in range(1,5):
   F=1+2*C*t
   for j in range(5):
    H=C+F*(B+(2*j+1)*C)
    assert (H-B)%(2*C)==0 and (H-C)%F==0 and H>=B+2*C
    oldj=(H-B)//(2*C)-1
    assert oldj>=0 and H==B+2*(oldj+1)*C
    congruences+=1
receipt={'status':'pass','exact_ratio_input_pairs':count,'congruence_cases':congruences,'degree_propagation':d,'limitations':'Finite regressions do not prove the unbounded theorem or construct complete MR witnesses. See AUDIT.md for the universal mathematical argument.'}
print(json.dumps(receipt,indent=2))
