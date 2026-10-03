"""Independent direct rational-power check of the Stirling residue and root shift."""
from fractions import Fraction as Q
from math import factorial, comb
from pathlib import Path
import json
primes=[3,5,7,11,13,17,19]
MMAX=8;R=max(MMAX*(p-1) for p in primes)
h=[Q(1)]+[Q((-1)**(j-1),j*(j+1)) for j in range(1,R+1)]
logh=[Q(0)]
for n in range(1,R+1):logh.append(h[n]-sum((j*logh[j]*h[n-j] for j in range(1,n)),Q(0))/n)
powers=[[Q(1)]+[Q(0)]*R]
for j in range(1,MMAX):powers.append([sum((powers[-1][i]*h[n-i] for i in range(n+1)),Q(0)) for n in range(R+1)])
st=[[1]]
for m in range(1,MMAX+1):
 row=[0]*(m+1)
 for j in range(1,m+1):row[j]=(st[-1][j-1] if j-1<len(st[-1]) else 0)+(m-1)*(st[-1][j] if j<len(st[-1]) else 0)
 st.append(row)
def modq(q,p):
 if q.denominator%p==0:raise RuntimeError(('nonintegral',q,p))
 return q.numerator*pow(q.denominator,-1,p)%p
count=0;triangle=0;shift=0
for p in primes:
 for m in range(2,min(MMAX,p-1)+1):
  r=m*(p-1)
  for j in range(1,m):
   c=st[m][j]
   expected=-Q(factorial(j)**2*factorial(m-j-1)*c,factorial(m)*factorial(m-1))
   actual=p**(j-1)*powers[j][r]
   if modq(actual-expected,p):raise RuntimeError(('residue',p,m,j))
   count+=1
   M=r+j;b=Q(factorial(M),factorial(j))*powers[j][r]
   if b.denominator!=1:raise RuntimeError(('triangle integer',M,j))
   expected_b=Q((-1)**j*factorial(j)*c,factorial(m))
   if modq(b/Q(p**(m-j))-expected_b,p):raise RuntimeError(('triangle residue',p,m,j))
   triangle+=1
   deriv=sum((powers[j][i]*logh[r-i] for i in range(r+1)),Q(0))*p**m
   expected_deriv=Q(factorial(j)*(-1)**(m-1-j)*factorial(m-1-j),factorial(m))
   if modq(deriv-expected_deriv,p):raise RuntimeError(('derivative',p,m,j))
   root_unit=-modq(expected,p)*pow(modq(deriv,p),-1,p)%p
   shift_unit=modq(Q((-1)**(m-1-j)*factorial(j)*c,factorial(m-1)),p)
   if root_unit!=shift_unit:raise RuntimeError(('root shift',p,m,j))
   shift+=1
out={'maximum_multiplier':MMAX,'maximum_coefficient_degree':R,'primes':primes,'Stirling_residue_checks':count,'scaled_triangle_checks':triangle,'root_derivative_and_displacement_checks':shift,'rows':{str(m):st[m][1:m] for m in range(2,MMAX+1)},'all_pass':True}
Path(__file__).with_name('stirling_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
