"""Independent integer-scaled direct convolution of H(z)^Y."""
from math import lcm
from pathlib import Path
import json
RMAX=60;YMAX=128;primes=[2,3,5,7,11,13,17,19,23,29,31]
def vp(n,p):
 if n==0:raise RuntimeError('zero coefficient')
 n=abs(n);v=0
 while n%p==0:n//=p;v+=1
 return v
D=lcm(*range(1,RMAX+2))
H=[D]+[((-1)**(j-1))*D//(j*(j+1)) for j in range(1,RMAX+1)]
P=[1]+[0]*RMAX
principal=shifted=denominator=0;boundary=0
for p in primes:
 for j in range(1,501):
  v=vp(j*(j+1),p)
  if (p-1)*v>j or ((p-1)*v==j)!=(j==p-1):raise RuntimeError(('denominator',p,j))
  if p>2 and j-(p-1)*v in (0,1) and j not in(1,p-1,p):raise RuntimeError(('shifted denominator',p,j))
  denominator+=1
for Y in range(1,YMAX+1):
 Q=[0]*(RMAX+1)
 for r in range(RMAX+1):Q[r]=sum(P[r-j]*H[j] for j in range(r+1))
 P=Q
 for p in primes:
  e=vp(Y,p);deduct=Y*vp(D,p)
  for m in range(1,RMAX//(p-1)+1):
   r=(p-1)*m
   if m<=p**e:
    actual=vp(P[r],p)-deduct;expected=e-vp(m,p)-m
    if actual!=expected:raise RuntimeError(('principal',Y,p,m,actual,expected))
    principal+=1;boundary+=m==p**e
   r+=1
   if p>2 and r<=RMAX and m<p**e and r%p:
    actual=vp(P[r],p)-deduct;expected=e-m
    if actual!=expected:raise RuntimeError(('shifted',Y,p,m,actual,expected))
    shifted+=1
out={'max_defect':RMAX,'max_exponent':YMAX,'primes':primes,'principal_checks':principal,'shifted_checks':shifted,'principal_boundary_m_equals_p_power_e':boundary,'denominator_checks':denominator,'all_pass':True}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
