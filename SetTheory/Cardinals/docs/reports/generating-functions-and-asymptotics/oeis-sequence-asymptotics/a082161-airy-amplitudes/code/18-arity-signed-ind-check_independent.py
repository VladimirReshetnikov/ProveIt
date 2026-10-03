from fractions import Fraction as F
from math import factorial
import json
from pathlib import Path
import sympy as s
counts={'source_vs_run_all_entries':0,'signed_transforms':0,'scaled_beta_identities':0,'ratio_constants':0,'published_table_entries':0}
reported={}
for k in range(3,11):
 q=k-1; nmax=9; xmax=q*nmax
 for typ in ['R','C','B']:
  arr={(x,0):F(1) for x in range(xmax+1)}
  if typ=='B':arr[-1,0]=F(1)
  for m in range(1,nmax+1):
   for x in range(q*m,xmax+1):
    delta=F(m,2) if typ=='B' else F(m-1) if typ=='C' else F(0)
    arr[x,m]=arr.get((x,m-1),0)+(m+1)*arr.get((x-1,m),0)-delta*arr.get((x-k,m-1),0)
  # arr is already b/2^m; auxiliary b(-1,0) remains one
  completed={0:F(1)}
  for m in range(1,nmax+1):
   level=m-1; new={}
   for start,prefix in completed.items():
    for end in range(max(start,q*m),xmax+1):
     ell=end-start; weight=F(m**ell)
     if typ=='B' and m==1:weight/=2
     elif ell>=k:
      if typ=='B':weight*=1-F(1,2*m**q)
      if typ=='C':weight*=1-F(m-1,m**k)
     new[end]=new.get(end,0)+prefix*weight
   completed=new
   for x in range(q*m,xmax+1):
    value=sum(v*(m+1)**(x-end) for end,v in completed.items() if end<=x)
    assert value==arr[x,m],(k,typ,x,m)
    counts['source_vs_run_all_entries']+=1
  def d(i,j):
   if i<0 or j<0 or j>i or (i-j)%k:return F(0)
   x=(q*i+j)//k;m=(i-j)//k
   return F(q**(2*x),factorial(x))*arr.get((x,m),0)
  for (x,m),val in arr.items():
   i=x+m;j=x-q*m
   if x<0 or i<k+1:continue
   delta=F(m,2) if typ=='B' else F(m-1) if typ=='C' and m else F(0)
   coeff=delta*F(q**(2*k),1)
   for r in range(k):coeff/=x-r
   rhs=F(q*q*(m+1),x)*d(i-1,j-1)+d(i-1,j+q)-coeff*d(i-k-1,j-1)
   assert rhs==d(i,j),(k,typ,i,j)
   counts['signed_transforms']+=1
  if k<=5:reported[f'{k}{typ}']=[int(arr[q*n,n]*(2**n if typ=='B' else 1)) for n in range(7)]
 # Independent symbolic rational substitution, with a fresh epsilon and height
 e,h=s.symbols('e h');i=e**-3;j=h/e-1;X=(q*i+j)/k;m=(i-j)/k
 den=s.prod(q+h*e**2-(1+k*r)*e**3 for r in range(k))
 for typ,delta,numerator in [('B',m/2,1-h*e**2+e**3),('C',m-1,1-h*e**2-q*e**3)]:
  beta=delta*q**(2*k)/s.prod(X-r for r in range(k))
  expected=q**(2*k)*k**(k-1)*e**(3*q)*numerator/den/(2 if typ=='B' else 1)
  assert s.cancel(beta-expected)==0
  counts['scaled_beta_identities']+=1
  beta_lead=F(q**k*k**(k-1),2 if typ=='B' else 1)
  delta_sigma=-beta_lead/F(k**k)
  delta_h=-delta_sigma/F(k*(q-1))
  count_coefficient=delta_h/F(k**(q-1))
  assert count_coefficient==F(q,k)**k/F((k-2)*(2 if typ=='B' else 1))
  counts['ratio_constants']+=1
expected={'3C':[1,1,7,133,5299,371329,40898599], '4C':[1,1,15,975,182175,75961695,60422966655], '5C':[1,1,31,6541,5373571,12458850121,66790559866471], '3B':[1,1,14,532,42644,6011320,1330452032], '4B':[1,1,30,3900,1460700,1220162880], '5B':[1,1,62,26164,43023908,199596500056]}
for key,seq in expected.items():
 assert reported[key][:len(seq)]==seq
 counts['published_table_entries']+=len(seq)
out={'status':'PASS','range':'k=3..10, n<=9, all available physical entries','checks':counts,'source_tables':reported}
Path(__file__).with_name('independent-output.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
