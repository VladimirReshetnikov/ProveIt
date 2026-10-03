"""Independent rational checks of A213863's exact transformed recurrence."""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json
A=[[1]]
for n in range(1,41):
 row=[(2*n-1)*A[-1][0]]
 for k in range(1,n+1):row.append(row[-1]+(2*n+k-1)*(A[-1][k] if k<n else 0))
 A.append(row)
def d(N,j):
 if j<0 or j>N or (N+j)%2:return F(0)
 n,k=(N+j)//2,(N-j)//2
 return F(A[n][k],3**n*factorial(n))
def gs(N,j):
 v=F(1)
 for k in range(1,j+1):v*=F(3*N+k-2,3*(N+k))
 return v
rec=0;rat=0
for N in range(1,41):
 for j in range(N%2,N+1,2):
  assert d(N,j)==d(N-1,j+1)+F(3*N+j-2,3*(N+j))*d(N-1,j-1)
  rec+=1
 if N>=2:
  for j in range(N+2):
   q=F(N+j,N)
   for r in range(2,5):q*=F(3*N-r,3*N+j-r)
   assert gs(N-1,j)/gs(N,j)==q and 0<q<=1
   rat+=1
report={'recurrence_checks':rec,'gauge_contraction_checks_including_artificial_endpoints':rat,'first_ten_diagonal':[r[-1] for r in A[:10]],'initial_v1_squared':'1/3','frozen_first_eigenvalue_squared':'2/3','status':'All exact rational assertions passed; not a substitute for the analytic proof.'}
Path(__file__).with_name('exact-cocycle-checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
