from math import comb
from pathlib import Path
import json,mpmath as m
m.mp.dps=80

def diagonal_counts(steps,M):
 L=M+1;size=L**3;prev=[0]*size;out=[]
 for i in range(L):
  now=[0]*size
  for j in range(L):
   for k in range(L):
    for l in range(L):
     ix=(j*L+k)*L+l
     if i==j==k==l==0:now[ix]=1;continue
     if sum(s*c for s,c in zip(steps,(i,j,k,l)))<0:continue
     now[ix]=(prev[ix] if i else 0)+(now[ix-L*L] if j else 0)+(now[ix-L] if k else 0)+(now[ix-1] if l else 0)
  out.append(now[(i*L+i)*L+i]);prev=now
 return out

M=30
four=diagonal_counts((-3,-1,1,3),M)
five=[comb(5*n,n)*x for n,x in enumerate(diagonal_counts((-2,-1,1,2),M))]
phi=(1+m.sqrt(5))/2;r=phi-m.sqrt(phi)
params={4:(r/(m.sqrt(2)*m.pi**m.mpf('1.5')),m.mpf('2.5'),-37*r**3/200+11*r*r/40+13*r/40-m.mpf(259)/400),5:((3*m.sqrt(5)-5)/(8*m.pi**2),m.mpf(3),13*(m.sqrt(5)-5)/50)}
reports=[]
for q,data in [(4,four),(5,five)]:
 C,beta,c1=params[q];diagnostics=[]
 for n in [5,10,15,20,25,30]:
  ratio=m.mpf(data[n])/(C*m.mpf(q)**(q*n)/m.mpf(n)**beta)
  diagnostics.append({'n':n,'a':str(data[n]),'ratio_to_leading':str(ratio),'n_times_leading_relative_error':str(n*(ratio-1)),'n_squared_first_correction_residual':str(n*n*(ratio-1-c1/n))})
 reports.append({'q':q,'method':'forward nonnegative-height dynamic programming in a three-dimensional rolling count array; q=5 independently deletes and reinserts n zero steps','max_n':M,'c1':str(c1),'diagnostics':diagnostics,'all_diagonal_terms':[str(x) for x in data]})
out={'status':'exact coefficients, numerical asymptotic diagnostics only','reports':reports}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
for R in reports:
 print('q',R['q'],'c1',R['c1'])
 for z in R['diagnostics']:print(z['n'],z['n_times_leading_relative_error'][:25],z['n_squared_first_correction_residual'][:25])
