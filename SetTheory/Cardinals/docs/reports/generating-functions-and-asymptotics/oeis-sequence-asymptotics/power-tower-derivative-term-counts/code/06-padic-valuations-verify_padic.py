"""Independent exact integer-triangle checks for the valuation families."""
from pathlib import Path
import json

def vp(n,p):
 if not n:raise RuntimeError('valuation of zero')
 n=abs(n);v=0
 while n%p==0:n//=p;v+=1
 return v

def vfact(n,p):
 z=0
 while n:n//=p;z+=n
 return z
primes=[2,3,5,7,11,13,17,19,23,29,31]
MAX=360
prevprev=[1];prev=[0,1]
counts=[0,0];examples=[]
for M in range(2,MAX+1):
 row=[0]*(M+1)
 for Y in range(1,M+1):
  v=(Y-M+1)*(prev[Y] if Y<len(prev) else 0)+prev[Y-1]
  if Y-1<len(prevprev):v+=(M-1)*prevprev[Y-1]
  row[Y]=v
  r=M-Y
  if r==0:continue
  for p in primes:
   e=vp(Y,p)
   if r%(p-1)==0:
    m=r//(p-1)
    if m<=p**e:
     expected=e-vp(m,p)-m+vfact(M,p)-vfact(Y,p)
     if v==0 or vp(v,p)!=expected:raise RuntimeError(('principal',M,Y,p,expected,v))
     counts[0]+=1
     if (r,Y,p) in [(17,32,2),(20,27,3)]:examples.append({'r':r,'Y':Y,'p':p,'b_valuation':expected,'b':str(v)})
   if p>2 and r>1 and (r-1)%(p-1)==0:
    m=(r-1)//(p-1)
    if m>=1 and m<p**e and r%p:
     expected=e-m+vfact(M,p)-vfact(Y,p)
     if v==0 or vp(v,p)!=expected:raise RuntimeError(('shifted',M,Y,p,expected,v))
     counts[1]+=1
     if (r,Y,p) in [(17,9,3),(21,25,5)]:examples.append({'r':r,'Y':Y,'p':p,'b_valuation':expected,'b':str(v)})
 prevprev,prev=prev,row
out={'maximum_row':MAX,'primes':primes,'principal_checks':counts[0],'shifted_checks':counts[1],'examples':examples,'all_pass':True}
Path(__file__).with_name('padic_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
