from pathlib import Path
import json
N=400;out={}
for b in [2,3,4,8,16]:
 # Independent construction 1: finite coloured distinct-part product.
 a=[0]*(N+1);a[0]=1;power=1
 while power<=N:
  for k in range(power,N+1,power):
   for n in range(N,k-1,-1):a[n]+=a[n-k]
  power*=b
 # Independent construction 2: logarithmic derivative recurrence.
 c=[0]*(N+1)
 for k in range(1,N+1):
  multiplicity=1;temp=k
  while temp%b==0:multiplicity+=1;temp//=b
  for j in range(1,N//k+1):c[k*j]+=multiplicity*k*(1 if j%2 else -1)
 a2=[0]*(N+1);a2[0]=1
 for n in range(1,N+1):
  total=sum(c[k]*a2[n-k] for k in range(1,n+1));assert total%n==0;a2[n]=total//n
 assert a==a2
 # Independent construction 3, when applicable: allowed 2-adic valuation parts.
 if b&(b-1)==0:
  m=b.bit_length()-1;u=[0]*(N+1);u[0]=1
  for k in range(1,N+1):
   if ((k&-k).bit_length()-1)%m==0:
    for n in range(k,N+1):u[n]+=u[n-k]
  assert a==u
 out[str(b)]={'through':N,'all_equal':True,'first_32':a[:32],'at_400':str(a[N])}
Path(__file__).with_name('exact-checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
