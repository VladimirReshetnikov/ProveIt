import math,json
import mpmath as mp
mp.mp.dps=60

def vals(k,N):
 h=[0]*(N+1)
 for n in range(1,N+1):
  h[n]=n**(k*n)-sum(math.comb(n-1,i-1)*n**(k*(n-i))*h[i] for i in range(1,n))
 a=[0]+[h[n]//math.factorial(n-1) for n in range(1,N+1)]
 T=[0]*(N+1);s=[1]+[0]*N
 for m in range(1,k*N+2):
  s=[0]+[j*s[j]+s[j-1] for j in range(1,N+1)]
  if m%k==1 and 0<(m-1)//k<=N:T[(m-1)//k]=s[(m-1)//k]
 return a,T
out={}
for k in [2,3,4]:
 N=200;a,T=vals(k,N)
 v=1+mp.lambertw(-k*mp.exp(-k))/k;r=1-v;c=1-k*r
 c1=k*r*v/(2*c)
 rows=[]
 for n in [10,20,50,100,200]:
  b=mp.mpf(a[n])/T[n]
  rows.append(dict(n=n,ratio=str(b),scaled_c1=str((b-c)*n),scaled_c2=str((b-c-c1/n)*n*n)))
 out[k]=dict(v=str(v),c=str(c),c1=str(c1),rows=rows)
 print(k,'c=',mp.nstr(c,20),'c1=',mp.nstr(c1,20))
 for x in rows:print(x)
open(__import__('pathlib').Path(__file__).resolve().parent.parent / 'data' / 'numerics.json','w').write(json.dumps(out,indent=2))
