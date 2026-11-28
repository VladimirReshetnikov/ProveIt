from itertools import combinations_with_replacement
from math import comb
from collections import defaultdict

def digits(n,p):
 s=0
 while n:s+=n%p;n//=p
 return s

def compositions(t,p):
 if p==1:
  yield (t,);return
 for a in range(t+1):
  for q in compositions(t-a,p-1):yield (a,)+q

def score(p,nu):
 t=sum(nu);d=max(c+p*(v-1) for c,v in enumerate(nu) if v)
 inds=sorted(range(d+1),key=lambda j:(digits(j,p),j))
 basis={};chosen=[]
 for j in inds:
  if digits(j,p)>p-1:break
  row=[]
  for c,v in enumerate(nu):
   row += [comb(j,k)*pow(c,j-k,p)%p if j>=k else 0 for k in range(v)]
  for a,b in basis.items():
   if row[a]:
    z=row[a];row=[(x-z*y)%p for x,y in zip(row,b)]
  if any(row):
   a=next(i for i,x in enumerate(row) if x);z=pow(row[a],-1,p);row=[x*z%p for x in row];basis[a]=row;chosen.append(j)
 return max([t-1]+chosen),chosen

if __name__=='__main__':
 import sys,json,time
 p=int(sys.argv[1]);t=int(sys.argv[2]);assert max(digits(i,p) for i in range(t))<=p
 best=-1;w=[];hist=defaultdict(int);start=time.time()
 for nu in compositions(t,p):
  if nu[0]<max(nu):continue # translate maximal to 0
  ans,chosen=score(p,nu);hist[ans]+=1
  if ans>best:best=ans;w=[(nu,chosen)]
  elif ans==best:w.append((nu,chosen))
 print(json.dumps({'p':p,'t':t,'best':best,'witnesses':w[:20],'hist':dict(hist),'seconds':time.time()-start}))
