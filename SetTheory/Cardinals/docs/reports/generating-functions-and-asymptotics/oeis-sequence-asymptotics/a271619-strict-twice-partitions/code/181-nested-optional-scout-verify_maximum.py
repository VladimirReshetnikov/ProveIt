#!/usr/bin/env python3
import math,json
from pathlib import Path
import verify_nested_partitions as v
mp=v.mp;N=600;ns=[100,200,400,600];w=N+3;mask=(1<<((N+1)*w))-1;F=1;pk=[1]+[0]*N
sizes={};ts={};mus={};targets={}
for n in ns:
 t=v.saddle(n);mu=v.A/t+mp.log(t/(2*mp.pi))/2-t/24
 ts[n]=t;mus[n]=mu
 for x in [-1,0,1]:
  m=int(mp.floor((mu+mp.log(1/t)+x)/t));targets[n,x]=m
for k in range(1,N+1):
 for j in range(k,N+1):pk[j]+=pk[j-k]
 B=1+sum(pk[j]<<(w*(j+k)) for j in range(N-k+1));F=F*B&mask
 for (n,x),m in targets.items():
  if m==k:sizes[n,x]=(F>>(n*w))&((1<<w)-1)
a={n:(F>>(n*w))&((1<<w)-1) for n in ns}
R=[]
for (n,x),m in targets.items():
 t=ts[n];mu=mus[n];actual=mp.mpf(sizes[n,x])/a[n]
 lp=mp.mpf(0); logs=[]
 for k in range(1,int(v.A/t**2+160/t)):
  lp-=mp.log1p(-mp.exp(-t*k))
  if k>m:logs.append(mp.log1p(mp.exp(lp-t*k)))
 bol=mp.exp(-mp.fsum(logs))
 R.append({'n':n,'x':x,'cutoff':m,'normalized_cutoff':str(t*m-mu-mp.log(1/t)),'exact_CDF':str(actual),'Boltzmann_CDF':str(bol),'Gumbel_at_x':str(mp.exp(-mp.exp(-x)))})
Path(__file__).with_name('maximum_verification.json').write_text(json.dumps(R,indent=2)+'\n');print(json.dumps(R,indent=2))
