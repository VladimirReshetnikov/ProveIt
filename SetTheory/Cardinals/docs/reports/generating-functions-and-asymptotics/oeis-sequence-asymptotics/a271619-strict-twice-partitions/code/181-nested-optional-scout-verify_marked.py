#!/usr/bin/env python3
import math,json,time
from pathlib import Path
import verify_nested_partitions as v
mp=v.mp;HERE=Path(__file__).resolve().parent

def exact_moments(N):
 w=N+2*math.ceil(math.log2(N+1))+6
 mask=(1<<((N+1)*w))-1
 f=1;g=0;h=0;pk=[1]+[0]*N
 for k in range(1,N+1):
  for j in range(k,N+1):pk[j]+=pk[j-k]
  B=sum(pk[j]<<(w*(j+k)) for j in range(N-k+1))
  h=(h*(1+B)+2*g*B)&mask
  g=(g*(1+B)+f*B)&mask
  f=(f*(1+B))&mask
 get=lambda P,n:(P>>(n*w))&((1<<w)-1)
 return [(get(f,n),get(g,n),get(h,n)) for n in range(N+1)]

def bmoments(t):
 N=int(v.A/t**2+160/t);pLog=mp.mpf(0);ys=mp.mpf(0)
 mean=mp.mpf(0);var=mp.mpf(0);cov=mp.mpf(0)
 for k in range(1,N+1):
  q=mp.exp(-t*k);pLog-=mp.log1p(-q);ys+=k*q/(1-q)
  p=mp.sigmoid(pLog-k*t)
  mean+=p;var+=p*(1-p);cov+=p*(1-p)*(k+ys)
 return mean,var,cov

R=[];D=exact_moments(600)
for n in [100,200,400,600]:
 t=v.saddle(n);L,K=v.cumulants(t,2);mb,vb,cov=bmoments(t)
 a,b,c=D[n];me=mp.mpf(b)/a;va=mp.mpf(c)/a+me-me**2
 R.append({'n':n,'mean':str(me),'Boltzmann_mean':str(mb),'mean_difference_over_t':str((me-mb)/t),'variance':str(va),'Schur_variance':str(vb-cov**2/K[2]),'3t_variance':str(3*t*va),'count_over_sqrt_n':str(me/mp.sqrt(n))})
(HERE/'marked_verification.json').write_text(json.dumps(R,indent=2)+'\n');print(json.dumps(R,indent=2))
