#!/usr/bin/env python3
"""Independent integer counts and arbitrary-precision positive-sum diagnostics.
Tail bounds are analytic geometric bounds evaluated at working precision;
these diagnostics are not outward-rounded total numerical-error certificates.
"""
from functools import lru_cache
from math import factorial
import json, mpmath as mp
mp.mp.dps=80
@lru_cache(None)
def graph(r,u=-1):
 if not any(r): return 1
 i=next(i for i,x in enumerate(r) if x)
 rr=list(r); rr[i]-=1
 ans=graph(tuple(rr),i) if u in (-1,i) else 0
 for k,nk in enumerate(rr):
  if k==i or not nk: continue
  tt=rr.copy(); tt[k]-=1
  ans+=nk*graph(tuple(tt),u)
 return ans

def branch_int(parts,i):
 ans=0
 P=factorial(parts[0])*factorial(parts[1])*factorial(parts[2])
 for k in range(parts[i]+1):
  rem=list(parts);rem[i]-=k
  nums=[rem[0]+rem[1]-rem[2],rem[0]+rem[2]-rem[1],rem[1]+rem[2]-rem[0]]
  if any(x<0 or x%2 for x in nums):continue
  den=factorial(k)
  for x in nums:den*=factorial(x//2)
  ans+=P//den
 return ans

def exact(parts):
 branches=[branch_int(parts,i) for i in range(3)]
 nums=[parts[0]+parts[1]-parts[2],parts[0]+parts[2]-parts[1],parts[1]+parts[2]-parts[0]]
 perfect=0
 if all(x>=0 and x%2==0 for x in nums):
  perfect=factorial(parts[0])*factorial(parts[1])*factorial(parts[2])
  for x in nums:perfect//=factorial(x//2)
 return sum(branches)-2*perfect, branches, perfect

def ratio(n,d,j):
 return mp.mpf(n-j)**2/((d+2*j+2)*(d+2*j+1)*(j+1))

def window(n,d):
 lo=max(0,(-d+1)//2)
 left,right=lo,n
 while left<right:
  mid=(left+right)//2
  if ratio(n,d,mid)>=1:left=mid+1
  else:right=mid
 mode=left
 total=mp.mpf(1); mom1=mp.mpf(0);mom2=mp.mpf(0);tails=[]
 # moments centered at integer mode reduce cancellation
 for sign in [-1,1]:
  j=mode;t=mp.mpf(1)
  while (j>lo if sign<0 else j<n):
   rr=1/ratio(n,d,j-1) if sign<0 else ratio(n,d,j)
   t*=rr;j+=sign
   h=j-mode
   total+=t;mom1+=t*h;mom2+=t*h*h
   if t<mp.mpf('1e-70'):
    rnext=1/ratio(n,d,j-1) if sign<0 and j>lo else ratio(n,d,j) if sign>0 and j<n else mp.mpf(0)
    if rnext<1:
     tails.append(t*rnext/(1-rnext));break
  else:tails.append(mp.mpf(0))
 logt=2*(mp.loggamma(n+1)-mp.loggamma(n-mode+1))-mp.loggamma(d+2*mode+1)-mp.loggamma(mode+1)
 logZ=logt+mp.log(total)
 mean=mode+mom1/total
 var=mom2/total-(mom1/total)**2
 N=mp.root(n,3);delta=d/N**2
 # monotone equation delta=u-2/u² has unique positive root
 u=mp.findroot(lambda u:u-2/u**2-delta,(mp.mpf('.05'),max(mp.mpf(2),delta+1)),solver='bisect') if False else None
 low=mp.mpf('1e-10');high=abs(delta)+3
 for _ in range(350):
  mid=(low+high)/2
  if mid-2/mid**2<delta:low=mid
  else:high=mid
 u=(low+high)/2;s=1/u**2;chi=4/u+1/s;b=-2*s/chi
 C=-s**3/3+2*s**2/chi;Phi=u+s-delta*mp.log(u)
 logmain=-2*d*mp.log(N)+N**2*Phi-s**2*N+C-mp.log(N)-mp.log(2*mp.pi*u*s*chi)/2
 c1=(60*u**12+315*u**9+372*u**6+80*u**3-64)/(6*u**8*(u**3+4)**3)
 ell2=-(5*u**24-340*u**21-900*u**18+6056*u**15+17240*u**12-4800*u**9-30720*u**6-7680*u**3+6144)/(60*u**10*(u**3+4)**5)
 m0=-(3*u**6+7*u**3-8)/(u**3+4)**3
 v1=-4*(u**6+2*u**3+4)/(u*(u**3+4)**3)
 ret=dict(n=n,d=d,N=mp.nstr(N,16),delta=mp.nstr(delta,20),mode=mode,
  c1=mp.nstr(c1,20),scaled_log_residual=mp.nstr(N*(logZ-logmain),20),
  ell2=mp.nstr(ell2,20),scaled_second_log_residual=mp.nstr(N**2*(logZ-logmain-c1/N),20),
  mean_constant_target=mp.nstr(m0,20),mean_constant_residual=mp.nstr(mean-s*N**2-b*N,20),
  var_linear_target=mp.nstr(v1,20),var_linear_residual=mp.nstr((var-N**2/chi)/N,20),
  relative_sum_tail_bound=mp.nstr(sum(tails)/total,8))
 # all other branches bound in d<=0 regime using gamma reference B
 if d<=0:
  a1=-mp.mpf(d)/2;a2=n+mp.mpf(d)/2
  log_B_without_factorial=2*mp.loggamma(n+1)-mp.loggamma(a1+1)-2*mp.loggamma(a2+1)
  # |A-A_big| <=2 exp(2+sqrt(a1))B, overcounts perfect harmlessly
  ret['log_other_branch_upper_relative']=mp.nstr(mp.log(2)+2+mp.sqrt(a1)+log_B_without_factorial-logZ,20)
 return ret

def run():
 import argparse
 from pathlib import Path
 _ap=argparse.ArgumentParser(description='Optional arbitrary-precision diagnostics; not interval certificates')
 _ap.add_argument('--output-dir',required=True,type=Path,help='new output directory')
 _output=_ap.parse_args().output_dir
 _output.mkdir(exist_ok=False)

 ints=[]
 for n in range(0,11):
  for d in range(-n,n+3):
   parts=(2*n+d,n,n)
   if min(parts)<0:continue
   q,br,p=exact(parts);g=graph(parts)
   if q!=g:raise RuntimeError((n,d,q,g))
   # independent direct large-branch formula
   big=sum(factorial(2*n+d)*factorial(n)**2//(factorial(n-j)**2*factorial(d+2*j)*factorial(j)) for j in range(max(0,(-d+1)//2),n+1))
   if big!=br[0]:raise RuntimeError((n,d,big,br))
   ints.append(dict(n=n,d=d,total=str(q),branches=list(map(str,br)),perfect=str(p)))
 print('Independent graph recursion matches',len(ints),'integer (n,d) cases')
 out=[]
 for N in [10,20,40,80,160]:
  n=N**3
  for delta in [-3,-1,0,1,3]:
   # +1 tests actual odd d and non-limiting exact delta; d=0 retained separately
   d=delta*N*N+(1 if delta!=0 else 0)
   r=window(n,d);out.append(r)
   print(N,d,'c1target',r['c1'],'resid',r['scaled_log_residual'],'ell2target',r['ell2'],'resid',r['scaled_second_log_residual'])
 # Endpoint/parity tests d=-1 and -2 have half-integral vs integral gamma references
 for n,d in [(10**3,-1),(10**3,-2),(10**6,-1),(10**6,-2),(10**6,1)]:out.append(window(n,d))
 from pathlib import Path
 here=_output
 (here/'integer_checks.json').write_text(json.dumps(ints,indent=2)+'\n')
 (here/'diagnostics.json').write_text(json.dumps(out,indent=2)+'\n')
if __name__=='__main__':run()
