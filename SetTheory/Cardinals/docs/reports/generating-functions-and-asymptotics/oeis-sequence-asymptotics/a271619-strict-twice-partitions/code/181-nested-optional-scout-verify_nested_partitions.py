#!/usr/bin/env python3
"""Independent exact/product and asymptotic checks; local read/write only."""
import math,json,time
from pathlib import Path
import mpmath as mp
mp.mp.dps=55
HERE=Path(__file__).resolve().parent
OEIS=[1,1,2,4,8,15,28,51,92,164,289,504,871,1493,2539,4290,7201,12017,19939,32911,54044,88330,143709,232817,375640,603755,966816,1542776,2453536,3889338,6146126,9683279,15211881,23830271,37230720,58015116,90174847,139820368,216286593]
A=mp.pi**2/6

def exact_coeffs(N):
 # Integer Kronecker substitution with proven coefficient bound a_n<=2^(n-1)
 # from the composition bijection independently checked below.
 w=N+3; mask=(1<<((N+1)*w))-1; F=1; pk=[1]+[0]*N
 for k in range(1,N+1):
  for j in range(k,N+1):pk[j]+=pk[j-k]
  B=1+sum(pk[j]<<(w*(j+k)) for j in range(N-k+1))
  F=(F*B)&mask
 return [(F>>(j*w))&((1<<w)-1) for j in range(N+1)]

def direct_coeffs(N):
 p=[1]+[0]*N;F=[1]+[0]*N
 for k in range(1,N+1):
  for j in range(k,N+1):p[j]+=p[j-k]
  G=F.copy()
  for i in range(N+1):
   for j in range(N-i-k+1):G[i+j+k]+=F[i]*p[j]
  F=G
 return F

def brute_compositions(n):
 if n==0:return 1
 good=0
 for mask in range(1<<(n-1)):
  c=[];a=1
  for j in range(n-1):
   if mask>>j&1:c.append(a);a=1
   else:a+=1
  c.append(a);leaders=[c[0]]
  for j in range(1,len(c)):
   if c[j]>c[j-1]:leaders.append(c[j])
  good+=all(a<b for a,b in zip(leaders,leaders[1:]))
 return good

def bernoulli_polys(M):
 polys=[[0],[0,1]]
 for k in range(2,M+1):
  p=polys[-1];q=[0]*(len(p)+1)
  for j in range(1,len(p)):q[j]+=j*p[j];q[j+1]-=j*p[j]
  polys.append(q)
 return polys
BP=bernoulli_polys(8)

def eulerian(n):
 a=[1]
 for j in range(1,n+1):
  b=[0]*(j+1)
  for k in range(j):
   b[k]+=(k+1)*a[k]
   b[k+1]+=(j-1-k)*a[k]
  a=b
 return a
EP=[None]+[eulerian(j-1) for j in range(1,9)]

def cumulants(t,M=6):
 # c_j of jGeom via Eulerian polynomial; Bell composition with Bernoulli occupancy.
 q=mp.exp(-t); N=int(A/t**2+160/t); prodlog=mp.mpf(0); L=mp.mpf(0)
 ys=[mp.mpf(0)]*(M+1);K=[mp.mpf(0)]*(M+1)
 for k in range(1,N+1):
  v=q**k; den=1-v;prodlog-=mp.log(den)
  for m in range(1,M+1):
   ys[m]+=k**m*v*mp.polyval(list(reversed(EP[m])),v)/den**m
  h=prodlog-k*t;p=mp.sigmoid(h);L+=max(h,0)+mp.log1p(mp.exp(-abs(h)))
  c=ys.copy();c[1]+=k
  B=[[mp.mpf(0)]*(M+1) for _ in range(M+1)];B[0][0]=1
  betas=[0]+[mp.polyval(list(reversed(BP[r])),p) for r in range(1,M+1)]
  for m in range(1,M+1):
   for r in range(1,m+1):
    B[m][r]=sum(math.comb(m-1,j-1)*c[j]*B[m-j][r-1] for j in range(1,m-r+2))
   K[m]+=sum(betas[r]*B[m][r] for r in range(1,m+1))
 return L,K

def saddle(n):
 t=(3*A*A/(2*n))**mp.mpf('.25')
 for i in range(20):
  L,K=cumulants(t,2);new=t+(K[1]-n)/K[2]
  if new<=0:new=t/2
  if abs(new-t)<mp.mpf('1e-40'):return new
  t=new
 return t

def edgeworth(K):
 b=K[2]
 first=K[4]/(8*b*b)-5*K[3]**2/(24*b**3)
 second=-K[6]/(48*b**3)+35*K[4]**2/(384*b**4)+7*K[3]*K[5]/(48*b**4)-35*K[3]**2*K[4]/(64*b**5)+385*K[3]**4/(1152*b**6)
 return first,second

def reduced_L(t,J=2):
 ell=A/t+mp.log(t/(2*mp.pi))/2-t/24
 logM=mp.zeta(3)/t**2+mp.log(t)/12+mp.diff(mp.zeta,-1)
 for m in range(1,J//2+1):logM+=mp.zeta(1-2*m)*mp.zeta(-1-2*m)*t**(2*m)/mp.factorial(2*m)
 hs=[0,1,2,7,mp.mpf(68)/3,mp.mpf(391)/4,mp.mpf(40043)/90,mp.mpf(96787)/40,mp.mpf(17366357)/1260]
 return ell**2/(2*t)+A/t+ell/2+t/12-logM+sum(hs[k]*t**k for k in range(1,min(J,len(hs)-1)+1))

def main():
 st=time.time();N=600;seq=exact_coeffs(N)
 assert seq[:len(OEIS)]==OEIS
 assert seq[:61]==direct_coeffs(60)
 assert seq[:16]==[brute_compositions(n) for n in range(16)]
 results={'exact_checks':{'oeis_terms':len(OEIS),'direct_convolution_terms':61,'composition_enumeration_terms':16},'free_energy':[],'coefficients':[]}
 for tt in ['.1','.07','.05','.03']:
  t=mp.mpf(tt);L,K=cumulants(t,2)
  results['free_energy'].append({'t':tt,'L':str(L),'residual_after_t2_over_t3':str((L-reduced_L(t,2))/t**3),'residual_after_t6_over_t7':str((L-reduced_L(t,6))/t**7)})
 for n in [100,200,400,600]:
  t=saddle(n);L,K=cumulants(t,6);e1,e2=edgeworth(K)
  logapprox=n*t+L-mp.log(2*mp.pi*K[2])/2
  ratio=mp.exp(mp.log(seq[n])-logapprox)
  results['coefficients'].append({'n':n,'exact':str(seq[n]),'t':str(t),'gaussian_ratio':str(ratio),'first_correction':str(e1),'second_correction':str(e2),'error_after_first':str(ratio-1-e1),'error_after_second':str(ratio-1-e1-e2)})
 results['seconds']=time.time()-st
 (HERE/'verification.json').write_text(json.dumps(results,indent=2)+'\n')
 (HERE/'exact_terms_0_600.txt').write_text('\n'.join(f'{n} {v}' for n,v in enumerate(seq))+'\n')
 print(json.dumps(results,indent=2))
if __name__=='__main__':main()
