#!/usr/bin/env python3
import hashlib,gzip,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
root=Path(__file__).resolve().parents[2];pkg=root/'research/current14-carrier64-scalar-repair';gpath=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(gpath)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e' and sha(pkg/'check.py')=='6c913b084503101f5a806c2f995a48b6a32cb1874df372aec6c7c0547d00eb71'
g=json.loads(gpath.read_text());ports={}
for name,m in g['coefficient_binding']['ports'].items():
 raw=(gpath.parent/'coefficients'/m['file']).read_bytes();assert hashlib.sha256(raw).hexdigest()==m['gzip_sha256'];raw=gzip.decompress(raw);assert hashlib.sha256(raw).hexdigest()==m['raw_sha256'] and len(raw)==m['raw_bytes'];ports[name]=int.from_bytes(raw,'big')
cases=good=bad=0
for q in range(2,13):
 b=q-1
 for M in range(1,21):
  for F in range(1,16):
   for C in range(1,16):
    numerator=M*C-F
    if numerator<0 or numerator%b:continue
    z=1+numerator//b;assert M*C+q-F-z*b==1;G=q*(q-F)-C;u,r=divmod(G,b)
    predicted=[]
    if 2<=u<=b and 1<=r<u:
     t=M*(u-r)-(q-u)
     if t>=0 and t%b==0:predicted=[(q-u,r,u-r,1+t//b)]
    actual=[]
    for u0 in range(2,b+1):
     for alpha in range(1,u0):
      if b*u0+alpha!=G:continue
      F0=q-u0;C0=u0-alpha;t=M*C0-F0
      if t>=0 and t%b==0:actual.append((F0,alpha,C0,1+t//b))
    assert actual==predicted
    cases+=1;good+=bool(actual);bad+=not bool(actual)
assert (cases,good,bad)==(12695,661,12034)
# Alternate repair q=4,M=2,F=1,C=5,z=4; old (2,1,1,1).
q,M,F,C,z=4,2,1,5,4;assert M*C+q-F-z*(q-1)==1 and q-F-C==-2 and q*(q-F)-C==(q-1)*(q-2)+1 and M*1+q-2-1*(q-1)==1
beta,K=ports['beta'],ports['K0'];q=beta+1;b=q-1;assert beta%2==1 and beta>=31;M=K+q//2+(q-2)*K;F=1;C=q+1;z=1+(q+2)//2+K*(q+1);assert M*C+q-F-z*b==1;G=q*(q-F)-C;u,r=divmod(G,b);assert (u,r)==(q-2,q-3) and (M*(u-r)-(q-u))%b!=0
MC,MF=ports['MC'],ports['MF'];C2=2*q-1;w2=1+(q-2)*K;M2=K+w2;z2=3+K*(2*q-1);G2=q*(q-1)-C2;R2=G2*(q*q-1)+MC+q*MF;E2=w2*q**4;u2,r2=divmod(G2,b);assert M2*C2+q-1-z2*b==1 and q-1-C2==-q and (u2,r2)==(q-3,q-2) and r2>=u2 and R2%2==1 and 1<R2<q**4-q**3<E2
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier64-transport-proposal-independent/check.py')],capture_output=True,check=True,timeout=180)
# Independent exact verification of unit norm preservation in Z[p,x,y].
def plus(a,b,k=1):
 d=a.copy()
 for key,val in b.items():d[key]=d.get(key,0)+k*val
 return {key:val for key,val in d.items() if val}
def times(a,b):
 d={}
 for x,c in a.items():
  for y,e in b.items():
   key=tuple(i+j for i,j in zip(x,y));d[key]=d.get(key,0)+c*e
 return {key:val for key,val in d.items() if val}
one={(0,0,0):1}; pp={(1,0,0):1};xx={(0,1,0):1};yy={(0,0,1):1};disc=plus(times(pp,pp),one,-1);xxp=plus(times(pp,xx),times(disc,yy));yyp=plus(xx,times(pp,yy));assert plus(times(xxp,xxp),times(disc,times(yyp,yyp)),-1)==plus(times(xx,xx),times(disc,times(yy,yy)),-1)
# Small independent finite sanity check for the stated positive Pell enumeration.
import math
for pval in range(2,21):
 disc=pval*pval-1;found=[]
 for yval in range(1,1001):
  v=math.isqrt(1+disc*yval*yval)
  if v*v==1+disc*yval*yval:found.append((v,yval))
 generated=[];xval,yval=1,0
 while True:
  xval,yval=pval*xval+disc*yval,xval+pval*yval
  if yval>1000:break
  generated.append((xval,yval))
 assert found==generated
r=json.loads((pkg/'result.json').read_text());assert r['candidate_transport_cases']==cases and r['repairable']==good and r['unrepairable']==bad
out=subprocess.run([sys.executable,'-I','-S','-B',str(pkg/'check.py')],capture_output=True,text=True,check=True,timeout=180);assert not out.stderr and json.loads(out.stdout)==r
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','scope':'exact restricted scalar repair criterion, uniqueness and bounded check; no full-zero reverse equivalence or Lean'},indent=2))
