#!/usr/bin/env python3
"""Fail-closed finite m=R screen; small compact-type ports, not compact44."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent;root=here.parents[1]
graph=root/'research/p64-qcube72-free-main-candidate/graph.json'
if hashlib.sha256(graph.read_bytes()).hexdigest()!='875a9d0972c350e6858e25b68f2dc794b1f330e61f29cd52a5853ece90b24806':raise RuntimeError('graph hash')
# Deterministic Miller-Rabin bases for n<2^64.
def prime(n):
 if n<2:return False
 for p in (2,3,5,7,11,13,17,19,23,29,31,37):
  if n%p==0:return n==p
 if n>=2**64:raise RuntimeError('primality bound exceeded')
 d=n-1;r=0
 while d%2==0:d//=2;r+=1
 for a in (2,325,9375,28178,450775,9780504,1795265022):
  if a%n==0:continue
  x=pow(a,d,n)
  if x in (1,n-1):continue
  for _ in range(r-1):
   x=x*x%n
   if x==n-1:break
  else:return False
 return True
def factor(n):
 out=subprocess.run(['/usr/bin/factor',str(n)],check=True,capture_output=True,text=True,timeout=3).stdout
 labels=out.split(':')
 if len(labels)!=2 or int(labels[0])!=n:raise RuntimeError('factor output')
 ps=list(map(int,labels[1].split()));prod=1;d={}
 for p in ps:
  if not prime(p):raise RuntimeError('factor not prime')
  prod*=p;d[p]=d.get(p,0)+1
 if prod!=n:raise RuntimeError('factor product')
 return d
def pairpow(x,y,d,e):
 a,b=1,0
 while e:
  if e&1:a,b=a*x+d*b*y,a*y+b*x
  e//=2
  if e:x,y=x*x+d*y*y,2*x*y
 return a,b
checked=0;positive_scale=0;found=[]
for R in (43,47):
 for s in range(1,31):
  Y=27*s;U=Y*Y;C0=4*Y+3;Q=4*Y*(2**R+1)+3
  fq=factor(Q);fu=factor(U);factors=fq.copy()
  for p,e in fu.items():factors[p]=factors.get(p,0)+e
  divs=[1]
  for p,e in factors.items():divs=[d*p**k for d in divs for k in range(e+1)]
  for H in divs:
   if H<=C0 or (H-C0)%(12*Y):continue
   X=(H-C0)//(4*Y);w=X//3
   if w<=0 or X!=3*w:continue
   a=(X+1)*Y;n=a+2;D=n*n-1;P=X*U
   g,c=pairpow(n,1,D,R)
   if U*(g-X-a*c)%H:raise RuntimeError('projection identity failed')
   h=U*(g-X-a*c)//H
   if h<=0:raise RuntimeError('nonpositive h')
   checked+=1
   for j in range(1,R+1):
    t,k=pairpow(2*P+1,2,P*(P+1),j)
    if Y*k>=c:break
    if c<(Y+1)*k:
     positive_scale+=1
     found.append({'R':R,'s':s,'w':w,'j':j,'carrier_mod_3':(h+k-R-1)%3})
print(json.dumps({'status':'PASS_EXHAUSTIVE_BOUNDED_SCREEN','R':[43,47],'s_min':1,'s_max':30,'q':3,'beta':2,'J':1,'F':1,'alpha':1,'K0_choices':[0,1],'first_index_max':'R','projection_candidate_count':checked,'first_main_scale_candidate_count':positive_scale,'candidates':found,'scope':'Finite search over stated m=R parameters only; factorization verified; no compact44 or general absence claim.'},sort_keys=True))
