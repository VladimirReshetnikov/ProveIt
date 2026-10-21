#!/usr/bin/env python3
"""Independent exact source audit; no third-party imports or network."""
from pathlib import Path
import hashlib,json,math,sys
if not __debug__ or sys.flags.optimize:
 raise RuntimeError("Run with assertions enabled, without -O or -OO.")
R=Path(__file__).resolve().parent
raw=(R/'inputs/source.sites.json').read_bytes();sites=json.loads(raw)
assert hashlib.sha256(raw).hexdigest()=='2407f815551b4aba335c9bf041e15e8ce3cfb9ad830d89539f3bcf123462371a'
assert len(sites)==4733
leaf={p:i for i,(p,op,a)in enumerate(sites)};depth=max(map(len,leaf));interval={}
def index(p=''):
 if p in leaf:ans=(leaf[p],leaf[p]+1)
 else:
  a,b=index(p+'0'),index(p+'1');assert a[1]==b[0];ans=(a[0],b[1])
 interval[p]=ans;return ans
assert index()==(0,len(sites))
def locate(p):
 z=p+'0'*depth
 for k in range(1,depth+1):
  if z[:k]in leaf:
   assert '1'not in p[k:]
   return leaf[z[:k]]
 raise AssertionError('Invalid target')
def advance(p):return format((int(p,2)+1)%(1<<len(p)),'0'+str(len(p))+'b')if p else ''
def graph_arithmetic():
 g=[]
 for i,(p,op,a)in enumerate(sites):
  edge='1'if op=='CC'else'0';k=a if op in ('CC','CB')else 1
  positions=[j for j,b in enumerate(p)if b==edge];prefix=p[:positions[-k]]if len(positions)>=k else''
  q=locate(prefix if op=='CC'else advance(prefix))
  g.append([]if op=='CH'else[q]if op in('CC','CB')else[q,(i+1)%len(sites)]if op=='CD'else[(i+1)%len(sites)])
 return g
def graph_intervals():
 g=[]
 for i,(p,op,a)in enumerate(sites):
  edge='1'if op=='CC'else'0';left=a if op in('CC','CB')else 1;q=0
  while p:
   bit,p=p[-1],p[:-1]
   if bit==edge:
    left-=1
    if left==0:q=interval[p][0]if edge=='1'else interval[p][1]%len(sites);break
  g.append([]if op=='CH'else[q]if op in('CC','CB')else[q,(i+1)%len(sites)]if op=='CD'else[(i+1)%len(sites)])
 return g
g=graph_arithmetic();assert g==graph_intervals()
assert sites[4697]==['100111','CC',3]and g[4697]==[23]
assert sites[23]==['1000','CD',3]and g[23][0]==4698
assert sites[4718][1:]==['CH',None]
def run(t,n=7,w=99,d=13,l=0):
 r=[n,t,w,0,d,0,0,0,l];pc=4696;trace=[]
 for tick in range(2*t+16):
  p,op,a=sites[pc];trace.append([pc,sites[pc],r.copy()])
  if op=='CH':
   assert pc==4718 and tick==2*t+15
   return trace
  if op=='CI':r[a]+=1;pc=g[pc][0]
  elif op=='CD':b=int(r[a]>0);r[a]-=b;pc=g[pc][b]
  else:pc=g[pc][0]
 raise AssertionError('Missing halt')
assert run(42)==json.loads((R/'evidence/local_halt.json').read_text())['trace']
for t in range(101):run(t)
# Exact adjacent-pair lemma for the intended, but NOT literal, biased scheduler.
P=lambda a,b:(a+b)*(a+b+1)//2+b
def U(n):
 s=(math.isqrt(8*n+1)-1)//2;b=n-s*(s+1)//2;return s-b,b
def first(n):
 a,z=U(n)
 if a==0:return ('S',),z-1 if z else None
 y,z=U(z)
 if a==1:return ('MP',y),z if z else None
 x,z=U(z);return ('AX',a-2,x,y),z if z else None
for r in range(1,101):
 for v in range(1,31):
  u=P(1,r);y=P(v,u);n=P(2,y)
  assert n+1==P(1,y+1)and y+1==P(v-1,u+1)and u+1==P(0,r+1)
  assert first(n)==(('AX',0,1,v),r)
  assert first(n+1)==(('MP',v-1),u+1)
  assert first(u+1)==(('S',),r)
print(json.dumps({'status':'REJECTED_SOURCE_CONFIRMED','independent_CFG_agreement':len(g),'return_target':23,'not_scheduler_target':0,'local_sample_steps_to_CH':99,'finite_local_samples':101,'adjacent_shell_samples':3000,'scope':'Exact literal rejection and finite corroboration of separately proved intended-scheduler lemma. No whole-blank binary step count claimed.'},indent=2))
