from pathlib import Path
import json,random,math,time,sys
from functools import lru_cache
P=Path(__file__).resolve().parents[1]/'context_folds/recovered/67/research'
D=json.loads((P/'agent_state/rebracket/combined246_dag.json').read_text())
base={int(k):tuple(map(tuple,v))for k,v in D['nodes'].items()};root=D['root']
def canon(n,r):
 out={};memo={};pairid={}
 def go(e):
  if e[0]!='N':return e
  if e[1] in memo:return memo[e[1]]
  a,b=map(go,n[e[1]]);key=a,b
  if key not in pairid:
   q=len(out);out[q]=key;pairid[key]=('N',q)
  memo[e[1]]=pairid[key];return memo[e[1]]
 rr=go(('N',r));return out,rr[1]
def stats(n):
 bounds={};prefix={};choices=[]
 def b(e):return bounds[e[1]] if e[0]=='N' else (e[1]if e[0]=='B'else int(e[0]=='D'),e[1]if e[0]=='C'else 0)
 def p(e):return prefix[e[1]]if e[0]=='N'else 0
 for q,(a,c)in n.items():
  ba,ca=b(a);bc,cc=b(c);bounds[q]=max(ba-1,bc),max(ca,cc-1);prefix[q]=1+p(a)
  if a[0]=='N':
   x,y=n[a[1]]
   if b(x)==b(y)==b(c)==(0,0):choices.append((q,0))
  if c[0]=='N':
   x,y=n[c[1]]
   if b(a)==b(x)==b(y)==(0,0):choices.append((q,1))
 excess=sum(max(x-6,0)**2 for x in prefix.values())
 return len(n)+4*excess,excess,max(prefix.values()),choices
base,root=canon(base,root);beg=time.time();best=(1000,1000);records=[]
for seed in range(30):
 rng=random.Random(seed);n=base;r=root;score,ex,m,choices=stats(n)
 for i in range(10000):
  q,d=rng.choice(choices);a,c=n[q];nn=n.copy();fresh=max(n)+1
  if d==0:x,y=n[a[1]];nn[q]=(x,('N',fresh));nn[fresh]=(y,c)
  else:x,y=n[c[1]];nn[q]=(('N',fresh),y);nn[fresh]=(a,x)
  nn,rr=canon(nn,r);ns,ne,nm,nc=stats(nn)
  temp=max(.12,1.8*(1-i/10000))
  if ns<=score or rng.random()<math.exp(min(0,(score-ns)/temp)):
   n,r,score,ex,m,choices=nn,rr,ns,ne,nm,nc
  key=(ex,len(n))
  if key<best:
   best=key;rec={'seed':seed,'iteration':i,'nodes':len(n),'excess':ex,'maxzero':m};records.append(rec);print(rec,flush=True)
   if ex==0:
    path=Path(__file__).parent/f'depth6_n{len(n)}.json';path.write_text(json.dumps({'root':r,'nodes':n},indent=2)+'\n')
  if ex==0 and len(n)<=201:break
 if best[0]==0 and best[1]<=201:break
 print('seed',seed,'best',best,'seconds',time.time()-beg,flush=True)
(Path(__file__).parent/'anneal_depth_results.json').write_text(json.dumps({'records':records,'seconds':time.time()-beg},indent=2)+'\n')
