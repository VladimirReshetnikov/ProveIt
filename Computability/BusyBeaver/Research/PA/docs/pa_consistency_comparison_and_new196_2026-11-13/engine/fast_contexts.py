#!/usr/bin/env python3
"""Source-frame window collector using the PA196 affine-box interpreter.
The engine macro controls are conservatively covered by blank-window closure.
No proof assistant certification is claimed. Fixed source frames are exhaustive;
loop interiors are covered at every clipped boundary-distance case.
"""
import argparse, importlib.util, hashlib, json, re, sys, time
from pathlib import Path
from functools import lru_cache
from collections import deque

def load(path,name):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
BASE=Path(__file__).resolve().parent
RUNTIME=BASE/'inputs/native_symbolic_runtime.py'
CONJ=BASE/'inputs/Conjugacy.lean'

def program(raw):
 names={'CI':'inc','CD':'dec','CC':'continueTo','CB':'breakTo','CH':'halt'}
 sites=[(tuple(map(int,p)),names[op],r)for p,op,r in raw]
 def locate(p):
  for i,(q,_,_)in enumerate(sites):
   if q[:len(p)]==p or(p[:len(q)]==q and not any(p[len(q):])):return i
  raise ValueError(p)
 def after(p):
  for i in range(len(p)-1,-1,-1):
   if p[i]==0:return locate(p[:i]+(1,))
  return 0
 def cut(p,b,k):
  for i in range(len(p)-1,-1,-1):
   if p[i]==b:
    k-=1
    if k==0:return p[:i]
  raise ValueError((p,b,k))
 ins=[]
 for p,op,r in sites:
  if op=='inc':c=('inc',r,after(p))
  elif op=='dec':c=('dec',r,after(cut(p,0,1)),after(p))
  elif op=='continueTo':c=('jump',locate(cut(p,1,r)))
  elif op=='breakTo':c=('jump',after(cut(p,0,r)))
  else:c=('halt',)
  ins.append(c)
 return sites,ins

@lru_cache(None)
def bits(k):return tuple(tuple((v>>i)&1 for i in range(k))for v in range(1<<k))
@lru_cache(None)
def prefix(xs,k):
 if k==0:return ((),)
 if not xs:return ((0,)*k,)
 x=xs[0]
 if x[0]=='x':return bits(k)
 if x[0]=='b':return tuple((x[1],)+p for p in prefix(xs[1:],k-1))
 _,b,a,c=x
 ns=range(min(c,k),k+1)if a else(min(c,k),)
 out=set()
 for n in ns:
  if n==k:out.add((b,)*k)
  else:out.update((b,)*n+p for p in prefix(xs[1:],k-n))
 return tuple(out)

def blank(table,radius,projection):
 width=2*radius+1;mask=(1<<width)-1;seen={(0,0)};queue=deque(seen)
 while queue:
  q,x=queue.popleft();w,d,t=table[q,(x>>radius)&1];x=(x&~(1<<radius))|(w<<radius)
  if t==196:continue
  for b in(0,1):
   y=((x>>1)|(b<<(width-1)))if d else((x<<1)&mask)|b
   if(t,y)not in seen:seen.add((t,y));queue.append((t,y))
 out={q:set()for q in range(196)}
 for q,x in seen:out[q].add((x>>(radius-projection))&((1<<(2*projection+1))-1))
 return out,len(seen)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('table',type=Path);ap.add_argument('sites',type=Path);ap.add_argument('steps',type=int);ap.add_argument('output',type=Path);ap.add_argument('--radius',type=int,default=2);ap.add_argument('--labels',type=Path);ap.add_argument('--zero-only',type=int,nargs='*',default=[]);ap.add_argument('--skip-sites',type=int,nargs='*',default=[]);a=ap.parse_args()
 a.output.mkdir(parents=True,exist_ok=True);s=load(RUNTIME,'sym');L=json.loads(a.labels.read_text()) if a.labels else json.loads(re.search(r'def labels : List Nat := (\[[^\n]+\])',CONJ.read_text()).group(1));inv={q:i for i,q in enumerate(L)}
 table={}
 for line in a.table.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,n=line.split();table[int(q),int(b)]=int(w),d=='R',int(n)
 assert len(table)==392
 rows={(L[q],b):(w,d,L[t])for(q,b),(w,d,t)in table.items()}
 raw=json.loads(a.sites.read_text());ss,ii=program(raw);s.program=lambda:(ss,ii)
 cs=[c for c in s.contracts()if c[0]not in a.skip_sites and(c[0]not in a.zero_only or c[1]is None or c[1][1])];windows={q:set()for q in range(196)};radius=a.radius
 def collect(q,onl,l,r):
  if q==254:return
  left=prefix(l,radius+int(onl));right=prefix(r,radius+1-int(onl))
  win=windows[inv[q]]
  for ls in left:
   for rs in right:
    bs=ls[::-1]+rs;win.add(sum(b<<i for i,b in enumerate(bs)))
 unary=0;calls=0
 def observe(conf):
  nonlocal unary,calls
  q,onl,l,r=conf
  if q==254:return
  collect(q,onl,l,r);src,dst=(l,r)if onl else(r,l)
  if not src:return
  x=src[0]
  if x[0]=='x':calls+=1
  if x[0]!='r':return
  _,b,aa,c=x;act=rows[q,b]
  if act[2]!=q or act[1]==onl:return
  unary+=1
  for n in(range(c,c+2*(radius+1)+1)if aa else(c,)):
   for i in set(range(1,min(n,radius+2)))|set(range(max(1,n-radius-1),n)):
    f=(('r',b,0,n-i),)+src[1:];second=(('r',act[0],0,i),)+dst
    ll,rr=(f,second)if onl else(second,f);collect(q,onl,ll,rr)
 start=time.monotonic();receipt=s.validate(rows,cs,observe)
 assert receipt['ok'],receipt
 allwin,closure=blank(table,6,radius)
 for q in s.BOXSTATES:windows[inv[q]].update(allwin[inv[q]])
 tape=set();q=0;h=0
 for _ in range(a.steps):
  windows[q].add(sum(int(h+j in tape)<<(j+radius)for j in range(-radius,radius+1)))
  w,d,q=table[q,int(h in tape)];(tape.add if w else tape.discard)(h);h+=1 if d else -1
 expected={h-1,h,h+48};p=h+49
 for v in[0,0,0,0,0,0,2,0,0]+[1]*26:expected.update(range(p+1,p+v+2));p+=v+2
 assert q==inv[84] and tape==expected
 refined={q:windows[q]&allwin[q]for q in windows}
 text=''.join(f'{q} {(m>>radius)&1} {m}\n'for q in range(196)for m in sorted(refined[q]))
 (a.output/'source_contexts.txt').write_text(text)
 receipt.update(zero_only_sites=a.zero_only,unreachable_sites=a.skip_sites,machine_sha256=hashlib.sha256(a.table.read_bytes()).hexdigest(),source_sha256=hashlib.sha256(a.sites.read_bytes()).hexdigest(),radius=radius,blank_window_closure=closure,windows=sum(map(len,refined.values())),unary_events=unary,box_events=calls,seconds=time.monotonic()-start,context_sha256=hashlib.sha256(text.encode()).hexdigest(),scope='Affine symbolic source-frame contracts; whole native engine macro controls conservatively covered by independent blank closure; no Lean check')
 (a.output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
