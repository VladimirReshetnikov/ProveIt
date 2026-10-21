#!/usr/bin/env python3
"""Native-zero condensed detachment: complete cyclic unification for C(0,0)=0.
Research search; explicit proof substitutions are separately checked.
"""
import argparse,heapq,itertools,json,re,time,sys
from pathlib import Path
from functools import lru_cache
T='T'
def C(a,b):return T if a==b==T else (a,b)
@lru_cache(None)
def size(t):return 1 if not isinstance(t,tuple) else 1+size(t[0])+size(t[1])
@lru_cache(None)
def nvars(t):return max(nvars(t[0]),nvars(t[1])) if isinstance(t,tuple) else t+1 if isinstance(t,int) else 0
@lru_cache(None)
def rename(t,off):return (rename(t[0],off),rename(t[1],off)) if isinstance(t,tuple) else t+off if isinstance(t,int) else t
def canon(t):
 d={}
 def f(x):return C(f(x[0]),f(x[1])) if isinstance(x,tuple) else d.setdefault(x,len(d)) if isinstance(x,int) else x
 return f(t)
def norm(t):return C(norm(t[0]),norm(t[1])) if isinstance(t,tuple) else t
def parse(s):
 ts=re.findall(r'\d+|T|[()>]',s);i=0
 def go():
  nonlocal i
  t=ts[i];i+=1
  if t=='(':
   a=go();assert ts[i]=='>';i+=1;b=go();assert ts[i]==')';i+=1;return C(a,b)
  return int(t) if t.isdigit() else t
 out=go();assert i==len(ts);return out
def fmt(t):return '('+fmt(t[0])+'>'+fmt(t[1])+')' if isinstance(t,tuple) else str(t)
def subsumes(p,t):
 env={};todo=[(p,t)]
 while todo:
  a,b=todo.pop()
  if isinstance(a,int):
   if a in env:
    if env[a]!=b:return False
   else:env[a]=b
  elif isinstance(a,tuple):
   if not isinstance(b,tuple):return False
   todo.append((a[0],b[0]));todo.append((a[1],b[1]))
  elif a!=b:return False
 return True

def detach(major,minor,details=False):
 if not isinstance(major,tuple):return None
 off=nvars(major);minor=rename(minor,off);bindings={};zero_cycles=0
 def deref(t):
  while isinstance(t,int) and t in bindings:t=bindings[t]
  return t
 def occurs(v,t):
  t=deref(t)
  return v==t if not isinstance(t,tuple) else occurs(v,t[0]) or occurs(v,t[1])
 def collapse(t):
  t=deref(t)
  if isinstance(t,int):bindings[t]=T
  elif isinstance(t,tuple):collapse(t[0]);collapse(t[1])
  elif t!=T:raise ValueError('nonzero constant')
 todo=[(major[0],minor)]
 while todo:
  a,b=todo.pop();a,b=deref(a),deref(b)
  if a==b:continue
  if isinstance(b,int) and not isinstance(a,int):a,b=b,a
  if isinstance(a,int):
   if occurs(a,b):
    zero_cycles+=1;collapse(b);bindings[a]=T
   else:bindings[a]=b
  elif a==T:collapse(b)
  elif b==T:collapse(a)
  elif isinstance(a,tuple) and isinstance(b,tuple):todo.append((a[0],b[0]));todo.append((a[1],b[1]))
  else:return None
 def sub(t):
  t=deref(t)
  return C(sub(t[0]),sub(t[1])) if isinstance(t,tuple) else t
 out=canon(sub(major[1]))
 if details:
  return out, {str(v):sub(v) for v in range(nvars(major))},{str(v):sub(v+off) for v in range(nvars(minor)-off)},zero_cycles
 return out

def run(a):
 old=json.loads(Path(a.input).read_text());nodes=[dict(x) for x in old['formulas']]
 terms=[parse(x['term']) for x in nodes];known={t:i for i,t in enumerate(terms)}
 active=[False]*len(nodes);processed=[];pending=[];found={};start=time.monotonic();attempts=0;new_cycles=0
 # All axioms are valid under any natural assignment; prior fragments need no numerical bounds beyond subterm domination.
 hints=[]
 coq=Path(a.hints).read_text()
 for m in re.finditer(r'Lemma cd_(\d+).*?: thm230 (.*?)\.\s*Proof',coq,re.S):
  toks=re.findall(r'wim|v\d+|\d+|[()]',m[2]);i=0
  def go():
   nonlocal i
   x=toks[i];i+=1
   if x=='(':
    if toks[i]=='wim':
     i+=1;y=go();z=go();assert toks[i]==')';i+=1;return C(y,z)
    y=go();assert toks[i]==')';i+=1;return y
   if x=='wim':return C(go(),go())
   if x.startswith('v'):return int(x[1:])
   return T if x=='0' else int(x)
  try:h=canon(go());hints.append((int(m[1]),h))
  except Exception:pass
 targets={'I':C(0,0),'K':C(0,C(1,0)),'P':C(C(C(0,1),0),0),'cd59':C(C(0,1),C(C(C(0,2),0),1)),'B':C(C(0,1),C(C(1,2),C(0,2))),'S':C(C(0,C(1,2)),C(C(0,1),C(0,2)))}
 reached_hints={}
 def priority(t):
  matches=[n for n,h in hints if size(t)<=size(h) and subsumes(t,h)]
  return (min([size(t)]+[max(1,size(t)-a.hint_bonus) for _ in matches]),size(t))
 def insert_existing(i):
  t=terms[i]
  if any(active[j] and size(terms[j])<=size(t) and subsumes(terms[j],t)for j in range(i)):return
  active[i]=True
  for j in range(i):
   if active[j] and size(t)<=size(terms[j]) and subsumes(t,terms[j]):active[j]=False
 for i in range(len(terms)):insert_existing(i)
 for i,t in enumerate(terms):
  if active[i]:heapq.heappush(pending,(*priority(t),i))
 def add(t,parent):
  if t is None or size(t)>a.maxsize or t in known:return
  if any(active[j] and size(terms[j])<=size(t) and subsumes(terms[j],t)for j in range(len(terms))):return
  i=len(terms);terms.append(t);known[t]=i;active.append(True);nodes.append({'id':i,'term':fmt(t),'parent':parent})
  for j in range(i):
   if active[j] and size(t)<=size(terms[j]) and subsumes(t,terms[j]):active[j]=False
  heapq.heappush(pending,(*priority(t),i))
  for name,h in targets.items():
   if name not in found and size(t)<=size(h) and subsumes(t,h):found[name]=i;print('FOUND',name,i,fmt(t),flush=True)
  for n,h in hints:
   if n not in reached_hints and size(t)<=size(h) and subsumes(t,h):reached_hints[n]=i;print('HINT',n,i,fmt(t),flush=True)
 while pending and time.monotonic()-start<a.seconds and len(terms)<a.maxforms and len(processed)<a.maxprocessed:
  *_,i=heapq.heappop(pending)
  if not active[i]:continue
  x=terms[i]
  for j in processed+[i]:
   if not active[j]:continue
   y=terms[j]
   for major,minor in ((i,j),(j,i)) if i!=j else ((i,j),):
    attempts+=1;t=detach(terms[major],terms[minor]);add(t,{'major':major,'minor':minor,'rule':'native-zero-cd'})
  processed.append(i)
  if len(processed)%100==0:print('PROGRESS',len(processed),len(terms),sum(active),attempts,round(time.monotonic()-start,2),flush=True)
  if any(k in found for k in ['cd59','B','S']):break
 out={'input':a.input,'bounds':vars(a),'actual':{'forms':len(terms),'active':sum(active),'attempts':attempts,'seconds':time.monotonic()-start,'processed':len(processed)},'found':found,'hints_found':reached_hints,'formulas':nodes}
 Path(a.output).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='formulas'},indent=2),flush=True)
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--input',default='prior_reports/research218_progress_latex/research218_companion/checks/dominated/bounded_cd_refined_result.json');ap.add_argument('--hints',default='prior_reports/research218_progress_latex/research218_companion/evidence/logic/CD230.v');ap.add_argument('--output',default='formalism_work/zero_cd_result.json');ap.add_argument('--seconds',type=float,default=360);ap.add_argument('--maxsize',type=int,default=41);ap.add_argument('--maxforms',type=int,default=20000);ap.add_argument('--maxprocessed',type=int,default=5000);ap.add_argument('--hint-bonus',type=int,default=8);run(ap.parse_args())
