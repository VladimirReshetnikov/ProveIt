#!/usr/bin/env python3
"""Delete one state through independently rewritable external entrances.
New paths must join before executing any other changed entrance, allowing composition.
"""
from pathlib import Path
from collections import defaultdict,Counter
import sys,json,itertools,time,hashlib,importlib.util
D=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('check',D/'folds/check_joint_fold.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
p=Path(sys.argv[1]);out=Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=False)
O,st=c.read(p);Q={q for q,b in O};rad=7;fuel=97;I=c.domain(O,st,rad);tic=time.monotonic();stats=Counter();hits=[];partial=[]
incoming=defaultdict(list)
for k,(w,d,z)in O.items():
 if k[0]!=z and z in Q:incoming[z].append(k)
def step(T,q,h,m):
 b=(m>>(h+rad))&1;w,d,z=T[q,b];return z,h+d,(m&~(1<<(h+rad)))|(w<<(h+rad))
for drop in sorted(Q-{st}):
 ks=incoming[drop];N={k:act for k,act in O.items()if k[0]!=drop};choices={};failed=None
 for k in ks:
  q,b=k;ws=sorted(m for m in I[q]if(m>>rad)&1==b)
  if len(ws)>2:ws=[ws[0],ws[-1],*ws[1:-1]]
  oldpaths={}
  def check(act):
   N[k]=act;hist=Counter()
   for m in ws:
    if m not in oldpaths:
     goals={};oq,oh,om=q,0,m;oldhalt=None
     for on in range(1,fuel+1):
      if oq==254 or not -rad<=oh<=rad:break
      oq,oh,om=step(O,oq,oh,om)
      if oq==254:oldhalt=on
      if oq!=drop:goals.setdefault((oq,oh,om),on)
     oldpaths[m]=goals,oldhalt
    goals,oldhalt=oldpaths[m];nq,nh,nm=q,0,m;seen=set();joined=False
    for nn in range(1,fuel+1):
     if nq==254 or nq==drop or not -rad<=nh<=rad:break
     nb=(nm>>(nh+rad))&1
     if nn>1 and(nq,nb)in ks:break
     if(nq,nh,nm)in seen:break
     seen.add((nq,nh,nm));nq,nh,nm=step(N,nq,nh,nm)
     if nq==254:
      if oldhalt is not None:joined=True;hist[oldhalt,nn]+=1
      break
     if(nq,nh,nm)in goals:joined=True;hist[goals[nq,nh,nm],nn]+=1;break
    if not joined:return None
   return hist
  opts=[]
  for act in itertools.product((0,1),(-1,1),sorted(Q-{drop}|{254})):
   stats['attempted']+=1;hist=check(act)
   if hist is None:continue
   opts.append(act)
  N[k]=O[k]
  if not opts:failed=k;break
  choices[k]=opts
 if failed is None:
  hit={'drop':drop,'choices':[{'row':k,'actions':v}for k,v in choices.items()]};hits.append(hit);print('COMPLETE_DROP',hit,flush=True)
 elif choices:
  item={'drop':drop,'failed':failed,'choices':[{'row':k,'actions':v}for k,v in choices.items()]};partial.append(item);print('PARTIAL_DROP',item,flush=True)
 stats['states']+=1
r={'status':'COMPLETE_FIRST_FAILURE_PRUNED_MULTI_ENTRANCE_SEARCH','stats':dict(stats),'hits':hits,'partial':partial,'radius':rad,'fuel':fuel,'seconds':time.monotonic()-tic,'old_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'code_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};(out/'result.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
