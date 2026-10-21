#!/usr/bin/env python3
"""Discover one-row stuttering-equivalent rewrites over an all-tape window invariant."""
from pathlib import Path
from collections import Counter
import sys,json,itertools,time,hashlib,importlib.util
D=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('check',D/'folds/check_joint_fold.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
def main():
 p=Path(sys.argv[1]);out=Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=False)
 O,st=c.read(p);Q={q for q,b in O};radius=7;fuel=97;tic=time.monotonic();I=c.domain(O,st,radius);N=dict(O);stats=Counter();hits=[]
 def step(T,q,h,m):
  b=(m>>(h+radius))&1;w,d,z=T[q,b];return z,h+d,(m&~(1<<(h+radius)))|(w<<(h+radius))
 for k in sorted(O):
  q,b=k;ws=sorted(m for m in I[q]if(m>>radius)&1==b)
  if len(ws)>2:ws=[ws[0],ws[-1],*ws[1:-1]]
  oldpaths={}
  def check(act):
   N[k]=act;hist=Counter()
   for m in ws:
    if m not in oldpaths:
     goals={};oq,oh,om=q,0,m;oldhalt=None
     for oldn in range(1,fuel+1):
      if oq==254 or not -radius<=oh<=radius:break
      oq,oh,om=step(O,oq,oh,om)
      if oq==254:oldhalt=oldn
      goals.setdefault((oq,oh,om),oldn)
     oldpaths[m]=goals,oldhalt
    goals,oldhalt=oldpaths[m];nq,nh,nm=q,0,m;seen=set();joined=False
    for newn in range(1,fuel+1):
     if nq==254 or not -radius<=nh<=radius:break
     if(nq,nh,nm)in seen:break
     seen.add((nq,nh,nm));nq,nh,nm=step(N,nq,nh,nm)
     if nq==254:
      if oldhalt is not None:joined=True;hist[oldhalt,newn]+=1
      break
     if(nq,nh,nm)in goals:joined=True;hist[goals[nq,nh,nm],newn]+=1;break
    if not joined:return None
   return hist
  for act in itertools.product((0,1),(-1,1),sorted(Q|{254})):
   if act==O[k]:continue
   stats['attempted']+=1;h=check(act)
   if h is None:stats['rejected']+=1;continue
   stats['hits']+=1;hit={'row':list(k),'old':list(O[k]),'new':list(act),'contexts':len(ws),'histogram':[[a,b,n]for(a,b),n in sorted(h.items())]};hits.append(hit)
   print('HIT',hit,flush=True)
  N[k]=O[k]
 receipt={'status':'COMPLETE_ONE_ROW_REWRITE_SEARCH','stats':dict(stats),'hits':hits,'radius':radius,'fuel':fuel,'seconds':time.monotonic()-tic,'old_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'code_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'One changed action, every write/move/target. Positive finite-window common-endpoint diagrams over original all-initial-tape invariant. Discovery only; independent audit is required before using a rewrite.'}
 (out/'result.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items()if k!='hits'},indent=2))
if __name__=='__main__':main()
