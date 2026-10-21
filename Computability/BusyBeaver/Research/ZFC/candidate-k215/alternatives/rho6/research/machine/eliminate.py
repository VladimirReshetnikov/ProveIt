#!/usr/bin/env python3
"""Search retained-checkpoint one-state elimination with exact finite-window joins.
The dropped state is an old-run interior, not a pointwise mapped state.
Every starting tape is covered by the inductive window domain.
"""
from pathlib import Path
from collections import defaultdict,Counter
import sys, json, itertools, time, hashlib, importlib.util
D=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('check',D/'folds/check_joint_fold.py'); c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)

def main():
 oldp=Path(sys.argv[1]);out=Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=False)
 O,st=c.read(oldp);Q={q for q,b in O};RADIUS=7;FUEL=97;tic=time.monotonic();I=c.domain(O,st,RADIUS)
 incoming=defaultdict(list)
 for k,(w,d,z) in O.items():
  if z in Q and k[0]!=z: incoming[z].append(k)
 eligible={q:ks[0]for q,ks in incoming.items()if q!=st and len(ks)==1}
 print('eligible',eligible,flush=True)
 stats=Counter();hits=[];witnesses=[]
 def step(T,q,h,m):
  b=(m>>(h+RADIUS))&1;w,d,z=T[q,b]
  return z,h+d,(m&~(1<<(h+RADIUS)))|(w<<(h+RADIUS))
 for drop,k in sorted(eligible.items()):
  q,b=k; ws=sorted(m for m in I[q]if(m>>RADIUS)&1==b)
  if len(ws)>2:ws=[ws[0],ws[-1],*ws[1:-1]]
  oldpaths={};N={kk:act for kk,act in O.items()if kk[0]!=drop}
  def check(act,all_words=True):
   N[k]=act;hist=Counter()
   for m in ws:
    if m not in oldpaths:
     goals={};oq,oh,om=q,0,m;oldhalt=None
     for oldn in range(1,FUEL+1):
      if oq==254 or not -RADIUS<=oh<=RADIUS: break
      oq,oh,om=step(O,oq,oh,om)
      if oq==254: oldhalt=oldn
      if oq!=drop: goals.setdefault((oq,oh,om),oldn)
     oldpaths[m]=(goals,oldhalt)
    goals,oldhalt=oldpaths[m];nq,nh,nm=q,0,m;seen=set();joined=False
    for newn in range(1,FUEL+1):
     if nq==254 or not -RADIUS<=nh<=RADIUS: break
     if(nq,nh,nm)in seen:break
     seen.add((nq,nh,nm));nq,nh,nm=step(N,nq,nh,nm)
     if nq==254:
      if oldhalt is not None:joined=True;hist[oldhalt,newn]+=1
      break
     if(nq,nh,nm)in goals:joined=True;hist[goals[nq,nh,nm],newn]+=1;break
    if not joined:return {'window':m,'reason':'no_positive_retained_join'}
   return hist
  for act in itertools.product((0,1),(-1,1),sorted(Q-{drop}|{254})):
   stats['attempted']+=1;f=check(act)
   if isinstance(f,dict) and not isinstance(f,Counter):stats['rejected']+=1;continue
   stats['hits']+=1;hit={'drop':drop,'row':list(k),'old':O[k],'new':act,'contexts':len(ws),'histogram':[[a,b,n]for(a,b),n in sorted(f.items())]};hits.append(hit)
   label=f'hit-{drop}-{act[0]}-{act[1]}-{act[2]}'; p=out/(label+'.tm');p.write_text('#! start '+str(st)+'\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(N.items())))
   print('HIT',hit,flush=True)
  print('drop',drop,'attempted',stats['attempted'],'elapsed',round(time.monotonic()-tic,2),flush=True)
 receipt={'status':'COMPLETE_FINITE_WINDOW_ELIMINATION_SEARCH','stats':dict(stats),'eligible':{str(k):v for k,v in eligible.items()},'hits':hits,'radius':RADIUS,'fuel':FUEL,'seconds':time.monotonic()-tic,'old_sha256':hashlib.sha256(oldp.read_bytes()).hexdigest(),'code_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Exactly one changed incoming row to a noninitial state with unique external incoming row. Deleted state is interior of old macroblocks, all retained states are common checkpoints. Every finite-window proof covers arbitrary initial tapes; failure only bounded proof-search failure.'}
 (out/'result.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
