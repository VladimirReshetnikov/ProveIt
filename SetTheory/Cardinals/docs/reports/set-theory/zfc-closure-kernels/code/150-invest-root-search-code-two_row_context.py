#!/usr/bin/env python3
"""Portable replay of the finite fold-plus-helper-row discovery search."""
from pathlib import Path
import argparse,json,sys,itertools,time
sys.path.insert(0,str(Path(__file__).resolve().parent))
import check_joint_fold as c,filter_source as f
ap=argparse.ArgumentParser()
ap.add_argument('--packet-root',type=Path,required=True)
ap.add_argument('--output',type=Path,required=True)
ap.add_argument('--domain',type=Path,required=True)
a=ap.parse_args();root=a.packet_root.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
old,start=c.read(root/'baseline218/k218.native.tm');I={int(q):v for q,v in json.loads(a.domain.read_text()).items()};Q=sorted(I);keep,drop=88,301;phi=lambda q:keep if q==drop else q
N={(q,b):(w,d,phi(z))for(q,b),(w,d,z)in old.items()if q!=drop};rad=9;fuel=97;paths={};patterns={};goals={};attempts=0;firststart=time.monotonic();hits=[]
for q,words in I.items():
 for b in (0,1):
  x=[m for m in words if(m>>rad)&1==b];patterns[q,b]=[x[0],x[-1],*x[1:-1]]if len(x)>2 else x

def one(q,m,collect=False):
 k=(q,m)
 if k not in goals:
  st=q;h=0;word=m;goal=set();halt=False
  for n in range(fuel):
   if st==254 or not-rad<=h<=rad:break
   b=(word>>(h+rad))&1;w,d,st=old[st,b];word=(word&~(1<<(h+rad)))|(w<<(h+rad));h+=d;goal.add((phi(st),h,word));halt|=st==254
  goals[k]=(goal,halt)
 goal,halt=goals[k];st=phi(q);h=0;word=m;visited=set();rows=[]
 for n in range(fuel):
  if st==254 or not-rad<=h<=rad:break
  key=(st,h,word)
  if key in visited:break
  visited.add(key);b=(word>>(h+rad))&1;rows.append((st,b));w,d,st=N[st,b];word=(word&~(1<<(h+rad)))|(w<<(h+rad));h+=d
  if(st,h,word)in goal or(st==254 and halt):return True,rows
 return False,rows

def check(qs):
 for q in qs:
  for b in(0,1):
   w,d,z=old[q,b]
   if N[phi(q),b]==(w,d,phi(z)):continue
   for m in patterns[q,b]:
    ok,rows=one(q,m)
    if not ok:return q,m,rows
 return None

actions=list(itertools.product((0,1),(-1,1),sorted(set(Q)-{drop}|{254})))
for ai,action in enumerate(actions):
 N[keep,0]=action;failure=check([keep,drop])
 if failure is None:print('BASEHIT',action,flush=True);continue
 q,m,rows=failure
 for helper in dict.fromkeys(rows):
  if helper[0]in(keep,drop):continue
  orig=N[helper]
  for change in actions:
   if change==orig:continue
   attempts+=1;N[helper]=change
   if not one(q,m)[0]:continue
   if check([keep,drop,helper[0]])is not None:continue
   hit={'a0':action,'helper':helper,'new':change,'attempt':attempts};print('HIT',hit,flush=True);hits.append(hit)
   (out/f'two_row_hit{len(hits):03d}.tm').write_bytes(f.encode(N));json.dump(hits,open(out/'two_row_hits.json','w'),indent=2)
  N[helper]=orig
 if ai%100==0:print('PROGRESS',ai,attempts,len(hits),time.monotonic()-firststart,flush=True)
print('COMPLETE',attempts,len(hits),time.monotonic()-firststart,flush=True)
json.dump({'status':'FINITE_DISCOVERY_ONLY','candidates':attempts,'hits':hits,'seconds':time.monotonic()-firststart},open(out/'two_row_result.json','w'),indent=2)
