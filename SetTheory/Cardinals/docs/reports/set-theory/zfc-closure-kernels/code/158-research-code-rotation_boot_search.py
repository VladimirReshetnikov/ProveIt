#!/usr/bin/env python3
"""Search semantics-preserving physical rotations for core217 initialization.

The search recognizes any complete source frame, not just the root. Candidate
hits still require the full unbounded runtime proof and seed calibration.
"""
from pathlib import Path
from functools import lru_cache
from array import array
import argparse,collections,hashlib,json,sys,time
HERE=Path(__file__).resolve().parent
PACKET=HERE.parent
import rotation_nodes as f
s,b=f.s,f.b

def rotations(table,tree,groups):
 incoming=collections.defaultdict(set)
 for key,act in table.items():incoming[act[2]].add(key)
 for q,ns in groups.items():
  if len(ns)!=1:continue
  node=next(iter(ns));ab=f.NODES[node]
  for edge in (0,1):
   r=table[q,edge][2]
   if f.isleaf(ab[edge]) or groups.get(r)!={ab[edge]}:continue
   if q==r or incoming[r]!={(q,edge)}:continue
   if not all(table[z,bit][:2]==(bit,1) for z in (q,r) for bit in (0,1)):continue
   if edge==0:
    (A,B),C=f.NODES[ab[0]],ab[1];newnode=f.intern((A,f.intern((B,C))))
    actions=[(q,0,table[r,0][2]),(q,1,r),(r,0,table[r,1][2]),(r,1,table[q,1][2])]
   else:
    A,(B,C)=ab[0],f.NODES[ab[1]];newnode=f.intern((f.intern((A,B)),C))
    actions=[(q,0,r),(q,1,table[r,1][2]),(r,0,table[q,0][2]),(r,1,table[r,0][2])]
   # The left factor must not escape by a break and the right factor must
   # not escape by a continue. The middle factor may have either exit.
   if f.boundary(A)[0] or f.boundary(C)[1]:continue
   memo={};nt=f.replace(tree,node,newnode,memo)
   ng={z:{f.replace(n,node,newnode,memo) for n in old} for z,old in groups.items()}
   ng[r]={f.NODES[newnode][1-edge]};tt=table.copy()
   for z,bit,target in actions:tt[z,bit]=bit,1,target
   mask=sum(1<<(2*z+bit) for z in (q,r) for bit in (0,1))
   yield (q,r,edge),tt,nt,ng,mask

def frame(h,ones,tree):
 if len(ones)<12 or min(ones)!=h-1:return None
 header=min((x for x in ones if x>=h+64),default=None)
 if header is None:return None
 node=tree;depth=0
 while not f.isleaf(node):
  node=f.NODES[node][int(h+depth in ones)];depth+=1
  if depth>64:return None
 if any(h+depth<=x<header for x in ones):return None
 p=header+1;end=max(ones);vals=[]
 while p<=end:
  if p in ones or p+1 not in ones:return None
  p+=1;n=0
  while p in ones:n+=1;p+=1
  vals.append(n-1)
 if len(vals)<10:return None
 phy=(6,2,0,4,3,7,8,5,1)
 return dict(head=h,pc=''.join(str(int(h+i in ones))for i in range(depth)),instruction=f.NODES[node],gap=header-h-64,registers=[vals[x]for x in phy],spares=vals[9:],support=sorted(ones))

def boot(table,tree,start,cap):
 q=start;h=0;ones=set();used=0
 for steps in range(cap+1):
  if q==254:return dict(status='HALT',steps=steps,used=used,q=q,head=h,ones=len(ones))
  if q==84:
   encoded=frame(h,ones,tree)
   if encoded is not None:return dict(status='FRAME',steps=steps,used=used,start=start,**encoded)
  if steps==cap:return dict(status='BOUND',steps=steps,used=used,q=q,head=h,ones=len(ones))
  bit=int(h in ones);used|=1<<(2*q+bit);w,d,z=table[q,bit]
  if not bit and z==q and (not ones or d==1 and h>max(ones) or d==-1 and h<min(ones)):
   return dict(status='RAY',steps=steps,used=used,q=q,head=h,ones=len(ones))
  if w:ones.add(h)
  else:ones.discard(h)
  q=z;h+=d

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--depth',type=int,default=5);ap.add_argument('--seconds',type=int,default=300)
 ap.add_argument('--cap',type=int,default=300000);ap.add_argument('--active-start0',action='store_true')
 ap.add_argument('--table',type=Path,default=PACKET/'data/core217.native.tm')
 ap.add_argument('--sites',type=Path,default=PACKET/'data/sites218.json')
 ap.add_argument('--table-only-dedup',action='store_true',help='Reproduce the first timed search, which deduplicated by physical table alone.')
 ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True)
 src=json.loads(a.sites.read_text());ut=s.tree(src)
 T=b.read_table(a.table.read_bytes());groups,_=b.decoder_map(T,ut)
 g={q:{f.pack(t)for t in ns}for q,ns in groups.items()};tree=f.pack(ut)
 keys=sorted(T);states=sorted({q for q,bit in keys});startindex=states.index(0)
 oldcfg=s.graph_arithmetic(src)[0];oldword=[x[1:] for x in src]
 initial=[boot(T,tree,q,a.cap) for q in states];seen={};count=0;checks=len(states);hits=[];rejected=[];began=time.monotonic();best=0
 def search(table,t,gr,boots,hist):
  nonlocal count,checks,best
  if time.monotonic()-began>a.seconds:return False
  key=hashlib.sha256(array('H',(table[k][2]for k in keys)).tobytes()+(b'' if a.table_only_dedup else t.to_bytes(8,'little'))).digest()
  if seen.get(key,a.depth+1)<=len(hist):return True
  seen[key]=len(hist);count+=1
  for result in boots:
   if result['status']=='FRAME':
    ut=f.unpack(t);ss=s.sites(ut)
    try:
     actual,_=b.decoder_map(table,ut)
     assert {q:{f.pack(n)for n in ns}for q,ns in actual.items()}==gr,'Decoder role relation differs'
     assert [x[1:]for x in ss]==oldword,'Primitive word differs'
     assert s.graph_arithmetic(ss)[0]==oldcfg==s.graph_intervals(ss),'Ordinal CFG differs'
    except Exception as e:
     rejected.append(dict(history=hist,reason=str(e)));print('Rejected frame:',str(e),hist,flush=True);continue
    d=a.output/f'hit{len(hits):03d}';d.mkdir(exist_ok=True)
    (d/'candidate.native.tm').write_bytes(b.table_bytes(table));(d/'sites.json').write_bytes(s.compact(ss))
    rec=dict(history=hist,frame={k:v for k,v in result.items()if k!='used'},metrics=s.metrics(ut),source_decoder='PASS',runtime='NOT CHECKED',seed_calibration='NOT CHECKED')
    (d/'discovery.json').write_text(json.dumps(rec,indent=2)+'\n');hits.append(rec);print('BOOT FRAME',str(d),rec,flush=True);return False
  score=max(x['ones']for x in boots if x['status']!='FRAME')
  if score>best:best=score;print('New maximum final support',score,'history',hist,'start0', {k:v for k,v in boots[startindex].items()if k!='used'},flush=True)
  if count%500==0:print('Layouts',count,'distinct',len(seen),'blank runs',checks,'seconds',round(time.monotonic()-began,1),flush=True)
  if len(hist)<a.depth:
   neighbors=list(rotations(table,t,gr));neighbors.sort(key=lambda row: not bool(row[4]&boots[startindex]['used']))
   for rot,tt,nt,ng,mask in neighbors:
    if a.active_start0 and not (mask&boots[startindex]['used']):continue
    nb=boots.copy()
    for i,old in enumerate(boots):
     if old['status']!='RAY' or mask&old['used']:nb[i]=boot(tt,nt,states[i],a.cap);checks+=1
    if not search(tt,nt,ng,nb,hist+[rot]):return False
  return True
 complete=search(T,tree,g,initial,[])
 receipt=dict(status='COMPLETE'if complete else'STOPPED',layouts=count,distinct=len(seen),blank_runs=checks,seconds=time.monotonic()-began,depth=a.depth,active_start0=a.active_start0,cap=a.cap,hits=hits,rejected_frames=rejected,maximum_final_support=best)
 receipt.update(table_only_dedup=a.table_only_dedup,table_sha256=hashlib.sha256(a.table.read_bytes()).hexdigest(),sites_sha256=hashlib.sha256(a.sites.read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
 (a.output/'result.json').write_text(json.dumps(receipt,indent=2)+'\n');print(receipt,flush=True)

if __name__=='__main__':main()
