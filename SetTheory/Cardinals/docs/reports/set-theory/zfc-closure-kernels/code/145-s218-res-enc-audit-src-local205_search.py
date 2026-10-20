"""Occurrence-local rotations; count DAG changes from the changed ancestry only."""
from pathlib import Path
from collections import Counter
from functools import lru_cache
import argparse,json,random,time,heapq
from dag205_search import Hdag,compact,s
from environment import BASE_SOURCE

def occurrences(d,root):
 R=d.reach(root);counts=Counter({root:1})
 for q in sorted(R,reverse=True):
  if not d.leaf(q):
   for c in d.nodes[q]:counts[c]+=counts[q]
 return R,counts

def local(d,root):
 R,counts=occurrences(d,root);todo=[(root,())]
 while todo:
  q,anc=todo.pop()
  if d.leaf(q):continue
  a,b=d.nodes[q];todo.extend([(a,anc+((q,0),)),(b,anc+((q,1),))])
  for nq,direction in d.rotations(q):
   oldinner=d.nodes[q][0 if direction=='right'else 1]
   newinner=d.nodes[nq][1 if direction=='right'else 0]
   delta=Counter();delta[q]-=1;delta[oldinner]-=1;delta[nq]+=1;delta[newinner]+=1;nr=nq
   for oldp,side in reversed(anc):
    l,r=d.nodes[oldp];np=d.add((nr,r)if side==0 else(l,nr));delta[oldp]-=1;delta[np]+=1;nr=np
   nn=len(R)
   for v,change in delta.items():
    before=counts[v];after=before+change
    assert after>=0
    nn+=int(after>0)-int(before>0)
   yield nr,nn

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,default=BASE_SOURCE);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--steps',type=int,default=20);ap.add_argument('--quota',type=int,default=30);ap.add_argument('--maxdag',type=int,default=209);ap.add_argument('--seed',type=int,default=205218);a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True)
 rows=json.loads(a.source.read_text());graph=s.graph_intervals(rows);d=Hdag();root=d.intern(s.tree(rows));front=[root];seen={d.hashes[root]};best=len(d.reach(root));rng=random.Random(a.seed);start=time.monotonic();improvements=[]
 for depth in range(a.steps):
  heaps={n:[]for n in range(205,a.maxdag+1)};counts=Counter();generated=0
  while front:
   cur=front.pop()
   for nr,nn in local(d,cur):
    h=d.hashes[nr]
    if h in seen:continue
    seen.add(h);generated+=1
    if d.zero[nr]>6 or nn>a.maxdag:continue
    counts[nn]+=1
    if nn<best:
     assert nn==len(d.reach(nr));t=d.tree(nr);ss=s.sites(t)
     assert s.graph_intervals(ss)==graph and s.graph_arithmetic(ss)[0]==graph
     best=nn;name=f'best_n{nn}_d{depth+1}';(a.out/(name+'.sites.json')).write_bytes(s.compact(ss));rec={'name':name,'metrics':s.metrics(t),'cfg_identical':True,'seconds':time.monotonic()-start};(a.out/(name+'.json')).write_text(json.dumps(rec,indent=2)+'\n');improvements.append(rec);print('BEST',rec,flush=True)
     if nn<=205:return
    if nn in heaps:
     item=(rng.random(),nr);heap=heaps[nn]
     if len(heap)<a.quota:heapq.heappush(heap,item)
     elif item>heap[0]:heapq.heapreplace(heap,item)
   if len(d.nodes)>150000:
    keep=[(n,score,q)for n,hp in heaps.items()for score,q in hp];nf=len(front);d,rr=compact(d,front+[q for n,sc,q in keep]);front=rr[:nf];heaps={n:[]for n in heaps}
    for(n,score,oldq),newq in zip(keep,rr[nf:]):heapq.heappush(heaps[n],(score,newq))
  front=[q for h in heaps.values()for score,q in h];d,front=compact(d,front)
  rec={'depth':depth+1,'frontier':len(front),'counts':dict(counts),'seen':len(seen),'best':best,'seconds':round(time.monotonic()-start,2)};print('DEPTH',json.dumps(rec),flush=True);(a.out/'summary.json').write_text(json.dumps({'last':rec,'improvements':improvements},indent=2)+'\n')
  if not front:break
if __name__=='__main__':main()
