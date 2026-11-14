from pathlib import Path
from functools import lru_cache
import argparse,hashlib,json,random,sys,time
sys.dont_write_bytecode=True
import search_directional as D
L=D.L
class Node(tuple):
 def __new__(cls,children):
  self=tuple.__new__(cls,children);self.cached_hash=tuple.__hash__(self);return self
 def __hash__(self):return self.cached_hash
intern_pool={}
def intern(n):
 if isinstance(n,Node)or L.leaf(n):return n
 key=intern(n[0]),intern(n[1])
 if key not in intern_pool:intern_pool[key]=Node(key)
 return intern_pool[key]
@lru_cache(200000)
def leaves(n):
 return 1 if L.leaf(n) else leaves(n[0])+leaves(n[1])
@lru_cache(200000)
def badcount(n,r=0):
 if r>=6:return leaves(n)
 if L.leaf(n):return 0
 return badcount(n[0],r+1)+badcount(n[1],0)
@lru_cache(200000)
def terminal(n,r=0):
 if L.leaf(n):return int(r>=5)
 return terminal(n[0],min(5,r+1))+terminal(n[1],0)
@lru_cache(200000)
def maxzero(n,r=0):
 if L.leaf(n):return r
 return max(maxzero(n[0],r+1),r,maxzero(n[1],0))
@lru_cache(200000)
def depth(n):
 return 0 if L.leaf(n) else 1+max(depth(n[0]),depth(n[1]))
def score(n):
 return maxzero(n),badcount(n),terminal(n),depth(n)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('label');ap.add_argument('--depth',type=int,default=20);ap.add_argument('--width',type=int,default=20);args=ap.parse_args()
 b=D.I.base
 if args.label=='A':tp=b/'machine/variant_plain/u208.native.tm';sp=b/'machine/variant_plain/u208.sites.json'
 else:tp=b/'machine/u208.native.tm';sp=b/'machine/u208.sites.json'
 t=D.I.read(tp);ss=json.loads(sp.read_text());root=intern(L.tree(ss));seen={tuple(t.values())};front=[(t,root,[])];began=time.monotonic();rng=random.Random(327819);best=score(root);results=[]
 out=D.S.work/('shortzero_'+args.label);out.mkdir(exist_ok=True);D.out=out
 for depth in range(1,args.depth+1):
  cand=[]
  for t,r,hist in front:
   for rot in D.enum(t,r):
    nt,nr=D.rotate(t,r,rot);nr=intern(nr);k=tuple(nt.values())
    if k in seen:continue
    seen.add(k);sc=score(nr);nh=hist+[rot]
    if sc<best:best=sc;print('BEST',depth,best,nh,flush=True)
    if sc[0]<=5:
     mt={(q,b):(w,d,75 if z==34 else z)for(q,b),(w,d,z)in nt.items()if q!=34}
     rec=D.test(mt,nr,nh,[(34,75)],len(results));results.append(rec)
     if rec['pass']:print('FOUND_FINITE',rec,flush=True)
    cand.append((sc,rng.random(),nt,nr,nh))
  cand.sort(key=lambda x:x[:2]);front=[x[2:]for x in cand[:args.width]]
  print('DEPTH',depth,'seen',len(seen),'best',best,'seconds',time.monotonic()-began,flush=True)
  (out/'progress.json').write_text(json.dumps({'depth':depth,'seen':len(seen),'best':best,'results':results},indent=2)+'\n')
  if not front:break
if __name__=='__main__':main()
