#!/usr/bin/env python3
"""Deterministic finite beam over joint rotations; abstract grammar checks only."""
import argparse,json,time,heapq
from pathlib import Path
from functools import lru_cache
P=argparse.ArgumentParser();P.add_argument('seed',type=Path);P.add_argument('--inputs',type=Path,required=True);P.add_argument('--lock',type=Path,required=True);P.add_argument('--output',type=Path,required=True);P.add_argument('--depth',type=int,default=5);P.add_argument('--beam',type=int,default=30);a=P.parse_args()
s=json.loads((a.inputs/'closed-sequence-grammar-next22.json').read_text());symbols=json.loads((a.inputs/'semantic-symbols.json').read_text());enc={v:k for k,v in symbols.items()}
l=(a.inputs/'semantic.txt').read_text().splitlines();n,nr,na=map(int,l[0].split());names={int(q):w for k,w,q in map(str.split,l[1:n+1])};old={w:(w[:int(k)],w[int(k):]) for k,w,q in map(str.split,l[1:n+1])};allowed={c:int(m)for c,m in map(str.split,l[n+1+nr:])};byast={int(v):names[int(q)]for q,v in s['sequence_ast_roots'].items()}
d=json.loads(a.seed.read_text());initial={w:(l,r)for w,l,r in d['rules']};routes={(r['source'],r['read']):r['word']for r in d['routes']};roots={names[q]for q in s['required_entry_roots']if q not in{24,89,107,152,154,175,188,207,213,245}}|set(routes.values())
cs=[]
for c in s['left_entry_projection_constraints']:
 r=c['reason'];p=c['prefix'];p=str(r['previous'])+p if r.get('via')==177 else p
 cs.append((routes[r['source'],r['read']],p,''.join(enc[t]for t in c['word'])))
for row in a.lock.read_text().splitlines()[1:]:
 w,b,t=row.split();roots.add(w);cs.append((w,b,t))
def validchild(l,r):return(len(l)>1 or allowed[l]&1)and(len(r)>1 or allowed[r]&2)
def evaluate(g):
 try:
  for w,p,t in cs:
   for b in p:w=g[w][int(b)]
   if w!=t:return
  seen=set();todo=list(roots)
  while todo:
   w=todo.pop()
   if len(w)==1 or w in seen:continue
   seen.add(w);todo.extend(g[w])
  gg={w:g[w]for w in seen}
  def join(l,r):return(l[0]+1,max(l[0]+1,l[1],r[1]),max(l[2],r[2])+1,l[3]+r[3]+int(l[0]+1>5))
  @lru_cache(None)
  def wp(w):
   if len(w)==1:return ep(s['atoms'][symbols[w]]['ast'])
   return join(*(wp(x)for x in gg.get(w,old.get(w))))
  @lru_cache(None)
  def ep(i):
   if i in byast:return wp(byast[i])
   row=s['ast_dag'][i]
   if row[0]=='L':return(0,0,0,0)
   return join(ep(row[1]),ep(row[2]))
  prop=ep(s['original_ast'])
  if prop[1]>6 or prop[2]>64:return
  return gg,prop,len(gg)+1000*prop[3]
 except(KeyError,RecursionError,TypeError):return

def neighbors(g):
 for w,(l,r) in list(g.items()):
  if l in g:
   x,y=g[l];part=y+r
   if validchild(x,part)and(part in g or validchild(y,r)):
    h=g.copy();h.setdefault(part,(y,r));h[w]=(x,part);yield h,('left',w)
  if r in g:
   y,z=g[r];part=l+y
   if validchild(part,z)and(part in g or validchild(l,y)):
    h=g.copy();h.setdefault(part,(l,y));h[w]=(part,z);yield h,('right',w)
  for k in range(1,len(w)):
   x,y=w[:k],w[k:]
   if(x in g or x in symbols)and(y in g or y in symbols)and(x,y)!=(l,r)and validchild(x,y):
    h=g.copy();h[w]=(x,y);yield h,('cut',w,k)

def key(g):return tuple(sorted((w,len(c[0]))for w,c in g.items()))
init=evaluate(initial);assert init;best=init;beam=[(init,[])];seen={key(init[0])};total=0;t0=time.monotonic()
def save(best,history):
 g,p,c=best;out=d.copy();out.update(status='ABSTRACT_ROUTING_GRAMMAR_ONLY',rules_count=len(g),rules=[[w,*g[w]]for w in sorted(g)],properties=p,beam_repair=dict(score=c,history=history,elapsed=time.monotonic()-t0,evaluated=total));a.output.write_text(json.dumps(out,indent=2)+'\n')
save(best,[]);print('INITIAL',len(best[0]),best[1],flush=True)
for depth in range(1,a.depth+1):
 pool=[];serial=0
 for(cur,history)in beam:
  for g,m in neighbors(cur[0]):
   total+=1;r=evaluate(g)
   if r is None:continue
   k=key(r[0])
   if k in seen:continue
   seen.add(k);hist=history+[m]
   if r[2]<best[2]:best=r;save(best,hist);print('BEST',len(r[0]),r[1],'depth',depth,'evals',total,'sec',time.monotonic()-t0,flush=True)
   if len(r[0])<=160 and r[1][3]==0:save(r,hist);print('TARGET',flush=True);raise SystemExit(0)
   if r[2]<=best[2]+15:
    serial+=1;pool.append((r[2],len(r[0]),r[1][2],serial,r,hist))
 pool.sort(key=lambda x:x[:4]);beam=[(r,hist)for score,n,dep,ser,r,hist in pool[:a.beam]]
 print('LAYER',depth,'beam',len(beam),'pool',len(pool),'evals',total,'best',best[1],'sec',time.monotonic()-t0,flush=True)
 if not beam:break
print('DONE',total,time.monotonic()-t0,flush=True)
