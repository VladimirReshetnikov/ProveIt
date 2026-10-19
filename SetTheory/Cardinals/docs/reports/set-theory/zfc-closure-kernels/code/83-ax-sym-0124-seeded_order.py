#!/usr/bin/env python3
"""Source grammar exploration from pinned original203 phrases.
Candidate source only; no implicit binary-machine correctness claim.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter,defaultdict
import sys,json,random,time,argparse,itertools
ROOT=Path(__file__).resolve().parent
import source_model as a
seeddata=json.loads((a.DATA_DIR/'sparse201.json').read_text())
a.NODES.clear();a.NODES.update({int(k):tuple(map(tuple,v)) for k,v in seeddata['nodes'].items()})
a.bounds.cache_clear();a.normal.cache_clear()
N=a.NODES

# original source phrase expansions in the same source-independent atom alphabet.
@lru_cache(None)
def flat(e):
 x=a.normal(e)
 es=x[1:] if x[0]=='S' else (x,)
 return tuple(a.ENCODE[a.map_normal(t)] for t in es)
words_by_node={i:flat(('N',i)) for i in N if a.normal(('N',i))[0]=='S'}
node_by_word={w:i for i,w in words_by_node.items()}
trie={}
for w,n in node_by_word.items():
 t=trie
 for sym in w:t=t.setdefault(sym,{})
 t['N']=n
@lru_cache(None)
def descendants(e):
 if e[0]!='N':return frozenset()
 l,r=N[e[1]]
 return frozenset({e[1]})|descendants(l)|descendants(r)
# Mapping all canonical atoms to existing original source leaf/subtree.
edge_by_normal={a.normal(('N',i)):('N',i) for i in N}
atom_edges={}
for e,k in a.ENCODE.items():
 # canonical normal -> region token needs inverse conversion.
 def normal_from_region(t):
  if t[0]=='A':
   l,r=a.ATOMS[t[1]];return ('A',normal_from_region(l),normal_from_region(r))
  if t[0]=='S':return ('S',*(normal_from_region(x) for x in a.SEQS[t[1]]))
  return t
 nf=normal_from_region(e)
 atom_edges[k]=edge_by_normal[nf] if nf[0] in ('A','S') else nf

ROLE_NAMES=('a','b','c')
ROLE_PERMS=tuple(itertools.permutations(ROLE_NAMES))
def subst(f,p):
 if f in ROLE_NAMES if isinstance(f,str) else False:return dict(zip(ROLE_NAMES,p))[f]
 if isinstance(f,tuple):return (f[0],subst(f[1],p),subst(f[2],p))
 return f
role_rows=[]
for row in a.ROWS[1:]:
 lane=[]
 for p in ROLE_PERMS:
  f=subst(row,p)
  macro_word=tuple(t for m in a.theory.emit(f) for t in a.MACROS[m])
  lane.append(tuple(a.ENCODE[a.map_normal(t)] for t in macro_word))
 role_rows.append(lane)

# Exact reuse-oriented DP: all dictionary phrases remain available, final
# dependency union counts each retained source node exactly once.
def parse(word,rng,noise=0.,price=None):
 n=len(word);cost=[float('inf')]*(n+1);choice=[None]*n;cost[n]=0.
 for i in range(n-1,-1,-1):
  e=atom_edges[word[i]];opts=[(i+1,e)]
  t=trie;j=i
  while j<n and word[j] in t:
   t=t[word[j]];j+=1
   if 'N' in t:opts.append((j,('N',t['N'])))
  best=None
  for j,e in opts:
   c=cost[j]+1+(noise*rng.random())
   if price is not None:c+=price*len(descendants(e))
   if best is None or c<best[0]:best=(c,j,e)
  cost[i],j,e=best;choice[i]=(j,e)
 out=[];i=0
 while i<n:
  j,e=choice[i];out.append(e);i=j
 return tuple(out)

def compile_word(word,rng,noise=0.,price=None):
 pieces=parse(word,rng,noise,price)
 nodes=dict(N);pair_index={v:k for k,v in nodes.items()};oldroot=183
 def pair(l,r):
  p=l,r
  if p in pair_index:return ('N',pair_index[p])
  n=max(nodes)+1;nodes[n]=p;pair_index[p]=n;return ('N',n)
 # Build sequence at each split by maximal retained original phrase reuse.
 # New pieces can be associated to expose old pairs. A greedy pair-frequency
 # tie break with old pairs always preferred preserves source semantics.
 seq=list(pieces)
 while len(seq)>1:
  choices=[]
  for i,p in enumerate(zip(seq,seq[1:])):
   old=p in pair_index
   score=10000*old+sum(q==p for q in zip(seq,seq[1:]))+rng.random()*.1
   choices.append((score,i,p))
  _,i,p=max(choices);e=pair(*p)
  ns=[];j=0
  while j<len(seq):
   if j+1<len(seq) and (seq[j],seq[j+1])==p:ns.append(e);j+=2
   else:ns.append(seq[j]);j+=1
  seq=ns
 axroot=seq[0]
 # All occurrences of original complete AX replaced, rest source unchanged.
 @lru_cache(None)
 def changed(e):
  if e==('N',oldroot):return axroot
  if e[0]!='N':return e
  l,r=N[e[1]];nl,nr=changed(l),changed(r)
  return e if (nl,nr)==(l,r) else pair(nl,nr)
 final=changed(('N',a.DATA['root']))
 seen=set()
 @lru_cache(None)
 def metric(e):
  if e[0]!='N':return 0,0,0
  seen.add(e[1]);l,r=map(metric,nodes[e[1]])
  p=l[0]+1;return p,max(p,l[1],r[1]),1+max(l[2],r[2])
 p,z,d=metric(final)
 return {i:nodes[i] for i in sorted(seen)},final[1],(len(seen),z,d),pieces

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--runs',type=int,default=20000);ap.add_argument('--seed',type=int,default=246193);ap.add_argument('--output',type=Path,default=Path(__file__).with_name('results'));args=ap.parse_args()
 args.output.mkdir(parents=True,exist_ok=True);rng=random.Random(args.seed);start=time.monotonic();best=(1000,1000,1000);bestcost=1000;history=[];champ=None
 for trial in range(args.runs):
  if trial==0:order=list(range(8));roles=[0]*8
  elif champ is not None and rng.random()<.85:
   order,roles=map(list,champ)
   if rng.random()<.5:x,y=rng.sample(range(8),2);order[x],order[y]=order[y],order[x]
   else:roles[rng.randrange(8)]=rng.randrange(6)
  else:order=rng.sample(range(8),8);roles=[rng.randrange(6) for _ in range(8)]
  w=a.PREFIX+sum((role_rows[i][roles[i]] for i in order),())+a.SUFFIX
  noise=0 if trial%4 else rng.random()*.6
  price=None if trial%5 else rng.random()*.02
  nodes,root,m,pieces=compile_word(w,rng,noise,price)
  if champ is None or m[0]<=bestcost or rng.random()<.015:champ=tuple(order),tuple(roles)
  if m<best:
   best=m;bestcost=m[0];champ=tuple(order),tuple(roles)
   row=dict(trial=trial,order=order,roles=roles,role_permutations=[ROLE_PERMS[i] for i in roles],metrics=m,pieces=len(pieces),seconds=time.monotonic()-start)
   history.append(row);record=dict(**row,root=root,nodes=nodes,ax_word=w,ax_pieces=pieces)
   (args.output/'best.json').write_text(json.dumps(record,indent=2)+'\n');(args.output/f'candidate_{trial}_{m[0]}.json').write_text(json.dumps(record,indent=2)+'\n')
   print('BEST',row,flush=True)
  if trial%500==0:print('progress',trial,best,round(time.monotonic()-start,2),flush=True)
 summary=dict(runs=args.runs,best=best,history=history,seconds=time.monotonic()-start)
 (args.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary),flush=True)
if __name__=='__main__':main()
