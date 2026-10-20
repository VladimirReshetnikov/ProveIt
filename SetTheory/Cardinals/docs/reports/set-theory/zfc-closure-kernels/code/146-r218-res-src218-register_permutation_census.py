#!/usr/bin/env python3
"""All8! register permutations against the existing decoder-alias catalogue.

This does not synthesize new aliases or redesign the arithmetic engine.  It
counts every old alias whose two exact source-role patterns occur after a
global renaming, including pairs that were not aliased before renaming.
"""
from pathlib import Path
from functools import cache
from itertools import permutations,combinations
from collections import Counter
import hashlib,json,sys,time
from hardware_objective219 import ROOT,r
from grammar_search import nodes
p=ROOT/'baseline219/K219_Construction_2026-10-20/machine';raw=(p/'sites219.json').read_bytes()
tree=r.normalise(r.s.tree(json.loads(raw)));T=r.b.read_table((p/'k219.native.tm').read_bytes())
groups,paths,ns=r.mapping(T,tree);internal=[n for n in nodes(tree)if not r.s.leaf(n)]
aliases={q:tuple(nn)for q,nn in groups.items()if len(nn)>1};assert len(aliases)==15 and all(len(nn)==2 for nn in aliases.values())
def constraints(a,b):
 mp={};reverse={};todo=[(a,b)]
 while todo:
  x,y=todo.pop();xl,yl=r.s.leaf(x),r.s.leaf(y)
  if xl!=yl:return None
  if not xl:todo.extend(zip(x,y));continue
  if x[0]!=y[0]:return None
  if x[0]not in('CI','CD'):
   if x!=y:return None
   continue
  i,j=x[1],y[1]
  if(i==0)!=(j==0):return None
  if i in mp and mp[i]!=j or j in reverse and reverse[j]!=i:return None
  mp[i]=j;reverse[j]=i
 return tuple(sorted(mp.items()))
targets={n for nn in aliases.values()for n in nn}|{(('CD',6),('CC',2))}
patterns={target:set(v for source in internal if(v:=constraints(source,target))is not None)for target in targets}
def evaluate(perm):
 present={target:any(all(perm[i]==j for i,j in req)for req in options)for target,options in patterns.items()}
 available=[q for q,nn in aliases.items()if all(present[n]for n in nn)]
 # State13 has immutable arithmetic work. If it is outside the new source,
 # count the orphan. If its role is also used in the108 alias, count the
 # duplicate. Retaining13 alone with no108 alias needs neither surcharge.
 p6=(('CD',6),('CC',2));extra=int(not present[p6]or 108 in available)
 return dict(known_aliases=len(available),available_alias_states=sorted(available),
             q13_extra_physical_role=extra,model_lower_bound=50+len(internal)-len(available)+extra)
started=time.monotonic();hist=Counter();best=1000;best_permutations=[];near=[]
for tail in permutations(range(1,9)):
 perm=(0,)+tail;rec=evaluate(perm);cost=rec['model_lower_bound'];hist[cost]+=1
 if cost<best:best=cost;best_permutations=[]
 if cost==best:best_permutations.append(list(perm))
 if cost<=220:near.append(dict(permutation=perm,**rec))
swaps=[]
for i,j in combinations(range(1,9),2):
 perm=list(range(9));perm[i],perm[j]=perm[j],perm[i];swaps.append(dict(swap=[i,j],**evaluate(perm)))
out=ROOT/'source218/register_permutations.json'
receipt=dict(status='EXACT_EXISTING_ALIAS_CATALOGUE_CENSUS',permutations=40320,fixed_register=0,
             internal_nodes=len(internal),known_alias_pairs=len(aliases),minimum_model_bound=best,
             best_permutations=best_permutations,histogram=dict(sorted(hist.items())),near=near,transpositions=swaps,
             source_sha256=hashlib.sha256(raw).hexdigest(),code_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             seconds=time.monotonic()-started,
             scope='Only the existing15 physical alias pairs and state13 arithmetic-role requirement. Ignores context/other helper overhead. New aliases, changed arithmetic architecture, and new startup encodings are outside this census.')
out.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items()if k not in('near','transpositions')},indent=2))
