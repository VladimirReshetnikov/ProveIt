#!/usr/bin/env python3
"""Check closed-block commutations and generate reproducible AX order variants.

No binary-machine or state-count claim follows from this source-level checker.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import argparse, json, random

ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'reference/zfc245'

class Context:
 def __init__(self):
  self.source=json.loads((BASE/'inputs/closed-sequence-grammar-next22.json').read_text())
  self.encoding=json.loads((ROOT/'grammar/fine_encoding.json').read_text())
  self.sym=json.loads((BASE/'inputs/semantic-symbols.json').read_text())
  enc={v:k for k,v in self.sym.items()}
  self.original=''.join(enc[x] for x in self.source['flattened_semantic_words']['76'])
  self.fine=''.join(self.encoding['atom_expansions'][x] for x in self.original)
  self.asts={c:int(i) for i,c in self.encoding['fine_tokens'].items()}
  self.support={c:self.info(i)[0] for c,i in self.asts.items()}
  self.nohalt={c:not self.info(i)[1] for c,i in self.asts.items()}
  for c,i in self.asts.items():
   assert self.bounds(i)==(0,0), ('Nonclosed atom',c,i)
 @lru_cache(None)
 def info(self,i):
  row=self.source['ast_dag'][i]
  if row[0]=='L':
   op,*r=row[1]
   return (frozenset(r) if op in ('inc','dec') else frozenset(),op=='halt')
  a,b=self.info(row[1]),self.info(row[2])
  return a[0]|b[0],a[1] or b[1]
 @lru_cache(None)
 def bounds(self,i):
  row=self.source['ast_dag'][i]
  if row[0]=='L':
   op,*r=row[1]
   return (1 if op=='dec' else r[0] if op=='brk' else 0,r[0] if op=='cont' else 0)
  a,b=self.bounds(row[1]),self.bounds(row[2])
  return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0)
 def independent(self,a,b):
  return a!=b and self.nohalt[a] and self.nohalt[b] and not self.support[a]&self.support[b]
 def certificate(self,target):
  assert Counter(self.fine)==Counter(target)
  work=list(self.fine);moves=[];swaps=0
  for i,c in enumerate(target):
   j=work.index(c,i)
   if j>i:
    passed=''.join(work[i:j])
    assert all(self.independent(c,b) for b in passed),('dependent crossing',i,j,c,passed)
    moves.append([i,j,c,passed]);swaps+=j-i
    work.insert(i,work.pop(j))
  assert ''.join(work)==target
  return dict(status='PASS_CLOSED_DISJOINT_BLOCK_COMMUTATIONS',length=len(target),
              adjacent_swaps=swaps,moves=moves)
 def topo(self,rank):
  last={};succ=[[] for _ in self.fine];indeg=[0]*len(self.fine)
  for i,c in enumerate(self.fine):
   pred={last[r] for r in self.support[c] if r in last}
   # Unsupported/Halt blocks are barriers. AX has neither.
   assert self.support[c] and self.nohalt[c]
   for j in pred:succ[j].append(i);indeg[i]+=1
   for r in self.support[c]:last[r]=i
  ready=[i for i,n in enumerate(indeg) if not n];out=[];width=0
  while ready:
   width=max(width,len(ready))
   i=min(ready,key=lambda i:(rank[self.fine[i]],i));ready.remove(i);out.append(self.fine[i])
   for j in succ[i]:
    indeg[j]-=1
    if indeg[j]==0:ready.append(j)
  assert len(out)==len(self.fine)
  return ''.join(out),width

def main():
 p=argparse.ArgumentParser();p.add_argument('--count',type=int,default=256);p.add_argument('--output',type=Path,default=ROOT/'semantic/commuting_ax_variants.json');a=p.parse_args()
 C=Context();rng=random.Random(20261018244);letters=sorted(set(C.fine));variants={C.fine:dict(seed='identity',rank=None)}
 for seed in range(a.count):
  rank=letters.copy();rng.shuffle(rank)
  word,width=C.topo({c:i for i,c in enumerate(rank)})
  variants.setdefault(word,dict(seed=seed,rank=''.join(rank),maximum_ready_width=width))
 records=[]
 for i,(word,meta) in enumerate(variants.items()):
  records.append(dict(id=i,word=word,**meta,certificate=C.certificate(word)))
 result=dict(status='SOURCE_EQUIVALENCE_ONLY',original_AX_word=C.original,original_fine_AX=C.fine,
             source_reg_names=['N','T','W','A','D','H','X','Y','L'],
             fine_tokens={c:dict(ast=C.asts[c],support=sorted(C.support[c]),contains_halt=not C.nohalt[c]) for c in C.asts},
             attempted_ranks=a.count,distinct_words=len(records),variants=records)
 a.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(dict(status=result['status'],attempted_ranks=a.count,distinct_words=len(records),
     max_adjacent_swaps=max(x['certificate']['adjacent_swaps'] for x in records),
     output=str(a.output)),indent=2))
if __name__=='__main__':main()
