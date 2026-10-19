#!/usr/bin/env python3
"""Recognize exact draining-loop affine maps and check extra commutations.

Loop recognition checks the finite control cycle; the mathematical correctness
lemma is induction on the tested natural register, not sampled execution.
"""
from commutations import Context, ROOT, BASE
from pathlib import Path
from functools import lru_cache
import sys,json,collections
sys.path.insert(0,str(BASE/'reference/jeff/ZF/m254/tools/prog'))
import rmpath
C=Context()
@lru_cache(None)
def tree(i):
 row=C.source['ast_dag'][i]
 return ('L',tuple(row[1])) if row[0]=='L' else ('N',tree(row[1]),tree(row[2]))
def ident():return tuple(tuple(int(i==j) for j in range(10)) for i in range(10))
def mul(A,B):return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(10)) for j in range(10)) for i in range(10))
def linear(i):
 t=tree(i);A=[list(r) for r in ident()]
 if t[0]=='L':
  if t[1][0]!='inc':return None
  r=t[1][1];A[r][9]+=1
  return tuple(map(tuple,A)),dict(kind='increment',register=r)
 wrapper=('N',t,('L',('halt',)))
 first,P=rmpath.seg(wrapper,[])
 e,Q=rmpath.site(wrapper,P)
 if first or e[0]!='dec':return None
 r=e[1]
 try:
  pos,Qp=rmpath.seg(wrapper,rmpath.inc_path(Q),fuel=10000)
  neg,Qn=rmpath.seg(wrapper,rmpath.brk(1,Q),fuel=10000)
 except RuntimeError:return None
 ep,_=rmpath.site(wrapper,Qp);en,_=rmpath.site(wrapper,Qn)
 if ep!=e or en!=('halt',) or neg or r in pos:return None
 if rmpath.site(wrapper,Qn)[1]!=[True]:return None
 if C.info(i)[1]:return None
 # The positive path must return to exactly the same test, not merely a
 # syntactically equal test at a different location.
 if rmpath.site(wrapper,Qp)[1]!=Q:return None
 A[r]=[0]*10
 for j in pos:A[j][r]+=1
 return tuple(map(tuple,A)),dict(kind='draining_loop',register=r,increment_counts=list(rmpath.counts(pos)),
   initial_pointer=P,test_path=Q,positive_pointer=Qp,zero_pointer=Qn,zero_target='halt_sentinel')

maps={};cert={}
for c,i in C.asts.items():
 v=linear(i)
 if v:maps[c],cert[c]=v

@lru_cache(None)
def independent(a,b):
 if C.independent(a,b):return True
 return a!=b and a in maps and b in maps and mul(maps[a],maps[b])==mul(maps[b],maps[a])

def canonical(word):
 last={};succ=[[] for _ in word];indeg=[0]*len(word)
 for i,c in enumerate(word):
  pred={j for d,j in last.items() if not independent(c,d)}
  for j in pred:succ[j].append(i);indeg[i]+=1
  last[c]=i
 ready=[i for i,n in enumerate(indeg) if n==0];out=[]
 while ready:
  i=min(ready,key=lambda i:(word[i],i));ready.remove(i);out.append(word[i])
  for j in succ[i]:
   indeg[j]-=1
   if indeg[j]==0:ready.append(j)
 return ''.join(out)

if __name__=='__main__':
 letters=sorted(C.asts);pairs=[(a,b) for a in letters for b in letters if a<b and independent(a,b)]
 extra=[(a,b) for a,b in pairs if not C.independent(a,b)]
 G=json.loads((BASE/'grammar.json').read_text());E=C.encoding['atom_expansions'];classes=collections.defaultdict(list)
 for w,a,b in G['rules']:classes[canonical(''.join(E[c] for c in w))].append(['rule',w])
 for c,f in E.items():classes[canonical(f)].append(['atom',c])
 collisions=[v for v in classes.values() if len(v)>1]
 out=dict(status='EXACT_SOURCE_AFFINE_AND_COMMUTATION_CERTIFICATE',linear_atoms={c:dict(ast=C.asts[c],matrix=maps[c],control=cert[c]) for c in maps},
  independent_pairs=pairs,extra_affine_pairs=extra,collision_classes=collisions)
 (ROOT/'semantic/affine_commutations.json').write_text(json.dumps(out,indent=2)+'\n')
 print('LINEAR',list(maps),'PAIRS',len(pairs),'EXTRA',len(extra),'COLLISIONS',collisions)
 print('EXTRA',extra)
