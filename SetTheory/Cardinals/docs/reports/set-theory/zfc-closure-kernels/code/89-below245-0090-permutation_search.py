#!/usr/bin/env python3
"""Axiom-order search with oriented, rank-bounded dictionary parsing.

Only the eight independently closed AX rows are permuted. This is a source
search; changing the row order requires the separate selector theorem.
"""
import argparse,json,random,time
from pathlib import Path
from functools import lru_cache
from collections import defaultdict

P=argparse.ArgumentParser();P.add_argument('--package',type=Path,required=True)
P.add_argument('--parts',type=Path,required=True);P.add_argument('--output',type=Path,required=True)
P.add_argument('--trials',type=int,default=1200);P.add_argument('--seed',type=int,default=202610181)
A=P.parse_args();A.output.mkdir(parents=True,exist_ok=True);began=time.monotonic();rng=random.Random(A.seed)
d=json.loads((A.package/'grammar.json').read_text());g={w:(l,r)for w,l,r in d['rules']}
parts=json.loads(A.parts.read_text());oldroot=parts['prefix']+''.join(parts['rows'])+parts['tail'];assert oldroot in g
roots=set(d['roots'])|{r['word']for r in d['routes']};roots.remove(oldroot)
def closure(gram,rs):
 seen=set();stack=list(rs)
 while stack:
  w=stack.pop()
  if len(w)==1 or w in seen:continue
  seen.add(w);stack.extend(gram[w])
 return seen
base=closure(g,roots)
ss=json.loads((A.package/'inputs/closed-sequence-grammar-next22.json').read_text());symbols=json.loads((A.package/'inputs/semantic-symbols.json').read_text());enc={v:k for k,v in symbols.items()}
names={int(q):''.join(enc[x]for x in w)for q,w in ss['flattened_semantic_words'].items()}
byast={int(v):names[int(q)]for q,v in ss['sequence_ast_roots'].items()}
ls=(A.package/'inputs/semantic.txt').read_text().splitlines();n,nr,na=map(int,ls[0].split());allowed={c:int(m)for c,m in map(str.split,ls[n+1+nr:])}
old={w:(w[:int(k)],w[int(k):])for k,w,q in map(str.split,ls[1:n+1])}
def join(a,b):return(a[0]+1,max(a[0]+1,a[1],b[1]),max(a[2],b[2])+1)
@lru_cache(None)
def ep(i):
 if i in byast:return prop(byast[i])
 row=ss['ast_dag'][i]
 if row[0]=='L':return (0,0,0)
 return join(ep(row[1]),ep(row[2]))
@lru_cache(None)
def prop(w):
 if len(w)==1:return ep(ss['atoms'][symbols[w]]['ast'])
 return join(*(prop(x)for x in g.get(w,old.get(w))))
@lru_cache(None)
def deps(w):return frozenset(closure(g,[w]))
for w in g:prop(w)
patterns=defaultdict(list)
for w in [*g,*symbols]:
 if w!=oldroot:patterns[w[0]].append(w)
def legal(l,r):return(len(l)>1 or allowed[l]&1)and(len(r)>1 or allowed[r]&2)
def trial(target,alpha):
 cost=[float('inf')]*(len(target)+1);choice=[None]*len(target);cost[-1]=0
 weight={w:1+alpha*len(deps(w)-base)+(rng.random()-.5)*.08 for w in g if w!=oldroot}
 for i in range(len(target)-1,-1,-1):
  for w in patterns[target[i]]:
   j=i+len(w)
   if not target.startswith(w,i):continue
   v=cost[j]+weight.get(w,1)
   if v<cost[i]:cost[i]=v;choice[i]=w
 tokens=[];i=0
 while i<len(target):w=choice[i];tokens.append(w);i+=len(w)
 return assemble_tokens(tokens)
def assemble_tokens(tokens):
 target=''.join(tokens)
 N=len(tokens);offset=[0]
 for t in tokens:offset.append(offset[-1]+len(t))
 subword=lambda i,j:target[offset[i]:offset[j]]
 dp={};prods={}
 for width in range(1,N+1):
  for i in range(N-width+1):
   j=i+width;w=subword(i,j);opts={}
   if len(w)==1 or w in g:
    p=prop(w)
    if p[1]<=6 and p[2]<=64:opts[p[0]]=(0,p[2],None)
   for k in range(i+1,j):
    l=subword(i,k);r=subword(k,j)
    if not legal(l,r):continue
    for a,(ca,da,_)in dp.get((i,k),{}).items():
     if a+1>6:continue
     for b,(cb,db,_)in dp.get((k,j),{}).items():
      dep=max(da,db)+1
      if dep>64:continue
      val=(ca+cb+1,dep,(k,a,b))
      if a+1 not in opts or val[:2]<opts[a+1][:2]:opts[a+1]=val
   dp[i,j]=opts
 if not dp[0,N]:return None
 lead=min(dp[0,N],key=lambda l:dp[0,N][l][:2])
 ng=dict(g)
 def emit(i,j,l):
  w=subword(i,j);z=dp[i,j][l][2]
  if z is not None:
   k,a,b=z;left=emit(i,k,a);right=emit(k,j,b);ng[w]=(left,right)
  return w
 emit(0,N,lead)
 used=closure(ng,roots|{target});ng={w:ng[w]for w in used}
 return ng, len(tokens)

elite=tuple(range(8));best=len(g);history=[];orders=set();counts=defaultdict(int);top=[]
for k in range(A.trials):
 if k==0:order=elite
 elif k%5==0:order=tuple(rng.sample(range(8),8))
 else:
  order=list(elite);i,j=rng.sample(range(8),2);order[i],order[j]=order[j],order[i];order=tuple(order)
 orders.add(order);target=parts['prefix']+''.join(parts['rows'][i]for i in order)+parts['tail']
 result=trial(target,10**rng.uniform(-2,.1))
 if result is None:counts['unparseable']+=1;continue
 ng,nt=result;score=len(ng);counts[str(score)]+=1
 if score<=best+2:
  rec=dict(trial=k,rules=score,order=list(order),tokens=nt,seconds=time.monotonic()-began)
  candidate=dict(d);candidate.update(status='ABSTRACT_AXIOM_PERMUTATION_GRAMMAR_ONLY',rules_count=score,rules=[[w,*ng[w]]for w in sorted(ng)],roots=[target if w==oldroot else w for w in d['roots']],original_AX_word=oldroot,modified_AX_word=target,axiom_push_order=[8-i for i in order],search_method='oriented_dictionary_interval_dynamic_programming')
  candidate.pop('properties',None)
  if score<best:
   best=score;elite=order;history.append(rec);(A.output/'best.json').write_text(json.dumps(candidate,indent=2)+'\n');print('BEST',rec,flush=True)
  elif score==best and rng.random()<.3:elite=order
  if score<130 and target!=oldroot:(A.output/f'candidate_{k}_{score}.json').write_text(json.dumps(candidate,indent=2)+'\n')
 if k%20==0:print('progress',k,'best',best,'scores',dict(counts),'seconds',round(time.monotonic()-began,3),flush=True)
report=dict(status='BOUNDED_SOURCE_SEARCH',trials=A.trials,distinct_orders=len(orders),best_rules=best,histogram=dict(counts),history=history,seconds=time.monotonic()-began,seed=A.seed)
(A.output/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2),flush=True)
