#!/usr/bin/env python3
"""Combine existing emitter/source rewrites and audit their literal compilation.

No machine below 196 states or PA consistency theorem is claimed. The two
source changes preserve their inherited mathematical proof obligations.
Derived source inputs and symbolic contracts retain their original notices.
Outputs go only to replayed/, leaving frozen evidence unchanged.
"""
from pathlib import Path
import sys,json,re,random,itertools,time,hashlib
BASE=Path(__file__).resolve().parent
DIST=BASE/'distributed_reference'
OUT=BASE/'replayed';OUT.mkdir(exist_ok=True)
sys.path.insert(0,str(BASE/'verification'))
import symbolic as s
import check as checks
import rebuild as rb
sys.path.insert(0,str(DIST))
import compiler as c
OLD=s.TREE
REPS,OCC=rb.decoder_map(s.rows,OLD)
NEG=s.NODES['x12']
SHORTNEG=(s.NODES['node37'],(('inc',1),s.NODES['node64']))
MP=s.NODES['node163'];SHORTMP=(s.NODES['node6'],s.NODES['node147'])
def freeze(x):return tuple(map(freeze,x))if isinstance(x,list)else x
def change(t,a,b):
 if t==a:return b
 if s.isleaf(t):return t
 return change(t[0],a,b),change(t[1],a,b)
def count(t,a):
 if t==a:return 1
 return 0 if s.isleaf(t)else count(t[0],a)+count(t[1],a)
def source_lean(path):
 old=s.NODES;s.NODES={}
 try:
  for line in path.read_text().splitlines():
   m=re.match(r'def (\w+) : Tree := (.*)',line)
   if m:s.NODES[m[1]]=s.parse_tree(m[2])
  return s.NODES['trie'] if 'trie'in s.NODES else s.NODES['node172']
 finally:s.NODES=old
DISTRIBUTED=source_lean(DIST/'Program.lean')
DIAGONAL=freeze(json.loads((BASE/'diagonal199/source.tree.json').read_text()))
def compile_tree(tree):
 # Each reused core node is at its original native reader. Context correctness
 # is not assumed here: all prospective final tables must pass s.validate.
 table={(q,b):v for(q,b),v in s.rows.items()if q<1300}
 states={q for q,b in table};mapped={n:min(qs&states) for n,qs in REPS.items()if qs&states}
 fresh=[];shape={}
 incq=min(REPS[(('inc',1),('inc',1))]);leafact={(('inc',1),b):s.rows[incq,b]for b in(0,1)}
 cp=min(REPS[s.NODES['x65']]);leafact[(('breakTo',1),1)]=s.rows[cp,1]
 # Preserve unchanged exterior, replacing AX and optionally MP in its parent.
 oldbody=s.NODES['x67']
 def body(t,p=()):
  if p==(1,0,1,0,1,0,0,1):return t
  if len(p)>=8:return None
  for b,z in enumerate(t):
   if not s.isleaf(z):
    a=body(z,p+(b,))
    if a is not None:return a
  return None
 ax=body(tree);assert ax is not None
 def get(n):
  if n in mapped:return mapped[n]
  assert not s.isleaf(n),n
  q=5000+len(fresh);fresh.append(n);mapped[n]=q;shape[q]=n
  for b,ch in enumerate(n):table[q,b]=leafact[ch,b]if s.isleaf(ch)else(b,'R',get(ch))
  return q
 table[101,1]=(1,'R',get(ax))
 if not count(tree,MP):table[164,1]=(1,'R',130)
 return rb.reachable(table),shape

def bools(M):return {k:(w,d=='R',n)for k,(w,d,n)in M.items()}
def strings(M):return {k:(w,'R'if d else'L',n)for k,(w,d,n)in M.items()}
def greedy(M,shape,seed):
 rand=random.Random(seed);folds=[];M=bools(M)
 shape={q:n for q,n in shape.items()if(q,0)in M}
 for z in range(15):
  ops=c.opportunities_fast(M,shape)
  if not ops:break
  rand.shuffle(ops)
  a,b,opts=ops[0];acts=[rand.choice(x)for x in opts]
  M=c.fold(M,a,b,acts);shape.pop(a,None)
  folds.append([a,b,acts]);
 return strings(M),folds

def save(name,M,tree,extra):
 p=OUT/name;p.mkdir(exist_ok=True)
 text=''.join(f'{q} {b} {w} {d} {n}\n'for(q,b),(w,d,n)in sorted(M.items()))
 (p/'machine.native.tm').write_text(text);(p/'source.tree.json').write_text(json.dumps(tree)+'\n')
 (p/'receipt.json').write_text(json.dumps(extra,indent=2)+'\n')
 labels=[74];seen={74}
 for q in labels:
  for bit in (0,1):
   n=M[q,bit][2]
   if n!=254 and n not in seen:seen.add(n);labels.append(n)
 assert seen=={q for q,bit in M}
 labels.append(254);ids={q:i for i,q in enumerate(labels)}
 dense=''.join(f'{ids[q]} {bit} {w} {d} {ids[n]}\n'for q in labels[:-1]for bit in(0,1)for w,d,n in[M[q,bit]])
 (p/'machine.tm').write_text(dense)
 (p/'dense_labels.json').write_text(json.dumps(labels)+'\n')

def main():
 results=[]
 for label,T in [('original',OLD),('distributed',DISTRIBUTED),('diagonal',DIAGONAL)]:
  for neg in [False,True]:
   for mp in [False,True]:
    name=label+('_neg'if neg else'')+('_mp'if mp else'')
    tree=change(T,NEG,SHORTNEG)if neg else T
    if mp:tree=change(tree,MP,SHORTMP)
    checks.set_tree(tree)
    M,shape=compile_tree(tree);best=M;bf=[];bs=-1;counts={}
    for seed in range(200):
     cand,folds=greedy(M,shape,seed);n=len(cand)//2;counts[n]=counts.get(n,0)+1
     if n<len(best)//2:best=cand;bf=folds;bs=seed
    checks.set_tree(tree)
    ok,detail=s.validate(best);steps=checks.startup(best)if ok else None
    res={'name':name,'negation_occurrences':count(T,NEG),'sites':len(s.SITES),'raw_states':len(M)//2,'best_states':len(best)//2,'folds':bf,'seed':bs,'counts':counts,'symbolic_ok':ok,'symbolic_detail':detail,'startup':steps}
    save(name,best,tree,res);results.append(res)
    print(json.dumps(res),flush=True)
 (OUT/'combined_receipts.json').write_text(json.dumps(results,indent=2)+'\n')
if __name__=='__main__':main()
