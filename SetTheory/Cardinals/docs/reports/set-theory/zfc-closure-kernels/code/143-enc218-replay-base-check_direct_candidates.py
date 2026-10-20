#!/usr/bin/env python3
"""Independent all-natural contract review support and literal candidate audit.
Owned AST evaluator and diagnostics; no received executable imports.
"""
import collections,hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent;ROOT=D.parent
basepath=ROOT/'latest219_baseline/candidate-k219/sites219.json';SS=json.loads(basepath.read_text())
def freeze(t):return tuple(map(freeze,t)) if isinstance(t,list) else t
def leaf(t):return isinstance(t[0],str)
def tree(ss):
 by={p:(op,n) for p,op,n in ss}
 def go(p=''):return by[p] if p in by else (go(p+'0'),go(p+'1'))
 return go()
def flat(t,p=''):return [(p,*t)] if leaf(t) else flat(t[0],p+'0')+flat(t[1],p+'1')
def uniq(t):return {t} if leaf(t) else {t}|uniq(t[0])|uniq(t[1])
def replace(t,target,new,p=''):
 if t==target:return new,[p]
 if leaf(t):return t,[]
 a,pa=replace(t[0],target,new,p+'0');b,pb=replace(t[1],target,new,p+'1')
 return (a,b),pa+pb
def calc(t,reg):
 reg=list(reg);steps=0
 def go(t):
  nonlocal steps
  if leaf(t):
   op,n=t;steps+=1
   if op=='CI':reg[n]+=1;return 'N',0
   if op=='CD':
    if reg[n]:reg[n]-=1;return 'N',0
    return 'B',1
   return op[1],n
  while True:
   k,n=go(t[0])
   if k=='B':return ('N',0) if n==1 else ('B',n-1)
   if k=='C':return k,n
   k,n=go(t[1])
   if k=='C' and n==1:continue
   return (k,n-1) if k=='C' else (k,n)
 return go(t),reg,steps
D5=('CD',5);D6=('CD',6);I5=('CI',5);I6=('CI',6);C1=('CC',1);C2=('CC',2);B1=('CB',1)
P=D6,C2;U=P,B1;A=D5,U;L=A,D6;Z=D5,C1;R=Z,U;E=L,R
Q=D5,(I6,C2);E09=L,(Q,U);L13=A,(I5,A);E13=L13,R
baseline=tree(SS);assert E==freeze(json.loads((ROOT/'latest219_baseline/candidate-k219/new_equality_macro.json').read_text()))
base_sides={(op,n,p[-1]) for p,op,n in SS};reports=[]
for name,macro in [('09',E09),('13',E13)]:
 p=ROOT/f'research218_source/direct_equality_{name}_sites.json';source=json.loads(p.read_text());rebuilt,paths=replace(baseline,E,macro)
 assert len(paths)==4 and [list(row) for row in flat(rebuilt)]==source
 assert tree(source)==rebuilt
 new_sides={(op,n,p[-1]) for p,op,n in source}-base_sides;assert not new_sides
 pairs=0;maximum_steps=0
 for a in range(101):
  for b in range(101):
   reg=[7,19,23,11,29,a,b,31,13];sig,out,n=calc(macro,reg)
   assert sig==(('N',0) if a==b else ('B',1)) and out[5:7]==[0,0]
   assert all(out[i]==reg[i] for i in range(9) if i not in [5,6])
   if name=='13':
    x,rx,_=calc(L13,reg);y,ry,_=calc(L,reg);assert (x,rx)==(y,ry)
   pairs+=1;maximum_steps=max(maximum_steps,n)
 large=[(0,100000),(100000,0),(10000,10000),(10000,9999),(9999,10000)]
 for a,b in large:
  reg=[13]*9;reg[5:7]=[a,b];sig,out,n=calc(macro,reg)
  assert sig==(('N',0) if a==b else ('B',1)) and out[5:7]==[0,0]
  assert all(out[i]==13 for i in range(9) if i not in [5,6])
 reports.append({'name':'direct'+name,'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'macro':macro,'replacements':paths,'distinct_nodes':len(uniq(rebuilt)),'leaves':len(source),'maximum_depth':max(len(p) for p,op,n in source),'new_primitive_child_sides':list(new_sides),'right_CD_count':sum(op=='CD' and p[-1]=='1' for p,op,n in source),'right_CI6_count':sum(op=='CI' and n==6 and p[-1]=='1' for p,op,n in source),'finite_diagnostic_pairs':pairs,'large_diagnostic_pairs':large,'scope':'All-natural theorem separately proved inDIRECT_CONTRACT_PROOFS.md; finite diagnostics not promoted to proof; no binary table correctness assertion'})
result={'status':'TWO_LITERAL_CANDIDATES_AND_DIAGNOSTICS_PASS','baseline_sha256':hashlib.sha256(basepath.read_bytes()).hexdigest(),'candidates':reports}
(D/'DIRECT_CANDIDATE_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
