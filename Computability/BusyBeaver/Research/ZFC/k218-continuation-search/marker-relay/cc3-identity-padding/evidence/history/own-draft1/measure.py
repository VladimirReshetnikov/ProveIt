"""Own fixed identity-padding family; source data/contracted CFG only."""
from pathlib import Path
import json,hashlib
import tree_reader as tr
R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
O=Path(__file__).parent
S=R/'Computability/BusyBeaver/Research/ZFC/candidate-k218/sites218.json'
oldrows=json.loads(S.read_text());tree=tr.parse(oldrows);oldcfg=tr.cfg(tree)
P=(('CD',6),('CC',2))
def nodes(t):
 seen=set()
 def walk(x):
  if x in seen:return
  seen.add(x)
  if not tr.leaf(x):walk(x[0]);walk(x[1])
 walk(t);return seen
def metrics(t):
 rs=tr.rows(t)
 return {'dag_nodes':len(nodes(t)),'leaves':len(rs),'depth':max(len(p)for p,_,_in rs),'zero_run':max(len(z)for p,_,_in rs for z in p.split('1'))}
results=[]
for r in range(9):
 entry={};actual={};extra=[];oi=0;ni=0
 def convert(t):
  global oi,ni
  if t==P:
   entry[oi]=ni;actual[oi]=ni+2;entry[oi+1]=ni+3;actual[oi+1]=ni+3
   extra.append((ni,r));oi+=2;ni+=4
   return ((('CI',r),('CD',r)),(('CD',6),('CC',3)))
  if tr.leaf(t):entry[oi]=ni;actual[oi]=ni;oi+=1;ni+=1;return t
  return convert(t[0]),convert(t[1])
 new=convert(tree);newrows=tr.rows(new);nc=tr.cfg(new)
 assert oi==4744 and ni==4762 and len(extra)==9
 for i,(effect,targets)in enumerate(oldcfg):
  j=actual[i]
  assert nc[j][0]==effect,(i,j)
  assert nc[j][1]==[entry[k]for k in targets],(i,j,targets,nc[j])
 for j,r1 in extra:
  assert nc[j]==[['increment',r1],[j+1]]
  assert nc[j+1][0]==['decrement',r1]and nc[j+1][1][1]==j+2
  # Its zero branch is impossible after the immediately preceding increment.
 p=O/f'pad-r{r}.sites.json';p.write_text(json.dumps(newrows,separators=(',',':'))+'\n')
 m=metrics(new);remaining=sum(t==P for t in nodes(new));assert remaining==0
 results.append({'name':f'pad-r{r}','register':r,'source':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'metrics':m,'added_neutral_pairs':len(extra),'contracted_full_CFG':True,'remaining_CD6_CC2_types':remaining})
# The already proved comparator-only register conjugation is a separate source option.
hits=json.loads((R/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/140-k219-res-enc-eq_clean_hits.json').read_text())
def freeze(x):return tuple(map(freeze,x))if isinstance(x,list)else x
E=freeze(hits[10]);changed=[]
def swapped(x):
 if tr.leaf(x):
  op,a=x;return(op,11-a)if op in('CI','CD')and a in(5,6)else x
 return swapped(x[0]),swapped(x[1])
def replace(x,p=''):
 if x==E:changed.append(p);return swapped(x)
 return x if tr.leaf(x)else(replace(x[0],p+'0'),replace(x[1],p+'1'))
swap=replace(tree);assert len(changed)==4
p=O/'swap-equality56.sites.json';p.write_text(json.dumps(tr.rows(swap),separators=(',',':'))+'\n')
# Eight late pairs disappear; the root pair survives, so this is not a total P elimination.
count=sum(1 for p0,op,a in tr.rows(swap)if op=='CC'and a==2 and p0.endswith('1')and [p0[:-1]+'0','CD',6]in tr.rows(swap))
assert count==1
results.append({'name':'swap-equality56','source':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'metrics':metrics(swap),'replaced_equality_macros':4,'remaining_CD6_CC2_occurrences':count,'contract':'Conjugate proved clean equality by register5/6 permutation; equality symmetric, both outputs zero.'})
res={'status':'TEN_FIXED_SOURCE_OPTIONS_MEASURED_NO_COMPILER','baseline':{'source':str(S),'sha256':hashlib.sha256(S.read_bytes()).hexdigest(),'metrics':metrics(tree)},'options':results,'scope':'All-natural source contracts plus literal source costs; no allocator, table, startup, runtime, generic-entry contract or state-count claim.','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(O/'result.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({'baseline':res['baseline']['metrics'],'options':[(x['name'],x['metrics'])for x in results]}))
