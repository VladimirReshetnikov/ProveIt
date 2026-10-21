"""Own source-tree comparison; reads data only, no submitted code or machine run."""
from pathlib import Path
import json,hashlib,sys
sys.path.insert(0,'/tmp/k217-cc3-identity-padding')
import tree_reader as tr
R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
B=R/'Computability/BusyBeaver/Research/ZFC'
A=Path('/tmp/zfc-intake191/K218_Dominated_Rho8_2026-10-20/K218_Dominated_Rho8_2026-10-20')
O=Path(__file__).parent
paths={'baseline219':B/'candidate-k219/sites219.json','primary218':B/'candidate-k218/sites218.json','contextual218':B/'candidate-k218/alternatives/contextual/machine/sites218.json','dominated_reference':A/'source/dominated_zyx206.json','dominated_final':A/'source/sites218.json'}
trees={k:tr.parse(json.loads(p.read_text()))for k,p in paths.items()}
def at(t,p):
 for bit in p:t=t[int(bit)]
 return t
def occurrences(t):
 out={}
 def visit(n,p):
  out.setdefault(n,[]).append(p)
  if not tr.leaf(n):visit(n[0],p+'0');visit(n[1],p+'1')
 visit(t,'');return out
occ={k:occurrences(t)for k,t in trees.items()}
def metrics(t):
 rr=tr.rows(t);return dict(DAG=len(occurrences(t)),leaves=len(rr),depth=max(len(p)for p,_,_ in rr),zero_run=max(len(z)for p,_,_ in rr for z in p.split('1')))
comparison=json.loads((B/'candidate-k218/alternatives/contextual/comparison/comparison.json').read_text())
foldtypes=set(at(trees['primary218'],p)for p in comparison['roles']['K218']['85']['prefixes'])
assert len(foldtypes)==2
fold=[]
for t in sorted(foldtypes,key=repr):
 fold.append(dict(tree=t,leaves=len(tr.flat(t)),occurrences={k:dict(count=len(d.get(t,[])),end0=sum(p.endswith('0')for p in d.get(t,[])),end1=sum(p.endswith('1')for p in d.get(t,[])),prefixes=d.get(t,[]))for k,d in occ.items()}))
new52=at(trees['primary218'],comparison['roles']['K218']['188']['prefixes'][0])
a,(b,c)=new52;old52=((a,b),c)
assert [len(tr.flat(x))for x in (a,b,c)]==[26,19,7]
assert all(tr.boundary(x)==(0,0,False)for x in(a,b,c))
rotations=[]
def replace(t,old,new):return new if t==old else t if tr.leaf(t)else(replace(t[0],old,new),replace(t[1],old,new))
for k in ('dominated_reference','dominated_final'):
 for label,left,right in [('primary_fold_enabler',old52,new52),('reverse',new52,old52)]:
  t=trees[k];n=replace(t,left,right)
  assert tr.flat(t)==tr.flat(n)and tr.cfg(t)==tr.cfg(n)
  rotations.append(dict(source=k,direction=label,occurrences=len(occ[k].get(left,[])),metrics=metrics(n),whole_CFG_identical=True))
assert tr.flat(trees['dominated_reference'])==tr.flat(trees['dominated_final'])
assert tr.cfg(trees['dominated_reference'])==tr.cfg(trees['dominated_final'])
out=dict(status='OWN_LITERAL_SOURCE_COMPARISON_PASS',sources={k:dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),metrics=metrics(trees[k]))for k,p in paths.items()},same_dominated_reference_final_primitive_word_and_CFG=True,folded85_types=fold,closed52_rotation=rotations,scope='Literal source identities and complete source CFG only; no new physical allocation, startup, runtime, or fold proof. Counterfactual rotation costs do not assert a state saving.')
(O/'source-comparison.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(fold_occurrences=[{k:(x['count'],x['end0'],x['end1'])for k,x in f['occurrences'].items()}for f in fold],rotations=rotations)))
