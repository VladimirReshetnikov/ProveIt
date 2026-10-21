"""Own exact source/row composition and data-only correctness guards; no full runtime."""
from pathlib import Path
import json,hashlib,sys,shutil
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');U=R/'Computability/BusyBeaver/Research/ZFC/k218-quantifier-stability/pricing';sys.path.insert(0,str(U))
import source_language as s,build221 as b
A=Path('/tmp/zfc-intake191/K218_Dominated_Rho8_2026-10-20/K218_Dominated_Rho8_2026-10-20');V=Path('/tmp/zfc-intake191/zfc-217-state-search/zfc-217-research');O=Path(__file__).parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())
oldrows=load(A/'source/sites218.json');old=s.tree(oldrows);T=b.read_table((A/'binary/machine/k218.native.tm').read_bytes());og,op=b.decoder_map(T,old)
base=s.tree(load(V/'baseline/sites218.json'));omit=s.tree(load(V/'variants/omit-zero/source.sites.json'))
assert omit==s.replace(base,'11111',s.subtree(base,'111111'))
assert s.subtree(old,'111111')==s.subtree(base,'11111')
parent='111111';deleted=parent+'0';promoted=parent+'1'
assert s.boundary(s.subtree(old,deleted))==(0,0,False)
assert s.boundary(s.subtree(old,promoted))==(0,0,False)
assert len(s.sites(s.subtree(old,deleted)))==19 and len(s.sites(s.subtree(old,promoted)))==7
assert op[164]==['11111']and T[164,1]==(1,1,98)and T[98,1]==(1,1,114)
new=s.replace(old,parent,s.subtree(old,promoted));newrows=s.sites(new);N=dict(T);N[164,1]=(1,1,114)
assert [k for k in T if T[k]!=N[k]]==[(164,1)]
ng,np=b.decoder_map(N,new)
oldstates={p:q for q,ps in op.items()for p in ps};newstates={p:q for q,ps in np.items()for p in ps}
for p,q in newstates.items():
 original=promoted+p[len(parent):]if p.startswith(parent)else p
 assert oldstates[original]==q,(p,q,original,oldstates[original])
# Every leaf still has exactly its old direct action at its corresponding parent state.
oldleaf={p:(op,arg)for p,op,arg in oldrows}
for p,op_,arg in newrows:
 original=promoted+p[len(parent):]if p.startswith(parent)else p
 assert oldleaf[original]==(op_,arg)
 assert N[newstates[p[:-1]],int(p[-1])]==T[oldstates[original[:-1]],int(original[-1])]
interval=[i for i,(p,_,_)in enumerate(oldrows)if p.startswith(deleted)];lo,hi=min(interval),max(interval)+1
assert interval==list(range(lo,hi))
assert [x[1:]for x in newrows]==[x[1:]for x in oldrows[:lo]+oldrows[hi:]]
graph0=s.graph_arithmetic(oldrows)[0];graph1=s.graph_arithmetic(newrows)[0]
assert graph0==s.graph_intervals(oldrows)and graph1==s.graph_intervals(newrows)
def redirect(i):
 if lo<=i<hi:
  assert i==lo,('nonentry deleted target',i)
  i=hi
 return i if i<lo else i-19
edge_count=0
for i,(effect,targets)in enumerate(graph0):
 if lo<=i<hi:continue
 j=i if i<lo else i-19
 assert graph1[j]==[effect,[redirect(t)for t in targets]],(i,j)
 edge_count+=len(targets)
# Exact successful first-entry blank trace is unchanged because the sole changed row is absent.
boot=load(Path('/tmp/zfc-intake191-source149-run1/results/runtime/startup.json'))
for q,h,rd,w,d,z in boot['trace']:
 assert N[q,rd]==(w,d,z)
assert not any((q,rd)==(164,1)for q,h,rd,w,d,z in boot['trace'])
reach={0};todo=[0]
for q in todo:
 for bit in(0,1):
  z=N[q,bit][2]
  if z!=254 and z not in reach:reach.add(z);todo.append(z)
assert reach=={q for q,_ in N}
(O/'candidate.native.tm').write_bytes(b.table_bytes(N));(O/'source.sites.json').write_bytes(s.compact(newrows))
report=dict(status='EXACT_DOMINATED_OMIT_ZERO_SOURCE_COMPOSITION_PASS',table_sha256=sha(O/'candidate.native.tm'),source_sha256=sha(O/'source.sites.json'),working_states=len(N)//2,rows=len(N),metrics=s.metrics(new),guarded_cases=sum(2 if op=='CD'else 1 for p,op,a in newrows),physical_patch=dict(row=[164,1],old=T[164,1],new=N[164,1],parent_occurrences=op[164]),source_edit=dict(parent=parent,deleted=deleted,promoted=promoted,deleted_ordinal_interval=[lo,hi],deleted_leaves=19,deleted_boundary=s.boundary(s.subtree(old,deleted))),whole_source_checks=dict(internal_nodes=len(newstates),all_leaf_actions_same_as_corresponding_prior_leaf=True,all_internal_prefix_paths_preserve_tape=True,two_independent_CFG_resolvers=True,retained_redirected_edges=edge_count),blank=dict(status='EXACT_PREVIOUS_TRACE_UNCHANGED',steps=boot['steps'],changed_row_absent=True,source_record='/tmp/zfc-intake191-source149-run1/results/runtime/startup.json',source_record_sha256=sha(Path('/tmp/zfc-intake191-source149-run1/results/runtime/startup.json'))),scope='Closed source deletion and exact decoder expansion, literal leaf actions, redirected full source CFG, and prior blank trace reuse. Ordinary compiler cleanup transfer is stated separately. This is not a full runtime proof for the shortened source or an accepted <=217 machine.',inputs={str(p):sha(p)for p in[Path(__file__),U/'source_language.py',U/'build221.py',A/'source/sites218.json',A/'binary/machine/k218.native.tm',V/'baseline/sites218.json',V/'variants/omit-zero/source.sites.json']})
(O/'composition.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
