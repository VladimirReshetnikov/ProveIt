#!/usr/bin/env python3
"""Read-only pre-merge source graph plan for the bounded comparison."""
from pathlib import Path
import collections,graphlib,hashlib,json,re,subprocess
D=Path(__file__).resolve().parent;R=D.parents[3];base=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
old=json.loads((R/'Computability/DiophantineConsistency/reviews/ipra-bounded-induction-rebase-companions/manifest.json').read_text())
commit='a163bf0ad6'; repo='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'
changed=subprocess.check_output(['git','show','--format=','--name-only',commit],cwd=R,text=True).splitlines()
overrides={Path(p).stem:p for p in changed if p.startswith(repo) and p.endswith('.lean')}
assert len(set(overrides)&set(old['observed_sources']))==4,overrides
sha=lambda b:hashlib.sha256(b).hexdigest();texts={}
def read(n):
 if n not in texts:
  raw=subprocess.check_output(['git','show',commit+':'+overrides[n]],cwd=R) if n in overrides else (base/(n+'.lean')).read_bytes()
  texts[n]=raw.decode()
 return texts[n]
imports=lambda n:re.findall(r'^import\s+([\w.]+)',read(n),re.M)
seen=set()
def visit(n):
 if n in seen:return
 seen.add(n)
 for x in imports(n):
  if x.startswith('DiophantineConsistency.'):visit(x.split('.')[-1])
visit('IPRABoundedInductionChecks')
new={n:sha(read(n).encode()) for n in seen};additional=sorted(seen-set(old['observed_sources']))
changed_in_closure=sorted(n for n in seen if old['observed_sources'].get(n)!=new[n]);assert set(changed_in_closure)<=set(overrides),changed_in_closure
rev=collections.defaultdict(set)
for n in seen:
 for x in imports(n):
  if x.startswith('DiophantineConsistency.') and x.split('.')[-1] in seen:rev[x.split('.')[-1]].add(n)
affected=set(changed_in_closure);todo=list(affected)
while todo:
 for n in rev[todo.pop()]:
  if n not in affected:affected.add(n);todo.append(n)
graph={n:sorted({x.split('.')[-1] for x in imports(n) if x.startswith('DiophantineConsistency.')}&affected) for n in affected};order=list(graphlib.TopologicalSorter(graph).static_order())
external=sorted({x for n in affected for x in imports(n) if not x.startswith('DiophantineConsistency.')})
plan={'incoming_commit':commit,'guarded_sources_changed':overrides,'new_closure_count':len(seen),'pruned_sources':sorted(set(old['observed_sources'])-seen),'additional_sources':additional,'changed_in_closure':changed_in_closure,'affected_count':len(affected),'affected_order':order,'affected_direct_imports':{n:imports(n) for n in order},'external_direct_imports':external,'postmerge_source_sha256':new,'scope':'Prospective source-only plan made before merge using git blobs for changed local files. Parent object hashes and complete postmerge workspace verification are not yet available; this is not a Lean replay.'}
(D/'plan.json').write_text(json.dumps(plan,sort_keys=True,indent=2)+'\n')
print('changed',len(changed_in_closure),'new closure',len(seen),'pruned',len(plan['pruned_sources']),'affected',len(affected),'external',len(external))
print('changed:',', '.join(changed_in_closure));print('external:',', '.join(external))
