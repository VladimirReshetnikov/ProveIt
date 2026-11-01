#!/usr/bin/env python3
"""Read-only actual merged-source graph plan for bounded comparison."""
from pathlib import Path
import collections,graphlib,hashlib,json,re,subprocess
D=Path(__file__).resolve().parent;R=D.parents[3];base=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
old=json.loads((R/'Computability/DiophantineConsistency/reviews/ipra-bounded-induction-rebase-companions/manifest.json').read_text())
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip();sha=lambda b:hashlib.sha256(b).hexdigest();texts={}
def read(n):
 if n not in texts:texts[n]=(base/(n+'.lean')).read_text()
 return texts[n]
imports=lambda n:re.findall(r'^import\s+([\w.]+)',read(n),re.M)
seen=set()
def visit(n):
 if n in seen:return
 seen.add(n)
 for x in imports(n):
  if x.startswith('DiophantineConsistency.'):visit(x.split('.')[-1])
visit('IPRABoundedInductionChecks')
new={n:sha(read(n).encode()) for n in seen};additional=sorted(seen-set(old['observed_sources']));changed_in_closure=sorted(n for n in seen if old['observed_sources'].get(n)!=new[n]);rev=collections.defaultdict(set)
for n in seen:
 for x in imports(n):
  if x.startswith('DiophantineConsistency.') and x.split('.')[-1] in seen:rev[x.split('.')[-1]].add(n)
affected=set(changed_in_closure);todo=list(affected)
while todo:
 for n in rev[todo.pop()]:
  if n not in affected:affected.add(n);todo.append(n)
graph={n:sorted({x.split('.')[-1] for x in imports(n) if x.startswith('DiophantineConsistency.')}&affected) for n in affected};order=list(graphlib.TopologicalSorter(graph).static_order());external=sorted({x for n in affected for x in imports(n) if not x.startswith('DiophantineConsistency.')})
assert head==subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
assert all(sha((base/(n+'.lean')).read_bytes())==x for n,x in new.items())
plan={'merged_head':head,'new_closure_count':len(seen),'pruned_sources':sorted(set(old['observed_sources'])-seen),'additional_sources':additional,'changed_in_closure':changed_in_closure,'affected_count':len(affected),'affected_order':order,'affected_direct_imports':{n:imports(n) for n in order},'external_direct_imports':external,'postmerge_source_sha256':new,'scope':'Read-only actual merged-workspace source graph; full source hashes checked before and after. This is not a Lean replay or authentication of inherited objects.'}
(D/'plan.json').write_text(json.dumps(plan,sort_keys=True,indent=2)+'\n')
print('HEAD',head,'changed',len(changed_in_closure),'new closure',len(seen),'pruned',len(plan['pruned_sources']),'affected',len(affected),'external',len(external))
print('changed:',', '.join(changed_in_closure));print('external:',', '.join(external))
