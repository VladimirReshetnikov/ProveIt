from pathlib import Path
from collections import defaultdict
from hashlib import sha256
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-corrected-lexical-inventory')
BASE=Path('research/ordinary13-fixed85-source-selection-plan/selection.json')
ROOT='IndependentKPositiveCorrectedComposition'
rootpath=Path('research/ordinary13-independent-k-positive-corrected-composition-draft/IndependentKPositiveCorrectedComposition.lean.src')
base=json.loads(BASE.read_text())['selected_modules']
idx=defaultdict(list)
for p in Path('research').rglob('*.lean*'):
 name=p.name[:-9] if p.name.endswith('.lean.src') else (p.name[:-5] if p.name.endswith('.lean') else None)
 if name:idx[name].append(str(p))
def digest(p):return sha256(Path(p).read_bytes()).hexdigest()
def imports(p):
 result=[]
 for line in Path(p).read_text().splitlines():
  m=re.match(r'^\s*(?:public\s+)?import\s+(.+?)\s*(?:--.*)?$',line)
  if m:result.extend(m.group(1).split())
 return result
selected={};ambiguities={};missing={};queue=[ROOT]
while queue:
 n=queue.pop()
 if n in selected or n in ambiguities or n in missing:continue
 if '.' in n:
  p=Path('Lean')/('/'.join(n.split('.'))+'.lean')
  candidates=[str(p)] if p.is_file() else []
 else:candidates=sorted(idx.get(n,[]))
 cand=[{'path':p,'sha256':digest(p)} for p in candidates]
 if n==ROOT:
  p=str(rootpath);kind='explicit root';assert p in candidates
 elif n in base:
  b=base[n];p=b['source_path']
  if not Path(p).is_file() or digest(p)!=b['sha256']:
   ambiguities[n]={'reason':'pinned baseline source unavailable or changed','candidates':cand,'baseline':b};continue
  kind='fixed85 JSON baseline'
 elif not candidates:
  missing[n]={'reason':'no local candidate found','imported_by':[]};continue
 elif len({x['sha256'] for x in cand})>1:
  ambiguities[n]={'reason':'multiple byte-distinct same-name candidates','candidates':cand};continue
 else:
  p=candidates[0];kind='single byte-equivalence class'
 # Record baseline decisions, including other observed candidate bytes.
 selected[n]={'path':p,'sha256':digest(p),'imports':imports(p),'selection_basis':kind,
  'observed_candidates':cand,'byte_distinct_observed_count':len({x['sha256'] for x in cand}),
  'baseline_alternative':bool(base[n]['alternative']) if n in base else False}
 queue.extend(selected[n]['imports'])
for n,d in selected.items():
 for dep in d['imports']:
  if dep in missing:missing[dep]['imported_by'].append(n)
  if dep in ambiguities:ambiguities[dep].setdefault('imported_by',[]).append(n)
for d in list(missing.values())+list(ambiguities.values()):
 if 'imported_by' in d:d['imported_by'].sort()
# A DFS is a lexical local graph property only; report instead of stopping at cycles.
state={};order=[];stack=[];cycles=[]
def visit(n):
 if state.get(n)==1:
  cycles.append(stack[stack.index(n):]+[n]);return
 if state.get(n)==2:return
 state[n]=1;stack.append(n)
 for m in selected[n]['imports']:
  if m in selected:visit(m)
 stack.pop();state[n]=2;order.append(n)
for n in sorted(selected):visit(n)
# Frontier observations: exact source paths under three known roots, plus
# the bounded historical review-copy pattern for the three BusyBeaver names.
# No observed source is promoted to a provider and traversal stops here.
observations={}
for n in sorted(missing):
 rel=Path('/'.join(n.split('.'))+'.lean')
 candidates=[]
 if n.startswith('Mathlib.'):
  candidates=[Path('../../.lake/packages/mathlib')/rel]
 elif n.startswith('Foundation.'):
  candidates=[Path('../../lib/FormalizedFormalLogic-Foundation')/rel]
 elif n.startswith('BusyBeaver.'):
  candidates=[Path('../../Computability/BusyBeaver/Lean')/rel]
  candidates+=sorted(Path('reviews').glob('*/sources/'+str(rel)))
 existing=[p for p in candidates if p.is_file()]
 observations[n]={'candidates':[{'path':str(p),'sha256':digest(p)} for p in existing],
  'byte_distinct_count':len({digest(p) for p in existing}),
  'scope':'Only named source roots and reviews/*/sources for BusyBeaver; imports and objects not followed.'}
print(json.dumps({'root':ROOT,'baseline_json_sha256':digest(BASE),'selected':selected,
 'ambiguous_frontier':ambiguities,'missing_frontier':missing,'frontier_source_observations':observations,'local_order':order,'cycles':cycles,
 'status':'Read-only, partial lexical JSON selection; unresolved imports cut traversal; no actual provider, olean, package, Lean, axiom or build validation.'},sort_keys=True,indent=2))
