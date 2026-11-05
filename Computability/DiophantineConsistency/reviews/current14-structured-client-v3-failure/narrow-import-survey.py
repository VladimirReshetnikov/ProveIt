#!/usr/bin/env python3
"""Count affected project nodes under a hypothetical import change."""
import collections,hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent;TASK=HERE.parents[1];PLAN=TASK/'research/current14-printed-port-extension-plan'
BASE=Path('/tmp/current14-standard-fresh-source-20261104/manifest.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
rows={}
for fn in ('kernel-manifest.json','masks-manifest.json'):
 for n,r in read(PLAN/fn)['sources'].items():
  if n in rows and (rows[n]['sha256']!=r['sha256'] or rows[n]['imports']!=r['imports']):raise ValueError(('source conflict',n))
  rows[n]=r
base=set(read(BASE)['sources']);extra=set(rows)-base
if len(rows)!=84 or len(extra)!=61:raise ValueError('wrong source closure')
reverse=collections.defaultdict(set)
for n,r in rows.items():
 for d in r['imports']:
  if d in rows:reverse[d].add(n)
def descendants(starts):
 todo=collections.deque(starts);seen=set()
 while todo:
  n=todo.popleft()
  if n in seen:continue
  seen.add(n);todo.extend(reverse[n]-seen)
 return seen
seeds={n for n,r in rows.items() if 'Mathlib.Tactic' in r['imports']};wilson='Diophantine.Paper1976.Wilson'
if len(seeds)!=10 or not seeds<=extra or wilson not in extra:raise ValueError('unexpected imports')
results={'status':'SOURCE_GRAPH_SURVEY_ONLY','project_sources':len(rows),'base_shared':len(rows)-len(extra),'extra_sources':len(extra),
         'direct_tactic_modules':sorted(seeds),'tactic_descendants':sorted(descendants(seeds)),
         'wilson_module':wilson,'wilson_descendants':sorted(descendants([wilson])),
         'combined_descendants':sorted(descendants(seeds|{wilson})),
         'plan_sha256':{fn:sha(PLAN/fn) for fn in ('kernel-manifest.json','masks-manifest.json','result.json')},
         'base_manifest_sha256':sha(BASE),'script_sha256':sha(__file__),
         'scope':'Source-declared graph counts for hypothetical edits; no replacement imports, new proof, Lean build, or guarantee of minimal rebuild.'}
out=HERE/'narrow-import-survey.json'
with out.open('x') as f:json.dump(results,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps({'tactic_seeds':len(seeds),'tactic_descendants':len(results['tactic_descendants']),
                  'wilson_descendants':len(results['wilson_descendants']),'combined_descendants':len(results['combined_descendants'])},sort_keys=True))
