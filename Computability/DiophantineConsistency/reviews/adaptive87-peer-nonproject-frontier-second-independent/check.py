#!/usr/bin/env python3
"""Independently reconstruct recorded input-edge multiset and rehash objects."""
from pathlib import Path
from collections import defaultdict,Counter
import hashlib,json,re
HERE=Path(__file__).resolve().parent;R=HERE.parents[1]
TASK=R/'research/adaptive87-peer-nonproject-frontier'
PINS={'check.py':'990c4f0f8c09ab05e569592b367a8c935159f1135011d5476261a5398f005b64','pins.json':'1f4d916edeb6db8ae87940b2677a2be94654d7bcc8e2e06092b6b668621b410a','receipt.json':'d5872fe007e4c9663bc6f42a6c7888a0f3ed2a5a9876cca0e0ece2e4845430ad','README.md':'bc906420244adca2df69619c04c79d8fcae03a68296fb5f7d9e72fc9f897d19f'}
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
for n,h in PINS.items():assert sha(TASK/n)==h,n
for n,h in json.loads((TASK/'pins.json').read_text()).items():assert sha(Path(n) if n.startswith('/') else R/n)==h,n
load=lambda p:json.loads((Path(p) if str(p).startswith('/') else R/p).read_text())
prior=load('research/adaptive87-peer-recorded-producer-trace/receipt.json'); boundary=load('research/adaptive87-peer-boundary-producers/receipt.json'); result=load('research/adaptive87-peer-nonproject-frontier/receipt.json')
manifest=load('reviews/ipra-adaptive-native-fixed-continuation/manifest.json')
records={}
for label in ('prefix_records','second_prefix_records','third_prefix_records','fourth_prefix_records'):
 records[label]={(n,v['object_sha256']):v for n,v in manifest[label].items()}
for label,path in [('repaired-peer','reviews/ipra-current-repaired-build-verification/independent-state.json'),('fixed','reviews/ipra-adaptive-native-fixed-continuation-verification/author-state.json'),('ancestry-repair','/tmp/ipra-frozen-ancestry-repair-6ftdeyrq/state.json')]:
 z=load(path);assert z['status']=='PASS';records[label]={(v['name'],v['object_sha256']):v for v in z['records']}
for label,path in [('ha-author','reviews/ha87-isolated-full-author-pass/state.json'),('pra-author','/tmp/pra14-full-transitive-g3ull6n_/state.json')]:
 z=load(path);assert z['status']=='PASS';records[label]={(v['module'],v['object_sha256']):v for v in z['records']}
for label,path in [('rank17-direct-inputs-project-only','/tmp/ipra-rank17-native-n795r_ja/state.json'),('postmerge','/tmp/ipra-bounded-induction-postmerge-wgkld2w0/state.json'),('rebase','/tmp/ipra-bounded-induction-rebase-companions-p8ekt8vt/state.json')]:
 z=load(path);assert z['status']=='PASS';records[label]={}
 for v in z['records']:
  n=v['module'] if label=='rank17-direct-inputs-project-only' else v['name'].removeprefix('DiophantineConsistency.')
  records[label][('DiophantineConsistency.'+n,v['object_sha256'])]=v
selected=[]
for n,v in prior['seen'].items():
 if v['producer'] is not None:selected.append((n,v['producer'],v['sha256']))
owners={'/tmp/ipra-bounded-induction-postmerge-wgkld2w0':'postmerge','/tmp/ipra-bounded-induction-rebase-companions-p8ekt8vt':'rebase','/tmp/pra14-full-transitive-g3ull6n_':'pra-author'}
for n,v in boundary['nodes'].items():selected.append((n,owners[v['owner']],v['sha256']))
assert len(selected)==673 and len({n for n,_,_ in selected})==673
edges=Counter()
for n,label,h in selected:
 row=records[label][(n,h)]
 if 'direct_imports' in row:
  entries=[(name,v['sha256'],v['resolved_path'],False) for name,v in row['direct_imports'].items()]
 elif 'dependency_hashes' in row:
  mirror={'ha-author':'/tmp/ha87-full-transitive-p3xt6wra/package-lib','pra-author':'/tmp/pra14-full-transitive-g3ull6n_/package-lib'}[label]
  entries=[(name,v,str(Path(mirror)/Path(*name.split('.')).with_suffix('.olean')),True) for name,v in row['dependency_hashes'].items()]
 else:
  entries=[]
  for p,v in row['direct_inputs'].items():
   if not p.endswith('.olean'):continue
   m=re.search(r'/(Foundation|Mathlib|Lean)/(.*)\.olean$',p)
   if m:name=m.group(1)+'.'+m.group(2).replace('/','.')
   elif Path(p).name=='Init.olean':name='Init'
   else:continue
   entries.append((name,v['sha256'],v['realpath'],False))
 for name,h,p,inferred in entries:
  if name=='Init' or name.startswith(('Foundation.','Mathlib.','Lean.')):edges[(n,label,name,h,p,inferred)]+=1
reported=Counter((e['module'],e['producer'],e['input'],e['recorded_sha256'],e['producer_path']['path'],e['producer_path_inferred_from_historical_package_mirror']) for e in result['edges'])
assert edges==reported and sum(edges.values())==1204
byname=defaultdict(set);missing=[];inferred=Counter();cache={}
def observe(p):
 p=Path(p)
 if not p.is_file():return None
 real=str(p.resolve())
 if real not in cache:cache[real]=sha(real)
 return cache[real]
for (n,label,name,h,path,infer),count in edges.items():
 byname[name].add(h);cur=observe(path)
 if cur is None:missing.extend([(name,h,infer)]*count);inferred[infer]+=count
 else:assert cur==h,(name,path)
assert len(byname)==95 and all(len(v)==1 for v in byname.values()) and len(missing)==68
mirrors={'ha_package':Path('/tmp/ha87-full-transitive-p3xt6wra/package-lib'),
         'pra_package':Path('/tmp/pra14-full-transitive-g3ull6n_/package-lib'),
         'foundation_rebuild':Path('/tmp/foundation-rebuild-20261101/.lake/build/lib/lean')}
for edge in result['edges']:
    actual=observe(edge['producer_path']['path'])
    assert edge['recorded_path_matches']==(actual is not None and actual==edge['recorded_sha256'])
    for label,base in mirrors.items():
        p=base/Path(*edge['input'].split('.')).with_suffix('.olean');h=observe(p)
        want=None if h is None else {'resolved':str(p.resolve()),'sha256':h,'matches_recorded':h==edge['recorded_sha256']}
        assert edge['mirror_observations'][label]==want,(edge['input'],label)
summary=result['summary']
assert summary['source_row_count']==673 and summary['input_edge_count']==1204 and summary['unique_names']==95
assert summary['recorded_path_nonmatches']==68 and summary['multiple_recorded_hashes']=={}
assert len({n for n,_,_ in missing})==26 and all(n.startswith('Foundation.') for n,_,_ in missing)
alt=Path('/tmp/foundation-rebuild-20261101/.lake/build/lib/lean');alt_results={}
for name in sorted({n for n,_,_ in missing}):
 p=alt/Path(*name.split('.')).with_suffix('.olean');h=observe(p);old=next(iter(byname[name]));assert h is not None and h!=old
 alt_results[name]={'recorded_sha256':old,'alternate_sha256':h,'alternate_resolved':str(p.resolve())}
prior_names={n for n in prior['external_names']+boundary['external_names'] if n.startswith(('Foundation.','Mathlib.','Lean.'))}
assert len(prior_names)==94 and set(byname)==prior_names|{'Init'}
lean=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');rank=load('/tmp/ipra-rank17-native-n795r_ja/manifest.json')
assert sha(lean)==rank['lean_sha256']==manifest['lean_sha256']
print(json.dumps({'status':'PASS','reviewed_receipt_sha256':sha(TASK/'receipt.json'),'selected_producer_rows':len(selected),'direct_nonproject_edges':sum(edges.values()),'direct_edges_with_nonproject_inputs':len({(n,l) for n,l,_,_,_,_ in edges}),
 'unique_names':len(byname),'previous_frontier_names':len(prior_names),'inferred_missing_edges':inferred[True],'explicit_missing_edges':inferred[False],
 'missing_names_alternate_hashes':alt_results,'lean_sha256':sha(lean),'limits':['Read-only check of pinned producer records and their direct names only; does not reauthenticate predecessor traces.',
 'Inferred paths are reconstructed mirror paths, not paths recorded in producer rows.','Hash differences do not prove incompatibility, and matching direct hashes do not prove transitive provider coherence.',
 'No Lean process, builds, project/package/dynamic ancestry validation, or staging.']},sort_keys=True,indent=2))
