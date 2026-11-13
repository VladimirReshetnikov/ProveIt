#!/usr/bin/env python3
"""Inspect recorded direct external inputs, without asserting a new LEAN_PATH."""
import hashlib,json
from collections import defaultdict
from pathlib import Path
R=Path(__file__).resolve().parents[2]; D=Path(__file__).resolve().parent
pins=json.loads((D/'pins.json').read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
for p,h in pins.items():
 q=Path(p) if p.startswith('/') else R/p
 assert sha(q)==h,p
prior=json.loads((R/'research/adaptive87-peer-recorded-producer-trace/receipt.json').read_text())
bound=json.loads((R/'research/adaptive87-peer-boundary-producers/receipt.json').read_text())
manifest=json.loads((R/'reviews/ipra-adaptive-native-fixed-continuation/manifest.json').read_text())
recordsets={}
for k in ['prefix_records','second_prefix_records','third_prefix_records','fourth_prefix_records']:
 recordsets[k]={(n,r['object_sha256']):r for n,r in manifest[k].items()}
for label,p in [('repaired-peer','reviews/ipra-current-repaired-build-verification/independent-state.json'),('fixed','reviews/ipra-adaptive-native-fixed-continuation-verification/author-state.json'),('ancestry-repair','/tmp/ipra-frozen-ancestry-repair-6ftdeyrq/state.json')]:
 q=Path(p) if p.startswith('/') else R/p;s=json.loads(q.read_text());assert s['status']=='PASS'
 recordsets[label]={(r['name'],r['object_sha256']):r for r in s['records']}
for label,p in [('ha-author','reviews/ha87-isolated-full-author-pass/state.json'),('pra-author','/tmp/pra14-full-transitive-g3ull6n_/state.json')]:
 s=json.loads((Path(p) if p.startswith('/') else R/p).read_text());assert s['status']=='PASS'
 recordsets[label]={(r['module'],r['object_sha256']):r for r in s['records']}
s=json.loads(Path('/tmp/ipra-rank17-native-n795r_ja/state.json').read_text());assert s['status']=='PASS'
recordsets['rank17-direct-inputs-project-only']={('DiophantineConsistency.'+r['module'],r['object_sha256']):r for r in s['records']}
for label,p in [('postmerge','/tmp/ipra-bounded-induction-postmerge-wgkld2w0/state.json'),('rebase','/tmp/ipra-bounded-induction-rebase-companions-p8ekt8vt/state.json')]:
 s=json.loads(Path(p).read_text());assert s['status']=='PASS'
 recordsets[label]={('DiophantineConsistency.'+r['name'].removeprefix('DiophantineConsistency.'),r['object_sha256']):r for r in s['records']}
owners={'/tmp/ipra-bounded-induction-postmerge-wgkld2w0':'postmerge','/tmp/ipra-bounded-induction-rebase-companions-p8ekt8vt':'rebase','/tmp/pra14-full-transitive-g3ull6n_':'pra-author'}
mirrors={'ha_package':'/tmp/ha87-full-transitive-p3xt6wra/package-lib','pra_package':'/tmp/pra14-full-transitive-g3ull6n_/package-lib','foundation_rebuild':'/tmp/foundation-rebuild-20261101/.lake/build/lib/lean'}
cache={}
def observe(path):
 if not path:return None
 p=Path(path)
 if not p.is_file():return {'path':path,'exists':False}
 if path not in cache:cache[path]={'path':path,'exists':True,'resolved':str(p.resolve()),'sha256':sha(p)}
 return cache[path]
def relevant(n):return n=='Init' or n.startswith(('Foundation.','Mathlib.','Lean.'))
def inputs(row,label):
 if 'direct_imports' in row:
  return [(n,v['sha256'],v['resolved_path']) for n,v in row['direct_imports'].items() if relevant(n)]
 if 'dependency_hashes' in row:
  base=mirrors['ha_package' if label=='ha-author' else 'pra_package']
  return [(n,h,str(Path(base)/(n.replace('.','/')+'.olean'))) for n,h in row['dependency_hashes'].items() if relevant(n)]
 # Rank-17 paths are captured directly, including Init; project edges were
 # considered separately by the previous trace.
 out=[]
 for path,v in row['direct_inputs'].items():
  if not path.endswith('.olean'):continue
  name=None
  for part in ('Foundation/','Mathlib/','Lean/'):
   if '/'+part in path:name=path.split('/'+part,1)[1];name=part+name;break
  if name is None and Path(path).name=='Init.olean':name='Init.olean'
  if name:out.append((name[:-6].replace('/','.'),v['sha256'],v['realpath']))
 return out
edges=[];found=set(); counts=defaultdict(int)
for n,v in prior['seen'].items():
 label=v['producer']
 if label is None:continue
 row=recordsets[label][(n,v['sha256'])];found.add(n);counts[label]+=1
 for name,h,path in inputs(row,label):edges.append((n,label,name,h,path))
for n,v in bound['nodes'].items():
 assert v is not None
 label=owners[v['owner']];row=recordsets[label][(n,v['sha256'])];found.add(n);counts[label]+=1
 for name,h,path in inputs(row,label):edges.append((n,label,name,h,path))
rows=[];byname=defaultdict(set)
for n,label,name,h,path in edges:
 recorded=observe(path);byname[name].add(h)
 comparisons={}
 for k,base in mirrors.items():
  obj=observe(str(Path(base)/(name.replace('.','/')+'.olean')))
  comparisons[k]=None if obj is None or not obj['exists'] else {'resolved':obj['resolved'],'sha256':obj['sha256'],'matches_recorded':obj['sha256']==h}
 rows.append({'module':n,'producer':label,'input':name,'recorded_sha256':h,'producer_path':recorded,'producer_path_inferred_from_historical_package_mirror':label in ('ha-author','pra-author'),'recorded_path_matches':bool(recorded and recorded['exists'] and recorded['sha256']==h),'mirror_observations':comparisons})
wanted={n for n in prior['external_names']+bound['external_names'] if n.startswith(('Foundation.','Mathlib.','Lean.'))}
assert wanted.issubset(byname), sorted(wanted-set(byname))
missing_names=sorted({x['input'] for x in rows if not x['recorded_path_matches']})
rank=json.loads(Path('/tmp/ipra-rank17-native-n795r_ja/manifest.json').read_text())
lean='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean';lean_obs=observe(lean)
assert rank['lean_sha256']==manifest['lean_sha256']
summary={'source_row_count':len(found),'previous_frontier_names_covered':len(wanted),'missing_input_names':missing_names,'input_edge_count':len(rows),'unique_names':len(byname),'multiple_recorded_hashes':{n:sorted(h) for n,h in byname.items() if len(h)>1},'recorded_path_nonmatches':sum(not x['recorded_path_matches'] for x in rows),'mirror_missing':{k:sum(x['mirror_observations'][k] is None for x in rows) for k in mirrors},'mirror_mismatches':{k:sum(x['mirror_observations'][k] is not None and not x['mirror_observations'][k]['matches_recorded'] for x in rows) for k in mirrors},'source_counts':dict(sorted(counts.items())),'lean_recorded_sha256':rank['lean_sha256'],'lean_current':lean_obs,'lean_current_matches':bool(lean_obs and lean_obs['exists'] and lean_obs['sha256']==rank['lean_sha256'])}
print(json.dumps({'summary':summary,'edges':rows,'scope':'selected recorded producer rows and direct Foundation/Mathlib/Lean/Init imports only; no selected future LEAN_PATH or package/dynamic/transitive closure asserted'},indent=2,sort_keys=True))
