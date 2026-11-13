#!/usr/bin/env python3
"""Independent recorded-edge reconstruction; no Lean, build, or provenance certification."""
import collections,hashlib,json,resource,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(55,55));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
r=Path(__file__).resolve().parents[2];d=Path(__file__).resolve().parent
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for b in iter(lambda:f.read(262144),b''):h.update(b)
 return h.hexdigest()
def require(v,m):
 if not v:raise RuntimeError(m)
pins=json.loads((d/'pins.json').read_text())
for p,want in pins.items():
 f=Path(p) if p.startswith('/') else r/p;require(sha(f)==want,'pin '+p)
def load(p):return json.loads((Path(p) if p.startswith('/') else r/p).read_text())
expected=load('research/adaptive87-peer-recorded-producer-trace/receipt.json');inventory=load('research/adaptive87-four-square-peer-provider-inventory/result.json')['objects'];manifest=load('reviews/ipra-adaptive-native-fixed-continuation/manifest.json')
# Insertion order is an explicit priority: repaired peer, ancestry repair,
# fixed continuation, four retained prefixes, HA author, rank-17 suffix.
records={};duplicates=collections.defaultdict(list)
def add(name,obj,label,deps,code):
 require(code==0,'failed record '+name);key=(name,obj);duplicates[key].append((label,deps));records.setdefault(key,(label,deps))
for label,file in [('repaired-peer','reviews/ipra-current-repaired-build-verification/independent-state.json'),('ancestry-repair','/tmp/ipra-frozen-ancestry-repair-6ftdeyrq/state.json'),('fixed','reviews/ipra-adaptive-native-fixed-continuation-verification/author-state.json')]:
 state=load(file);require(state['status']=='PASS','state '+label)
 for row in state['records']:add(row['name'],row['object_sha256'],label,{n:v['sha256'] for n,v in row['direct_imports'].items()},row['exit'])
for label in ['prefix_records','second_prefix_records','third_prefix_records','fourth_prefix_records']:
 for name,row in manifest[label].items():add(name,row['object_sha256'],label,{n:v['sha256'] for n,v in row['direct_imports'].items()},row['exit'])
h=load('reviews/ha87-isolated-full-author-pass/state.json');require(h['status']=='PASS','ha state')
for row in h['records']:add(row['module'],row['object_sha256'],'ha-author',row['dependency_hashes'],row['exit'])
h=load('/tmp/ipra-rank17-native-n795r_ja/state.json');require(h['status']=='PASS','rank17 state')
for row in h['records']:
 deps={}
 for name,val in row['direct_inputs'].items():
  if '/DiophantineConsistency/' in name and name.endswith('.olean'):deps['DiophantineConsistency.'+name.split('/DiophantineConsistency/',1)[1][:-6].replace('/','.')]=val['sha256']
 add('DiophantineConsistency.'+row['module'],row['object_sha256'],'rank17-direct-inputs-project-only',deps,row['exit'])
base=Path('/tmp/nine-ipra-guarded-peer-20261102-a/lib');cache={}
def obj(name):
 if name not in cache:
  f=base/Path(*name.split('.')).with_suffix('.olean')
  cache[name]=None if not f.is_file() else {'path':str(f.resolve()),'sha256':sha(f),'in_658':name in inventory}
 return cache[name]
roots=['DiophantineConsistency.HAAdaptiveFactor87','DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011','DiophantineConsistency.IPRAExpressionNative','DiophantineConsistency.HAExpressionSameZero','DiophantineConsistency.PRAPositiveCode'];seen={};missing=[];external=set();edges=[];todo=collections.deque(roots)
while todo:
 name=todo.popleft()
 if name in seen:continue
 x=obj(name);require(x is not None,'missing selected object '+name)
 if name in inventory:require((x['path'],x['sha256'])==(inventory[name]['resolved'],inventory[name]['object_sha256']),'selected inventory '+name)
 record=records.get((name,x['sha256']));seen[name]=dict(x,producer=record[0] if record else None)
 if record is None:missing.append(name);continue
 for dep,want in record[1].items():
  if not dep.startswith('DiophantineConsistency.'):external.add(dep);continue
  got=obj(dep);match=got is not None and got['sha256']==want
  edges.append((name,dep,want,None if got is None else got['sha256'],match))
  if match:todo.append(dep)
require(seen==expected['seen'],'selected objects or producer precedence')
require(len(edges)==expected['edge_count'] and len(edges)==1081,'edge count')
require([e for e in edges if not e[4]]==[] and expected['mismatches']==[],'edge mismatches')
require(sorted(missing)==expected['missing_record'] and len(missing)==40,'producer boundaries')
require(sorted(external)==expected['external_names'] and len(external)==111,'external frontier')
require(sorted(n for n,x in seen.items() if not x['in_658'])==expected['not_in_658'] and len(expected['not_in_658'])==27,'outside 658')
origins=load('reviews/ipra-frozen-repair-plan-v2-source-origin-audit/source-nodes.json');keys=set(origins)
matched=sorted(n for n,x in seen.items() if n+'|'+x['sha256']+'|'+x['path'] in keys)
require(matched==expected['source_origin_matches'] and len(matched)==380,'origin intersection')
require(sorted(n for n in missing if n in matched)==expected['frontier_source_origin_matches'] and len(missing)==40,'origin frontier intersection')
# Collect conflicting duplicate histories, without treating either record as actual provenance.
conflicts=[]
for name,x in seen.items():
 rows=duplicates[(name,x['sha256'])]
 if not rows:continue
 selected=rows[0][1]
 if any(deps!=selected for _,deps in rows[1:]):conflicts.append(name)
print(json.dumps({'scope':'recomputed bounded recorded edges and selected bytes; no producer authentication or Lean','pins_sha256':sha(d/'pins.json'),'selected_objects':len(seen),'matched_project_edges':len(edges),'mismatched_edges':0,'unrecorded_outgoing_boundaries':len(missing),'external_frontier':len(external),'outside_prior_658':len(expected['not_in_658']),'prior_origin_inventory_matches':len(matched),'frontier_origin_inventory_matches':len(missing),'selected_objects_with_differing_duplicate_records':sorted(conflicts)},sort_keys=True,indent=2))
