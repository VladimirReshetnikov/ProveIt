#!/usr/bin/env python3
"""Source-pinned, external dependency/liveness inventory; not a Lean theorem."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
recipe=D/'research/nine-seed38-jones-compact-macro-prototype/recipe.json'
q=D/'reviews/nine-seed38-jones-compact-lean-draft-frontier-independent'
prefix=D/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean'
for p,h in [(recipe,'779cd1d65dd84a4d5db6dd2072e94a7807b35394f5c245917b3688cc8ab2c090'),(q/'check.py','7af6a8fd7d31d55ddbf7383b85538d89f1c12ed357c556cfafe4d83b145fe4ca'),(q/'result.json','53a782182fc68652032d69a685e4d6520d366bbd03b55c9a26da01348cdefa94'),(prefix,'c2d995fcf0287325efcfbd060bed17eefd33a1b481a2b67a20978234614b00fa')]:
 if sha(p)!=h:raise RuntimeError(('pin',str(p)))
r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('source binding audit',r.returncode,r.stderr.decode(errors='replace')))
x=json.loads(recipe.read_text());nodes=x['nodes']
if not isinstance(nodes,list) or len(nodes)!=45 or x['inputs']!=9:raise RuntimeError('shape')
names=[n['name'] for n in nodes]
if len(set(names))!=len(names) or x['output']!=names[-1]:raise RuntimeError('names/output')
def references(v):
 if not isinstance(v,list):return set()
 if v and v[0]=='ref':
  if len(v)!=2 or not isinstance(v[1],str):raise RuntimeError('bad ref')
  return {v[1]}
 return set().union(*(references(y) for y in v))
consumers={n:[] for n in names};edges=[]
for j,node in enumerate(nodes,1):
 for name in sorted(references(node['expr'])):
  if name not in consumers or names.index(name)>=j-1:raise RuntimeError(('forward/missing ref',j,name))
  consumers[name].append(j);edges.append([name,j])
rows=[]
for i,name in enumerate(names,1):
 end=max(consumers[name],default=i);steps=max(0,end-i-1)
 rows.append({'name':name,'entry_index':i-1,'birth_prefix':i,'consumer_prefixes':consumers[name],'last_consumer_prefix':end,'one_snoc_steps_to_last_predecessor':steps})
print(json.dumps({'status':'PASS_EXTERNAL_INVENTORY','named_nodes':len(names),'distinct_reference_edges':len(edges),'one_snoc_steps_if_built_fresh_shared_per_entry':sum(r['one_snoc_steps_to_last_predecessor'] for r in rows),'rows':rows,'scope':'JSON-reference liveness for one possible shared per-entry carry chain; not a minimum, proof count, arithmetic operation count, exact degree, Lean theorem or verified JSON parser.'},indent=2,sort_keys=True))
