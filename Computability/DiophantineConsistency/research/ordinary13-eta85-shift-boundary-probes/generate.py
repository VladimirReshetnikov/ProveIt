from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-eta85-shift-boundary-probes')
p=Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json')
assert sha256(p.read_bytes()).hexdigest()=='97273735d1537b597544604d19969630c8464469e9a3ab2f8825f52dc602a648'
g=json.loads(p.read_text());assert len(g['source'])==85
for gate in ('F','alpha'):
 inp='n_'+gate
 assert [gate,'+',inp,1] in g['source']
 rows=[]
 for n,op,a,b in g['source']:
  if n==gate:continue
  rows.append([n,op,inp if a==gate else a,inp if b==gate else b])
 out={'name':'eta85-unshift-'+gate,'domain':g['domain'],'witnesses':g['witnesses'],
  'fixed_numerals':g['fixed_numerals'],'source':rows,'output':g['output'],
  'parent_sha256':sha256(p.read_bytes()).hexdigest(),
  'proof_status':'Exploratory candidate only; parent-to-child shift verified separately; zero-equivalence not established.'}
 (D/(gate+'-probe.json')).write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')
print(json.dumps({'parent_sha256':sha256(p.read_bytes()).hexdigest(),
 'probe_hashes':{n:sha256((D/(n+'-probe.json')).read_bytes()).hexdigest() for n in ('F','alpha')},
 'status':'Inert source-only probes; no zero-equivalence or Lean claim.'},sort_keys=True,indent=2))
