from pathlib import Path
from hashlib import sha256
from collections import defaultdict,deque
import json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-fixed85-omega-hazards-draft')
pins=json.loads((D/'source-pins.json').read_text())
for p,h in pins.items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
subprocess.check_call([sys.executable,'-I','-S','-B',str(D/'generate.py'),'--check'])
m=json.loads(Path('research/ordinary13-fixed85-native-composition-draft/manifest.json').read_text())
nodes=m['local_modules'];rev=defaultdict(set)
for n,r in nodes.items():
 for dep in r['imports']:
  if dep in nodes:rev[dep].add(n)
dist={};q=deque([('Fixed85Endpoint',0)])
while q:
 n,d=q.popleft()
 if n in dist:continue
 dist[n]=d
 for dep in nodes[n]['imports']:
  if dep in nodes:q.append((dep,d+1))
names=['ResidueExactIndexModel','ResidueExactIndexWitness','Residue90CompactGraphGamma',
 'Residue90FirstNormGap','Residue90FyForce','Residue90GammaModel',
 'AQ17Forced105Arithmetic','ResidueRankLower']
records={}
for name in names:
 old=Path(nodes[name]['path']);new=D/(name+'Repaired.lean.src')
 a,b=old.read_text(),new.read_text()
 assert re.search(r'\bomega\b',a) and not re.search(r'\bomega\b',b)
 def headers(s):
  return [(kind,n,re.sub(r'\s+',' ',body.strip())) for kind,n,body in
   re.findall(r'(?ms)^\s*(theorem|lemma)\s+(\w+)(.*?)(?=\s*:=\s*(?:by|\n))',s)]
 assert headers(a)==headers(b),name
 assert re.findall(r'^namespace\s+([^\s]+)',a,re.M)==re.findall(r'^namespace\s+([^\s]+)',b,re.M)
 seen={name};queue=deque(seen)
 while queue:
  for x in rev[queue.popleft()]:
   if x not in seen:seen.add(x);queue.append(x)
 assert 'Fixed85Endpoint' in seen
 records[name]={'old':str(old),'old_sha256':sha256(old.read_bytes()).hexdigest(),
  'alternative':str(new),'alternative_sha256':sha256(new.read_bytes()).hexdigest(),
  'shortest_import_distance_from_fixed85':dist[name],
  'direct_consumers':sorted(rev[name]),'reverse_reachable_count':len(seen)}
# Aggregate lexical inventory is a triage list, not parsing or elaboration.
missing=[];research=[];other=[]
for name,r in sorted(nodes.items()):
 text=Path(r['path']).read_text()
 if re.search(r'^\s*import\s+Mathlib\.Tactic\.Omega\s*$',text,re.M):missing.append(name)
 lines=[i for i,line in enumerate(text.splitlines(),1) if re.search(r'\bomega\b',line)
        and not line.strip().startswith(('--','/','*'))]
 if lines:
  (research if r['path'].startswith('research/') else other).append((name,lines))
assert missing==['ResidueSignFreePower']
mathlib=Path('../../.lake/packages/mathlib')
assert (mathlib/'Mathlib').is_dir()
missing_mathlib=[n for n in m['external_frontier'] if n.startswith('Mathlib.') and
 not (mathlib/('/'.join(n.split('.'))+'.lean')).is_file()]
assert missing_mathlib==['Mathlib.Tactic.Omega'],missing_mathlib
assert all(n in dict(research) for n in names)
# Bounded pure-natural controls for all replacement patterns.
for F in range(1,20):
 for A in range(1,20):
  for q0 in range(F+A+1,F+A+5):
   assert q0>=3 and q0-1>=2 and q0-F>=2
   assert ((q0-1)*(q0-F)+A)*(q0*q0-1)>=40
for y in range(20):
 for q0 in range(1,20):assert y*y<1+q0*y*y
for R in range(20):
 for q0 in range(1,10):assert R+1<=R+q0**3+q0+1
print(json.dumps({'source_pins_sha256':sha256((D/'source-pins.json').read_bytes()).hexdigest(),
 'manifest_sha256':sha256(Path('research/ordinary13-fixed85-native-composition-draft/manifest.json').read_bytes()).hexdigest(),
 'repaired_alternatives':records,'missing_omega_import_modules':missing,'missing_observed_mathlib_frontier':missing_mathlib,
 'generator_sha256':sha256((D/'generate.py').read_bytes()).hexdigest(),
 'research_omega_lexical_hits':research,'other_local_omega_lexical_hit_module_count':len(other),
 'hazard_classification':'Research candidates use abstract V; other lexical hits require context and include legitimate Nat/Int omega.',
 'lean_executed':False,'status':'Unelaborated isolated source alternatives and lexical triage; not a proof or authenticated provider plan.'},sort_keys=True,indent=2))
