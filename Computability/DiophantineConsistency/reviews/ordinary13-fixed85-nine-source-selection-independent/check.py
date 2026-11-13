from pathlib import Path
from hashlib import sha256
from collections import defaultdict,deque
import json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-fixed85-nine-source-selection-independent');A=Path('research/ordinary13-fixed85-source-selection-plan')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(A/'check.py')])==(A/'receipt.json').read_bytes()
s=json.loads((A/'selection.json').read_text());m=json.loads(Path('research/ordinary13-fixed85-native-composition-draft/manifest.json').read_text()); selected=s['selected_modules'];base=m['local_modules']
intended={'ResidueSignFreePower','ResidueRankLower','ResidueExactIndexWitness','ResidueExactIndexModel','Residue90FyForce','AQ17Forced105Arithmetic','Residue90FirstNormGap','Residue90CompactGraphGamma','Residue90GammaModel'}
assert set(s['local_alternatives'])==intended=={n for n,r in selected.items() if r['alternative']}
haz=json.loads(Path('research/ordinary13-fixed85-omega-hazards-draft/receipt.json').read_text());sign=json.loads(Path('research/ordinary13-signfree-omega-repair-draft/receipt.json').read_text())
assert set(haz['repaired_alternatives'])==intended-{'ResidueSignFreePower'}
assert set(selected)==set(base) and len(selected)==1354
for n,e in selected.items():
 p=Path(e['source_path']); data=p.read_bytes();assert sha256(data).hexdigest()==e['sha256']
 imports=[]
 for line in data.decode().splitlines():
  mm=re.match(r'^\s*(?:public\s+)?import\s+(.+?)\s*(?:--.*)?$',line)
  if mm:imports.extend(mm.group(1).split())
 assert imports==e['imports'],n
 assert e['virtual_logical_path']=='/'.join(n.split('.'))+'.lean'
 if n not in intended:
  assert (e['source_path'],e['sha256'],e['imports'])==(base[n]['path'],base[n]['sha256'],base[n]['imports']),n
 else:
  alt=s['local_alternatives'][n]
  assert alt['previous_path']==base[n]['path'] and alt['previous_sha256']==base[n]['sha256']
  assert alt['alternative_path']==e['source_path'] and alt['alternative_sha256']==e['sha256']
  if n!='ResidueSignFreePower':
   assert e['source_path']==haz['repaired_alternatives'][n]['alternative']
   assert e['sha256']==haz['repaired_alternatives'][n]['alternative_sha256']
  else:
   assert e['source_path']=='research/ordinary13-signfree-omega-repair-draft/ResidueSignFreePowerRepaired.lean.src'
   assert e['sha256']==sign['sha256'][e['source_path']]
  assert re.findall(r'^namespace\s+(.+)$',Path(base[n]['path']).read_text(),re.M)==re.findall(r'^namespace\s+(.+)$',data.decode(),re.M)
assert len({e['virtual_logical_path'] for e in selected.values()})==len(selected)
assert len({e['source_path'] for e in selected.values()})==len(selected)
seen=set();front=set();q=deque([s['root']]);rev=defaultdict(set)
while q:
 n=q.popleft()
 if n in seen or n in front:continue
 if n not in selected:front.add(n);continue
 seen.add(n);q.extend(selected[n]['imports'])
assert seen==set(selected) and front==set(s['external_frontier']) and len(front)==93
assert set(m['external_frontier'])-front=={'Mathlib.Tactic.Omega'} and not front-set(m['external_frontier'])
order=s['dependency_first_order'];pos={n:i for i,n in enumerate(order)}
assert len(pos)==len(order)==len(selected)
for n,e in selected.items():
 for dep in e['imports']:
  if dep in selected:
   assert pos[dep]<pos[n],(n,dep);rev[dep].add(n)
affected=set(intended);q=deque(intended)
while q:
 for n in rev[q.popleft()]:
  if n not in affected:affected.add(n);q.append(n)
assert len(affected)==s['reverse_affected_local_count']==55
assert s['reverse_affected_order']==[n for n in order if n in affected] and s['root'] in affected
print(json.dumps({'author_receipt_reproduces':True,'nine_exact_logical_to_source_mappings_checked':True,'all_selected_source_hashes_and_imports_checked':len(selected),'unique_virtual_logical_paths':True,'recomputed_frontier_names':len(front),'recomputed_reverse_affected_local_count':len(affected),'external_files_or_objects_checked':False,'lean_executed':False},sort_keys=True,indent=2))
