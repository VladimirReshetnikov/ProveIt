from pathlib import Path
from collections import Counter,defaultdict,deque
from hashlib import sha256
import difflib,json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-fixed85-omega-priority12-independent')
for path,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(path).read_bytes()).hexdigest()==h,path
P=Path('research/ordinary13-fixed85-omega-hazards-draft')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(P/'check.py')])==(P/'receipt.json').read_bytes()
m=json.loads(Path('research/ordinary13-fixed85-native-composition-draft/manifest.json').read_text());nodes=m['local_modules']
expected={'ResidueRankLower':Counter({'  have hq3 : (3:V)≤q := by omega':1,'  have hqm2 : (2:V)≤q-1 := by omega':1,'  have hqF2 : (2:V)≤q-F := by omega':1,'  have h5 : (5:V)≤(q-1)*(q-F)+alpha := by omega':1,'  have h8 : (8:V)≤q*q-1 := by omega':1}), 'ResidueExactIndexWitness':Counter({'  have hq3 : 3≤q p v := by omega':1}), 'ResidueExactIndexModel':Counter({'  have hq3 : 3≤q p v := by omega':1}), 'Residue90FyForce':Counter({'  dsimp only [c]\n  omega':1}), 'AQ17Forced105Arithmetic':Counter({'  omega':1,'    omega':1})}
rev=defaultdict(set)
for name,rec in nodes.items():
 for dep in rec['imports']:
  if dep in nodes:rev[dep].add(name)
counts={}
for name,want in expected.items():
 oldpath=Path(nodes[name]['path']);newpath=P/(name+'Repaired.lean.src');a=oldpath.read_text();b=newpath.read_text()
 assert sha256(oldpath.read_bytes()).hexdigest()==nodes[name]['sha256']
 old=a.splitlines();new=b.splitlines();ops=difflib.SequenceMatcher(a=old,b=new,autojunk=False).get_opcodes();seen=Counter();imports=0
 for kind,i,j,k,l in ops:
  if kind=='equal':continue
  oldchunk='\n'.join(old[i:j]);newchunk='\n'.join(new[k:l])
  if kind=='insert' and i==0:
   assert set(new[k:l])=={'import Mathlib.Tactic.NormNum','import Mathlib.Tactic.Ring'};imports+=1;continue
  assert kind=='replace' and oldchunk in want,(name,kind,oldchunk)
  assert 'omega' not in newchunk and newchunk.strip(),name
  seen[oldchunk]+=1
 assert seen==want and imports==1,(name,seen,want,imports)
 assert re.findall(r'^namespace\s+([^\s]+)',a,re.M)==re.findall(r'^namespace\s+([^\s]+)',b,re.M)
 assert not re.search(r'\bomega\b',b)
 queue=deque([name]);visited={name}
 while queue:
  for x in rev[queue.popleft()]:
   if x not in visited:visited.add(x);queue.append(x)
 assert 'Fixed85Endpoint' in visited
 counts[name]={'changed_omega_calls':sum(seen.values()),'direct_consumers':sorted(rev[name]),'lexical_reverse_closure':len(visited)}
# Anchors establish the arithmetic steps being reviewed, not elaboration.
rank=(P/'ResidueRankLowerRepaired.lean.src').read_text();fy=(P/'Residue90FyForceRepaired.lean.src').read_text();aq=(P/'AQ17Forced105ArithmeticRepaired.lean.src').read_text()
for t in ['add_le_add hF1 ha1','lt_of_le_of_lt h2 hgap','rw [hqminus]','lt_of_le_of_lt ha1 haF','add_le_add h4 ha1','rw [hq2minus]']:
 assert t in rank,t
for t in ['have he := pos_iff_one_le.mp','have hk\' := pos_iff_one_le.mp hyk','have hh := add_le_add he hk\'']:
 assert t in fy,t
for t in ['have hy : y*y≤q*(y*y)','lt_add_of_pos_left _ (by simp)','rw [←h] at hlt','simpa only [he] using hfour','not_lt_of_ge hbad']:
 assert t in aq,t
for name in ('ResidueExactIndexWitness','ResidueExactIndexModel'):
 s=(P/(name+'Repaired.lean.src')).read_text()
 assert 'add_le_add hF ha' in s and 'lt_of_le_of_lt h2 hgap' in s
print(json.dumps({'modules_reviewed':counts,'only_named_proof_blocks_and_imports_changed':True,'exact_source_level_namespaces_and_declarations_preserved':True,'author_receipt_reproduced':True,'provider_selection_performed':False,'lean_executed':False,'scope':'Five isolated alternatives only; arithmetic/source review, no elaboration, actual provider resolution, axiom or endpoint validation.'},sort_keys=True,indent=2))
