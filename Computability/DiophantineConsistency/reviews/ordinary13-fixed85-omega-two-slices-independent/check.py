from pathlib import Path
from hashlib import sha256
import json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-fixed85-omega-two-slices-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
names=('ordinary13-fixed85-model-omega-triage','ordinary13-fixed85-model-omega-triage-slice2');rs=[]
for name in names:
 A=Path('research')/name
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(A/'check.py')])==(A/'receipt.json').read_bytes()
 rs.append(json.loads((A/'receipt.json').read_text()))
assert [r['reviewed_module_count'] for r in rs]==[26,20]
assert [r['reviewed_omega_line_count'] for r in rs]==[63,83]
assert not(set(rs[0]['records'])&set(rs[1]['records']))
selection=Path('research/ordinary13-fixed85-source-selection-plan/selection.json');nodes=json.loads(selection.read_text())['selected_modules']
assert all(r['selection_sha256']==sha256(selection.read_bytes()).hexdigest() for r in rs)
for r in rs:
 count=0
 for n,item in r['records'].items():
  assert n in nodes and item['path']==nodes[n]['source_path'] and item['sha256']==nodes[n]['sha256']
  path=Path(item['path']);raw=path.read_bytes();assert sha256(raw).hexdigest()==item['sha256'];lines=raw.decode().splitlines()
  for hit in item['reviewed_sites']:
   assert lines[hit['line']-1].strip()==hit['text'] and re.search(r'\bomega\b',hit['text']);count+=1
 assert count==r['reviewed_omega_line_count']
# Independent representative context anchors, not goal-type inference.
anchors={
 'DiophantineConsistency.ModelArithmetic':['theorem exists_nat_of_lt (r : V) : ∀ n : ℕ','∃ m : ℕ, m < n'],
 'DiophantineConsistency.ArithmeticRunTrace':['obtain ⟨p, hp, rfl⟩ := standard_of_lt','∃ q, p = q + 1 := ⟨p - 1, by omega⟩'],
 'DiophantineConsistency.ArithmeticAdaptiveRankWindow2011':['private theorem two_power_bound (r n m : ℕ)','theorem current_bounds_nat'],
 'DiophantineConsistency.ArithmeticHome215':['{xs : List Seg} {i bound j : Nat}','(show j+1≤i+1 by omega)'],
 'DiophantineConsistency.ArithmeticControlFrame215':['(P : List Bool) (overflow : Bool) (extra : Nat)','change ¬(i.val+1=0 ∨ 4751<i.val+1); omega'],
 'DiophantineConsistency.Compact44.CompactRowComplete':['obtain ⟨m, hm, rfl⟩ := standard_of_lt','have hn : (tileN m).north < 439 := by omega'],
 'DiophantineConsistency.Compact44.CompactWordFieldCyclic':['(u : ℕ) (hu : u<8)','exact_mod_cast (show 1013+u<8807 by omega)']}
for n,needles in anchors.items():
 text=Path(nodes[n]['source_path']).read_text()
 for x in needles:assert x in text,(n,x)
print(json.dumps({'both_author_receipts_reproduce':True,'disjoint_module_sets':True,'site_counts':[63,83],'module_counts':[26,20],'every_selected_line_and_hash_checked':True,'representative_contexts_checked':len(anchors),'tactic_goal_inferred_by_lean':False,'lean_executed':False},sort_keys=True,indent=2))
