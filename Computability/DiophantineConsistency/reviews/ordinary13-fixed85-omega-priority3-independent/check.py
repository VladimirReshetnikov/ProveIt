from pathlib import Path
from hashlib import sha256
from collections import defaultdict,deque
import json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-fixed85-omega-priority3-independent');A=Path('research/ordinary13-fixed85-omega-hazards-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(A/'check.py')])==(A/'receipt.json').read_bytes()
rec=json.loads((A/'receipt.json').read_text());manifest=json.loads(Path('research/ordinary13-fixed85-native-composition-draft/manifest.json').read_text());nodes=manifest['local_modules'];rev=defaultdict(set)
for n,e in nodes.items():
 for dep in e['imports']:
  if dep in nodes:rev[dep].add(n)
fix={
'Residue90FirstNormGap':('''  have hk2 : (2:V)≤k v := by
    have h9 := Arithmetic.zero_le (v 9)
    have h10 := Arithmetic.zero_le (v 10)
    dsimp only [k]
    omega''','''  have hk2 : (2:V)≤k v := by
    have h9 : (1:V)≤v 9+1 := by simp
    have h10 : (1:V)≤v 10+1 := by simp
    have hh := add_le_add h9 h10
    simpa only [k,show (1:V)+1=2 by ring] using hh'''),
'Residue90CompactGraphGamma':('''  have hq2 : 2≤q p v := by
    have h := pos_iff_one_le.mp hb
    dsimp [q]
    omega''','''  have hq2 : 2≤q p v := by
    have hh := add_le_add_left (pos_iff_one_le.mp hb) (1:V)
    simpa only [q,show (1:V)+1=2 by ring] using hh'''),
'Residue90GammaModel':('''      have hq3nonneg := Arithmetic.zero_le (q^3)
      have hqnonneg := Arithmetic.zero_le q
      omega''','''      have h : R≤R+(q^3+q) := le_add_of_nonneg_right (Arithmetic.zero_le (q^3+q))
      have hh := add_le_add_right h (1:V)
      simpa only [add_assoc] using hh''')}
closures={}
for name,(oldblock,newblock) in fix.items():
 meta=rec['repaired_alternatives'][name];old=Path(meta['old']).read_text();new=Path(meta['alternative']).read_text()
 assert old.count(oldblock)==1;expected=old.replace(oldblock,newblock)
 for imp in ('Mathlib.Tactic.NormNum','Mathlib.Tactic.Ring'):
  line='import '+imp+'\n'
  if line not in expected:expected=line+expected
 assert new==expected,name
 assert not re.search(r'\bomega\b',new,re.I)
 assert re.findall(r'^namespace\s+(.+)$',old,re.M)==re.findall(r'^namespace\s+(.+)$',new,re.M)
 sig=lambda s:re.findall(r'(?ms)^(?:private\s+)?(?:theorem|lemma)\s+.*?(?=:=\s*by)',s)
 assert sig(old)==sig(new)
 assert sorted(rev[name])==meta['direct_consumers']
 seen={name};q=deque([name])
 while q:
  for n in rev[q.popleft()]:
   if n not in seen:seen.add(n);q.append(n)
 assert len(seen)==meta['reverse_reachable_count']
 closures[name]=len(seen)
# Verify the exact imported shifted-coordinate definitions.
norm=Path('research/ordinary13-residue90-norm-model-draft/Residue90GraphNorms.lean.src').read_text()
assert 'def k (v : Fin 13 → V) : V := (v 9+1)+(v 10+1)' in norm
assert 'def q (p : Fin 4 → ℕ) (v : Fin 13 → V) : V := 1+v 0*(p 0:V)' in norm
for x in range(250):
 for y in range(35):assert 2<=(x+1)+(y+1)
for b in range(1,1000):assert 2<=1+b
for R in range(100):
 for q in range(50):assert R+1<=R+q**3+q+1
print(json.dumps({'author_receipt_reproduces':True,'exact_priority3_deltas_and_signatures':True,'lexical_reverse_closures':closures,'finite_arithmetic_controls':True,'lean_executed':False,'provider_overrides_performed':False},sort_keys=True,indent=2))
