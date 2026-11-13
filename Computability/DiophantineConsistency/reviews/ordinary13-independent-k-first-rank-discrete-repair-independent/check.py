from pathlib import Path
from hashlib import sha256
from fractions import Fraction
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-first-rank-discrete-repair-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
repair=Path('research/ordinary13-independent-k-first-rank-discrete-repair');original=Path('research/ordinary13-independent-k-first-rank-model-draft')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(repair/'check.py')])==(repair/'receipt.json').read_bytes()
a=(original/'IndependentKFirstRank.lean.src').read_text();b=(repair/'IndependentKFirstRankDiscrete.lean.src').read_text()
old="    have halpha : A≤Q-F'-1 := by dsimp [C] at hc; linarith\n"
assert a.count(old)==1
start=b.index('    have hFA : F+alpha<q := by\n');end=b.index('    have hqF : Q-F',start)
block=b[start:end]
for token in ['apply ι_lt_ι.mp','(ι (F+alpha) : DiffRing V)<ι q','dsimp [C,Q,F\',A] at hc','add_one_le_iff.mpr hFA','ι_le_ι.mpr hFA1','simpa only [map_add,map_one] using hh','linarith [hFA1\']']:
 assert token in block,token
expected=a.replace(old,block).replace('namespace DiophantineConsistency.IndependentKFirstRankDraft','namespace DiophantineConsistency.IndependentKFirstRankDiscreteDraft').replace('end DiophantineConsistency.IndependentKFirstRankDraft','end DiophantineConsistency.IndependentKFirstRankDiscreteDraft').replace('#print axioms DiophantineConsistency.IndependentKFirstRankDraft.','#print axioms DiophantineConsistency.IndependentKFirstRankDiscreteDraft.')
assert expected==b
model=Path('Lean/DiophantineConsistency/ModelDifferenceRing.lean').read_text()
assert 'theorem ι_lt_ι {a b : V} : ι a < ι b ↔ a < b' in model
assert 'theorem ι_le_ι {a b : V} : ι a ≤ ι b ↔ a ≤ b' in model
count=0
for q in range(1,100):
 for F in range(q+2):
  for alpha in range(q+2):
   if 0<q-F-alpha:
    assert F+alpha<q and F+alpha+1<=q and alpha<=q-F-1
    count+=1
# The prior ordered-field countermodel fails the newly explicit unit-gap premise.
q=Fraction(4);F=Fraction(1);alpha=Fraction(5,2)
assert F+alpha<q and not F+alpha+1<=q
print(json.dumps({'author_receipt_reproduced':True,'exact_repair_and_namespace_delta':True,'source_reflection_orientations_checked':True,'finite_natural_gap_controls':count,'old_rational_counterexample_rejected_by_explicit_successor_premise':True,'lean_executed':False,'model_or_provider_elaboration':False},sort_keys=True,indent=2))
