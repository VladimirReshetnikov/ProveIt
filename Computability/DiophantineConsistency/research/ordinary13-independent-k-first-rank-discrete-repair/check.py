from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-first-rank-discrete-repair')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
s=Path('research/ordinary13-independent-k-first-rank-model-draft/IndependentKFirstRank.lean.src').read_text()
a="    have halpha : A≤Q-F'-1 := by dsimp [C] at hc; linarith\n"
b="""    have hFA : F+alpha<q := by
      apply ι_lt_ι.mp
      have hh : (ι (F+alpha) : DiffRing V)<ι q := by
        dsimp [C,Q,F',A] at hc
        simp only [map_add]
        linarith
      exact hh
    have hFA1 : F+alpha+1≤q := add_one_le_iff.mpr hFA
    have hFA1' : (ι F : DiffRing V)+ι alpha+1≤ι q := by
      have hh := ι_le_ι.mpr hFA1
      simpa only [map_add,map_one] using hh
    have halpha : A≤Q-F'-1 := by
      dsimp [A,Q,F']
      linarith [hFA1']
"""
assert s.count(a)==1
s=s.replace(a,b).replace('namespace DiophantineConsistency.IndependentKFirstRankDraft','namespace DiophantineConsistency.IndependentKFirstRankDiscreteDraft').replace('end DiophantineConsistency.IndependentKFirstRankDraft','end DiophantineConsistency.IndependentKFirstRankDiscreteDraft').replace('#print axioms DiophantineConsistency.IndependentKFirstRankDraft.','#print axioms DiophantineConsistency.IndependentKFirstRankDiscreteDraft.')
assert (D/'IndependentKFirstRankDiscrete.lean.src').read_text()==s
assert 'apply ι_lt_ι.mp' in s and 'add_one_le_iff.mpr hFA' in s and 'ι_le_ι.mpr hFA1' in s
assert 'IndependentKZeroMainRankDraft.zero_k_impossible' in s
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'exact_single_gap_repair_and_namespace_replacement':True,
 'reflection_successor_reembedding_observed':True,'parent_main_helper_call_preserved':True,
 'lean_executed':False,'elaboration_or_provider_validation':False},sort_keys=True,indent=2))
