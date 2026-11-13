from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/current2011-shear72-conditional-ipra-endpoint-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
s=(D/'Shear72ConditionalIPRA.lean.src').read_text()
for t in ['def ParentToChild : Prop','InternalZero parent v → ∃ w : Fin 14 → V, InternalZero child w','def ChildToParent : Prop','InternalZero child v → ∃ w : Fin 14 → V, InternalZero parent w','SameNoZero child parent','forward V v hv','reverse V v hv','HAExpressionNoZeroEquiv.bridge child parent (same_no_zero forward reverse)','OrdinarySphere7160IPRA.bridge71','IPRAExpressionNative.equivalence_of_bridge child','IPRAStandardTheory.provable_iff','IPRABoundedRhoZFC.zfcEquiv']:
 assert t in s,t
bridge=Path('Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean').read_text()
for t in ['def SameNoZero','theorem bridge {n m : ℕ}', '(h : SameNoZero e f) (hf : PolynomialBridge f) : PolynomialBridge e']:
 assert t in bridge,t
native=Path('Lean/DiophantineConsistency/IPRAExpressionNative.lean').read_text()
assert 'theorem equivalence_of_bridge {n : ℕ}' in native
parent=Path('research/current2011-ordinary71-60-ipra/OrdinarySphere7160IPRA.lean').read_text()
for t in ['theorem bridge71 : PolynomialBridge','theorem standard_translated_equivalence71','Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z)','Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h)']:
 assert t in parent,t
assert s.count('Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z)')==1
assert s.count('Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h)')==1
# Different finite zero sets can satisfy both existence maps; no same-valuation condition.
a={0};b={1,2};assert bool(a)==bool(b) and a!=b
# Either one-way map by itself does not establish equivalent existence.
assert (not set() or bool({1})) and bool(set())!=bool({1})
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'two_map_and_bridge_source_shapes_checked':True,'translated_composition_matches_parent':True,'different_witness_control':True,'one_map_insufficient_control':True,'maps_proved_here':False,'lean_executed':False},sort_keys=True,indent=2))
