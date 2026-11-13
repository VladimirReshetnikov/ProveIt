from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize
D=Path('research/adaptive87-four-square-current88-ipra-endpoint-draft');M=Path('research/adaptive87-four-square-current88-model-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
assert subprocess.run([sys.executable,'-I','-S','-B',str(M/'check.py')],check=True,stdout=subprocess.PIPE,timeout=30).stdout==(M/'result.json').read_bytes()
s=(D/'AdaptiveFourSquare88IPRA.lean.src').read_text();m=(M/'FourSquare88Model.lean.src').read_text();g=(M/'AdaptiveFourSquare88Graph.lean.src').read_text();h=Path('Lean/DiophantineConsistency/HAAdaptiveFactor87.lean').read_text();native=Path('Lean/DiophantineConsistency/IPRAExpressionNative.lean').read_text();std=Path('Lean/DiophantineConsistency/IPRAStandardTheory.lean').read_text();rho=Path('Lean/DiophantineConsistency/IPRABoundedRhoZFC.lean').read_text()
for t in ['import FourSquare88Model','import DiophantineConsistency.HAAdaptiveFactor87','theorem bridge88 : PolynomialBridge naturalExpression','AdaptiveFourSquare88ModelDraft.bridge HAAdaptiveFactor87.polynomialBridge','IPRAExpressionNative.equivalence_of_bridge naturalExpression bridge88','(IPRAStandardTheory.provable_iff _).2 native_equivalence88','(Semiformula.lMap embedding sourceSentence)ᴺ','Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z)','Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h)']:assert t in s,t
for t in ['def naturalExpression : Expr (Fin 13) := positiveShift (expressionAt CurrentWindowCarry2011.ports)','theorem sameZero : HAExpressionSameZero.SameZero naturalExpression','AdaptiveFirstRootFactor87Literal.naturalExpression87','theorem bridge (hp : PolynomialBridge AdaptiveFirstRootFactor87Literal.naturalExpression87)','PolynomialBridge naturalExpression']:assert t in m,t
assert 'def expressionAt (p : Fin 4 → ℤ) : Expr (Fin 13) := (graph p).output' in g
assert 'theorem polynomialBridge :' in h and 'PolynomialBridge AdaptiveFirstRootFactor87Literal.naturalExpression87' in h
assert 'theorem equivalence_of_bridge {n : ℕ}' in native
assert 'standardTheory ⊢ φ ↔ nativeTheory ⊢ φ' in std
assert '(Semiformula.lMap embedding sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation embedding' in rho
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'prior_model_source_receipt_reproduced':True,'same_shifted_literal_and_parent_bridge_interface_checked':True,'native_standard_gg_source_directions_checked':True,'parent_bridge_free_hypothesis':False,'lean_executed':False,'combined_provider_authenticated':False},sort_keys=True,indent=2))
