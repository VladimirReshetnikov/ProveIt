from pathlib import Path
from hashlib import sha256
import json,math,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-pell-period-ipra-interface-audit')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
checks={
 'Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean':['def xDef : 𝚺₁.Semisentence 3','def yDef : 𝚺₁.Semisentence 3','instance x_defined : 𝚺₁-Function₂[V] xcoord via xDef','instance y_defined : 𝚺₁-Function₂[V] ycoord via yDef'],
 'Lean/DiophantineConsistency/ArithmeticPellSquaredSeed.lean':['theorem doubled_quotients (n R a : V)','theorem squared_ordinate (R a : V)'],
 'research/ordinary13-explicit-pell-period-model-draft/ExplicitPellPeriod.lean.src':['theorem period_at_twice_index_ordinate','doubled_quotients (ycoord m a) m a'],
 'Lean/DiophantineConsistency/HAExpressionAssembly.lean':['def PolynomialBridge','theorem isigma1_equivalence','LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁'],
 'Lean/DiophantineConsistency/IPRAExpressionNative.lean':['theorem equivalence_of_isigma1','theorem equivalence_of_bridge','(hp : HAExpressionAssembly.PolynomialBridge e)'],
 'Lean/DiophantineConsistency/PRAISigmaOneOpenComparison.lean':['theorem comparison (σ : ArithmeticSentence) (p : 𝗜𝚺₁ ⊢ σ)','(θ : Semiproposition language 1) (hθ : θ.Open)','(hgoal : PRA ⊢ (Semiformula.lMap embedding σ 🡒 (∃⁰ θ).univCl))'],
 'Lean/DiophantineConsistency/PRAWitnessTransfer.lean':['theorem transfer (ψ φ Tg : ArithmeticSemisentence (n + 1))','(hdom : PRA ⊢ dominates Tg Tt)','(hb : (bnd ψ).Eval'],
 'Lean/DiophantineConsistency/IPRAFullGGTransfer.lean':['theorem from_classical {φ : Sentence language} (h : PRA ⊢ φ) : nativeTheory ⊢ φᴺ'],
 'Lean/DiophantineConsistency/IPRAMappedNoZero.lean':['theorem mapped_gg_noZero','(Semiformula.lMap embedding (noZero n a b))ᴺ'],
 'Lean/DiophantineConsistency/IPRANativeOpenDecidable.lean':['def openStable (φ : Proposition language) (h : φ.Open)'],
 'Lean/DiophantineConsistency/IPRAStandardTheory.lean':['theorem provable_iff (φ : Sentenceᵢ language) : standardTheory ⊢ φ ↔ nativeTheory ⊢ φ']}
for f,toks in checks.items():
 s=Path(f).read_text()
 for t in toks:assert t in s,(f,t)
for m in range(30):
 for c in range(30):
  h=2*m*c
  assert math.gcd(4*h,c)==c
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'source_interfaces_checked':len(checks),'period_at_twice_index_forces_gcd_4h_c_to_equal_c':True,'bounded_gcd_controls':900,'all_model_whole_expression_assembly_exists':True,'standalone_period_to_native_ipra_derived':False,'lean_executed':False},sort_keys=True,indent=2))
