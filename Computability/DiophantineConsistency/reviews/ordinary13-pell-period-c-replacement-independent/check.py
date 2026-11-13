from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-pell-period-c-replacement-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
P=Path('research/ordinary13-pell-period-c-replacement-draft/PellPeriodCReplacement.lean.src').read_text()
F=Path('research/ordinary13-pell-period-full-wb-conditional-draft/PellPeriodFullWB.lean.src').read_text()
B=Path('research/ordinary13-pell-period-final-replacements-draft/PellPeriodFinalReplacements.lean.src').read_text()
E=Path('research/ordinary13-pell-period-final-body-eval-draft/PellPeriodFinalBodyEval.lean.src').read_text()
R=Path('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text()
Y=Path('Lean/DiophantineConsistency/ArithmeticConstructionBoundPell.lean').read_text()
Q=Path('research/ordinary13-pell-run-exponential-bound-draft/PellRunExponentialBound.lean.src').read_text()
V=Path('Lean/DiophantineConsistency/PRAWitnessBoundTerms.lean').read_text()
S=Path('../../lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/Basic/Semantics/Semantics.lean').read_text()
T=Path('../../lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/Arithmetic/Definability/Definable.lean').read_text()
for label,arity,body in [('R',7,'finalBody'),('Y',6,'bodyR'),('X',5,'bodyY'),('H',4,'bodyX'),('C',3,'bodyH')]:
 assert f'def body{label} : ArithmeticSemisentence {arity} := ∃⁰ {body}' in F
assert 'def boundC : BoundTerm 2 := exp2 (poly ‘2 * (#1 + 2) * #0’) (poly ‘0’)' in F
assert '| exp2 A B, e => Exp.exp (A.vval e * Exp.exp (B.vval e))' in V
assert 'Eval b f (∃⁰ φ) ↔ ∃ x : M, Eval (x :> b) f φ' in S
assert 'yDef.val.Evalb ![c,m,a] ∧ h=2*m*c' in B and 'def BodyEvaluationBridge : Prop' in B
assert 'instance y_defined : 𝚺₁-Function₂[V] ycoord via yDef' in R
assert 'Defined (fun v ↦ v 0 = f (v ·.succ)) φ' in T
assert 'DefinedFunction (fun v => f (v 0) (v 1)) φ' in T
assert 'theorem y_le (t b : V) : ycoord t b ≤ power (2 * (b + 2)) t' in Y
assert 'theorem power_le_binary_exponential (B u : V)' in Q and 'power B u ≤ Exp.exp (B*u)' in Q
assert 'theorem bodyEvaluationBridge : BodyEvaluationBridge' in E
for tok in ['theorem ordinate_le_bound (m a : V)',
 'le_trans (y_le m a) (power_le_binary_exponential (2*(a+2)) m)',
 'theorem cReplacement (evalBody : BodyEvaluationBridge) : Replacement bodyC boundC',
 'have original := hc', 'obtain ⟨h,x,y,r,t,hfinal⟩ := hc',
 '(evalBody V (t :> r :> y :> x :> h :> c :> e)).mp hfinal',
 'change BodyData t r y x h c (e 0) (e 1) at data',
 'y_defined.defined ![c,e 0,e 1]', 'exact hy.mp data.1',
 'refine ⟨c, ?_, original⟩','rw [← heq] at hbound',
 'simpa [boundC, PRAWitnessBoundTerms.BoundTerm.vval, numeral_eq_natCast] using hbound',
 'cReplacement bodyEvaluationBridge']:assert tok in P,tok
count=0
for a in range(7):
 X,Y=1,0;delta=(a+1)*(a+3)
 for m in range(9):
  c=Y;outer=[m,a];h=4;x=5;y=6;r=7;t=8
  assert [t,r,y,x,h,c]+outer==[t,r,y,x,h,c,m,a]
  B=2*(a+2);bound=2**(B*m)
  assert c<=B**m<=bound
  X,Y=(a+2)*X+delta*Y,X+(a+2)*Y;count+=1
assert 0<=2**0
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'five_existential_order_and_eight_slots_inspected':True,
 'y_defined_function_argument_order_inspected':True,'growth_chain_and_boundC_inspected':True,
 'small_controls_including_zero_index':count,'body_bridge_and_simp_unelaborated':True,
 'lean_executed':False},indent=2,sort_keys=True))
