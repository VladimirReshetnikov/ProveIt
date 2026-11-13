from pathlib import Path
from hashlib import sha256
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-pell-period-h-replacement-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
P=Path('research/ordinary13-pell-period-h-replacement-draft/PellPeriodHReplacement.lean.src').read_text()
F=Path('research/ordinary13-pell-period-full-wb-conditional-draft/PellPeriodFullWB.lean.src').read_text()
R=Path('research/ordinary13-pell-period-final-replacements-draft/PellPeriodFinalReplacements.lean.src').read_text()
E=Path('research/ordinary13-pell-period-final-body-eval-draft/PellPeriodFinalBodyEval.lean.src').read_text()
V=Path('Lean/DiophantineConsistency/PRAWitnessBoundTerms.lean').read_text()
S=Path('../../lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/Basic/Semantics/Semantics.lean').read_text()
for label,arity,body in [('R',7,'finalBody'),('Y',6,'bodyR'),('X',5,'bodyY'),('H',4,'bodyX')]:
 assert f'def body{label} : ArithmeticSemisentence {arity} := ∃⁰ {body}' in F
assert 'def boundH : BoundTerm 3 := poly ‘2 * #1 * #0’' in F
assert '| poly P, e => P.val e Empty.elim' in V
assert 'Eval b f (∃⁰ φ) ↔ ∃ x : M, Eval (x :> b) f φ' in S
assert 'def BodyData (t r y x h c m a : V)' in R
assert 'yDef.val.Evalb ![c,m,a] ∧ h=2*m*c ∧' in R
assert 'BodyData (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) (e 7)' in R
for x in ['theorem hReplacement (evalBody : BodyEvaluationBridge) : Replacement bodyH boundH',
 'have original := hh', 'change (∃⁰ (∃⁰ (∃⁰ (∃⁰ finalBody)))).Eval (h :> e) Empty.elim at hh',
 'simp only [Semiformula.eval_ex] at hh', 'obtain ⟨x,y,r,t,hfinal⟩ := hh',
 '(evalBody V (t :> r :> y :> x :> h :> e)).mp hfinal',
 'change BodyData t r y x h (e 0) (e 1) (e 2) at data',
 'have heq : h=2*(e 1)*(e 0) := data.2.1',
 'refine ⟨h, ?_, original⟩', 'simpa [boundH, PRAWitnessBoundTerms.BoundTerm.vval, numeral_eq_natCast] using le_of_eq heq',
 'hReplacement bodyEvaluationBridge']:assert x in P,x
assert 'theorem bodyEvaluationBridge : BodyEvaluationBridge' in E
count=0
for c in range(16):
 for m in range(16):
  for a in range(6):
   e=[c,m,a];h=2*m*c;x,y,r,t=7,8,9,10
   vec=[t,r,y,x,h]+e
   assert vec==[t,r,y,x,h,c,m,a]
   assert vec[4]==2*vec[6]*vec[5]==2*e[1]*e[0]
   assert h<=2*e[1]*e[0]
   count+=1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'four_binders_and_eight_slot_order_checked':True,'boundH_context_and_same_witness_checked':True,
 'body_bridge_remains_unelaborated':True,'finite_context_controls':count,'lean_executed':False},indent=2,sort_keys=True))
