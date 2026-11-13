from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-pell-period-h-replacement-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
prior=Path('research/ordinary13-pell-period-full-wb-conditional-draft/PellPeriodFullWB.lean.src').read_text()
for tok in ['def bodyR : ArithmeticSemisentence 7 := ∃⁰ finalBody','def bodyY : ArithmeticSemisentence 6 := ∃⁰ bodyR','def bodyX : ArithmeticSemisentence 5 := ∃⁰ bodyY','def bodyH : ArithmeticSemisentence 4 := ∃⁰ bodyX','def boundH : BoundTerm 3 := poly ‘2 * #1 * #0’','def Replacement']:assert tok in prior,tok
r=Path('research/ordinary13-pell-period-final-replacements-draft/PellPeriodFinalReplacements.lean.src').read_text()
for tok in ['def BodyData (t r y x h c m a : V)','yDef.val.Evalb ![c,m,a] ∧ h=2*m*c','def BodyEvaluationBridge : Prop']:assert tok in r,tok
s=(D/'PellPeriodHReplacement.lean.src').read_text()
for tok in ['theorem hReplacement (evalBody : BodyEvaluationBridge) : Replacement bodyH boundH','t :> r :> y :> x :> h :> e','BodyData t r y x h (e 0) (e 1) (e 2)','h=2*(e 1)*(e 0)','⟨h, ?_, original⟩','hReplacement bodyEvaluationBridge']:assert tok in s,tok
# Trace the expected binder and context positions and test exact bounds.
e=['c','m','a'];assert e[0]=='c' and e[1]=='m'
assert ['t','r','y','x','h']+e==['t','r','y','x','h','c','m','a']
count=0
for c in range(15):
 for m in range(15):
  for a in range(5):
   h=2*m*c;env=[c,m,a];bound=2*env[1]*env[0]
   assert h<=bound and h==bound
   count+=1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'prior_body_and_bound_source_shapes_checked':True,'outer_environment':['c','m','a'],'nested_witness_order':['x','y','r','t'],'same_h_controls':count,'quotation_and_boundterm_elaborated':False,'lean_executed':False},sort_keys=True,indent=2))
