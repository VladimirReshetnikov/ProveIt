from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-pell-period-final-replacements-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
s=(D/'PellPeriodFinalReplacements.lean.src').read_text()
for tok in ['theorem replaceR','theorem replaceT','rcases eq_zero_or_pos c','def BodyData','def BodyEvaluationBridge : Prop','theorem tReplacement (evalBody : BodyEvaluationBridge)','theorem rReplacement (evalBody : BodyEvaluationBridge)','(e 4) (e 1) t hy','(e 3) (e 1) r hx','(t :> r :> e)','(t :> r\' :> e)']:assert tok in s,tok
p=Path('research/ordinary13-pell-period-full-wb-conditional-draft/PellPeriodFullWB.lean.src').read_text()
for tok in ['“t r y x h c m a. !yDef c m a','def bodyR : ArithmeticSemisentence 7 := ∃⁰ finalBody','def boundR : BoundTerm 6 := poly ‘#1’','def boundT : BoundTerm 7 := poly ‘#1’','def Replacement']:assert tok in p,tok
assert ['r','y','x','h','c','m','a'][1]=='y' and ['r','y','x','h','c','m','a'][4]=='c'
assert ['y','x','h','c','m','a'][1]=='x' and ['y','x','h','c','m','a'][3]=='c'
controls=0
for c in range(10):
 for r in range(12):
  for t in range(12):
   x=1+c*c*r;y=t*c*c
   rr=0 if c==0 else r;tt=0 if c==0 else t
   assert rr<=x and tt<=y and x==1+c*c*rr and y==tt*c*c
   controls+=1
# For c=0 the original witnesses cannot be uniformly bounded by x and y.
assert 10>1 and 10>0 and 1==1+0*0*10 and 0==10*0*0
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'exact_context_and_source_interfaces_checked':True,'replacement_controls':controls,'quoted_body_evaluation_bridge_unproved':True,'lean_executed':False,'ipra_derivation_proved':False},sort_keys=True,indent=2))
