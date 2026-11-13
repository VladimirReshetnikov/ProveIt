from pathlib import Path
from hashlib import sha256
import json,sys,re
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-pell-period-final-body-eval-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
E=Path('research/ordinary13-pell-period-final-body-eval-draft/PellPeriodFinalBodyEval.lean.src').read_text()
F=Path('research/ordinary13-pell-period-full-wb-conditional-draft/PellPeriodFullWB.lean.src').read_text()
B=Path('research/ordinary13-pell-period-final-replacements-draft/PellPeriodFinalReplacements.lean.src').read_text()
R=Path('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text()
S=Path('../../lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/Basic/Semantics/Semantics.lean').read_text()
T=Path('../../lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/Arithmetic/Definability/Definable.lean').read_text()
q=re.search(r'def finalBody : ArithmeticSemisentence 8 :=\s*“(.*?)”',F,re.S).group(1)
compact=lambda s:re.sub(r'\s+','',s)
assert compact(q)=='tryxhcma.!yDefcma∧h=2*m*c∧!xDefxha∧!yDefyha∧x=1+c*c*r∧y=t*c*c'
b=re.search(r'def BodyData \(t r y x h c m a : V\) : Prop :=(.*?)\nend Model',B,re.S).group(1)
assert compact(b)==compact('yDef.val.Evalb ![c,m,a] ∧ h=2*m*c ∧ xDef.val.Evalb ![x,h,a] ∧ yDef.val.Evalb ![y,h,a] ∧ x=1+c*c*r ∧ y=t*c*c')
assert 'BodyData (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) (e 7)' in B
for token in ['theorem bodyEvaluationBridge : BodyEvaluationBridge','intro V _ _ e',
 'simp [BodyData, finalBody, Semiformula.eval_substs]',
 'tReplacement bodyEvaluationBridge','rReplacement bodyEvaluationBridge']:assert token in E
for token in ['“out time b. ∃ state, !runDef state time b ∧ !pi₁Def out state”',
 '“out time b. ∃ state, !runDef state time b ∧ !pi₂Def out state”',
 'instance x_defined : 𝚺₁-Function₂[V] xcoord via xDef',
 'instance y_defined : 𝚺₁-Function₂[V] ycoord via yDef']:assert token in R
assert '@[simp] lemma eval_substs' in S
assert 'φ.Eval (Semiterm.val b f ∘ w) f' in S
assert '@[simp] lemma iff' in T and 'φ.val.Evalb v ↔ R v' in T
# Concretely interpret each of the six quoted conjuncts and compare with the
# independently mapped graph argument positions and named equations.
def pell(n,a):
 x,y=1,0
 for _ in range(n):x,y=(a+2)*x+(a+1)*(a+3)*y,x+(a+2)*y
 return x,y
def direct(e):
 t,r,y,x,h,c,m,a=e
 return [pell(m,a)[1]==c,h==2*m*c,pell(h,a)[0]==x,pell(h,a)[1]==y,
         x==1+c*c*r,y==t*c*c]
def slotted(e):
 args_y0=[e[i] for i in (5,6,7)];args_x=[e[i] for i in (3,4,7)];args_y1=[e[i] for i in (2,4,7)]
 return [args_y0[0]==pell(args_y0[1],args_y0[2])[1],e[4]==2*e[6]*e[5],
         args_x[0]==pell(args_x[1],args_x[2])[0],args_y1[0]==pell(args_y1[1],args_y1[2])[1],
         e[3]==1+e[5]*e[5]*e[1],e[2]==e[0]*e[5]*e[5]]
base=[4,6,4,7,2,1,1,0];assert all(direct(base))
for i in range(8):
 changed=base.copy();changed[i]+=1
 assert direct(changed)==slotted(changed) and not all(direct(changed)),i
assert direct(base)==slotted(base)
controls=0
for m in range(3):
 for a in range(3):
  c=pell(m,a)[1];h=2*m*c;x,y=pell(h,a)
  for r in range(4):
   for t in range(4):
    e=[t,r,y,x,h,c,m,a];assert direct(e)==slotted(e);controls+=1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'all_eight_named_slots_and_three_graph_vectors_checked':True,
 'graph_and_substitution_simp_interfaces_inspected':True,'natural_controls':controls,
 'all_eight_slot_mutations_detected_on_one_true_instance':True,
 'lean_simp_and_provider_resolution_executed':False,'lean_executed':False},indent=2,sort_keys=True))
