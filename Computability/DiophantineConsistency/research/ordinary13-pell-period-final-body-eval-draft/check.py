from pathlib import Path
from hashlib import sha256
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-pell-period-final-body-eval-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
prior=Path('research/ordinary13-pell-period-full-wb-conditional-draft/PellPeriodFullWB.lean.src').read_text()
m=re.search(r'def finalBody : ArithmeticSemisentence 8 :=\s*“(.*?)”',prior,re.S);assert m
q=' '.join(m.group(1).split())
assert q=='t r y x h c m a. !yDef c m a ∧ h=2*m*c ∧ !xDef x h a ∧ !yDef y h a ∧ x=1+c*c*r ∧ y=t*c*c'
s=Path('research/ordinary13-pell-period-final-replacements-draft/PellPeriodFinalReplacements.lean.src').read_text()
for tok in ['def BodyData (t r y x h c m a : V)','yDef.val.Evalb ![c,m,a] ∧ h=2*m*c','xDef.val.Evalb ![x,h,a] ∧ yDef.val.Evalb ![y,h,a]','x=1+c*c*r ∧ y=t*c*c','def BodyEvaluationBridge : Prop','BodyData (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) (e 7)','theorem tReplacement (evalBody : BodyEvaluationBridge)','theorem rReplacement (evalBody : BodyEvaluationBridge)']:assert tok in s,tok
z=(D/'PellPeriodFinalBodyEval.lean.src').read_text()
for tok in ['theorem bodyEvaluationBridge : BodyEvaluationBridge','simp [BodyData, finalBody, Semiformula.eval_substs]','tReplacement bodyEvaluationBridge','rReplacement bodyEvaluationBridge']:assert tok in z
r=Path('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text()
assert '“out time b. ∃ state, !runDef state time b ∧ !pi₁Def out state”' in r
assert '“out time b. ∃ state, !runDef state time b ∧ !pi₂Def out state”' in r
# Independent finite model: compare token-position interpretation of the
# quoted conjuncts with the separately named data interpretation.
def pell(n,a):
 x,y=1,0
 for _ in range(n):x,y=(a+2)*x+(a+1)*(a+3)*y,x+(a+2)*y
 return x,y
count=0;true_cases=0
for m in range(3):
 for a in range(3):
  c=pell(m,a)[1];h=2*m*c;x,y=pell(h,a)
  for rr in range(4):
   for tt in range(4):
    e=[tt,rr,y,x,h,c,m,a]
    interpreted=(pell(e[6],e[7])[1]==e[5] and e[4]==2*e[6]*e[5] and pell(e[4],e[7])[0]==e[3] and pell(e[4],e[7])[1]==e[2] and e[3]==1+e[5]*e[5]*e[1] and e[2]==e[0]*e[5]*e[5])
    t,r,Y,X,H,C,M,A=e
    named=(C==pell(M,A)[1] and H==2*M*C and X==pell(H,A)[0] and Y==pell(H,A)[1] and X==1+C*C*r and Y==t*C*C)
    assert interpreted==named
    true_cases+=int(named);count+=1
assert true_cases>0 and true_cases<count
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'named_and_quoted_source_shapes_checked':True,'source_slot_order':['t','r','y','x','h','c','m','a'],'standard_natural_controls':count,'true_controls':true_cases,'lean_quotation_ast_checked':False,'bridge_and_replacements_elaborated':False,'lean_executed':False},sort_keys=True,indent=2))
