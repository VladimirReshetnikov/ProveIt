from pathlib import Path
from hashlib import sha256
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/current2011-shear72-local-nozero-bridge-selection');BASE=Path('research/current2011-shear72-order-carrier-selection/selection.json')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
old=Path('research/current2011-shear72-conditional-ipra-endpoint-draft/Shear72ConditionalIPRA.lean.src').read_text();new=(D/'Shear72ConditionalIPRA.lean.src').read_text()
a='import DiophantineConsistency.HAExpressionNoZeroEquiv\n';assert old.count(a)==1;old=old.replace(a,'',1)
a='open AdaptiveEquationSyntax2011 HAExpressionAssembly HAExpressionNoZeroEquiv\n';b='open AdaptiveEquationSyntax2011 HAExpressionAssembly FoundationHANoZero\n';assert old.count(a)==1;old=old.replace(a,b,1)
marker='/-- Each direction may change the valuation; no same-witness assertion. -/'
insert='''/-- Local copy of the exact all-model no-zero interface. -/
def SameNoZero {n m : ℕ} (e : Expr (Fin n)) (f : Expr (Fin m)) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    (∀ v : Fin n → V, ¬InternalZero e v) ↔ ∀ v : Fin m → V, ¬InternalZero f v

'''
assert old.count(marker)==1;old=old.replace(marker,insert+marker,1)
a='''theorem bridge72 (forward : ParentToChild) (reverse : ChildToParent) :
    PolynomialBridge child :=
  HAExpressionNoZeroEquiv.bridge child parent (same_no_zero forward reverse)
    OrdinarySphere7160IPRA.bridge71
'''
b='''theorem bridge72 (forward : ParentToChild) (reverse : ChildToParent) :
    PolynomialBridge child := by
  intro V _ _
  have eqv : (classicalNoZero child).Evalb (M := V) ![] ↔
      (classicalNoZero parent).Evalb (M := V) ![] := by
    rw [classicalNoZero_iff, classicalNoZero_iff]
    simpa only [InternalZero, ne_eq] using same_no_zero forward reverse V
  exact eqv.trans (OrdinarySphere7160IPRA.bridge71 V)
'''
assert old.count(a)==1;old=old.replace(a,b,1);assert old==new
oldj=Path('research/current2011-shear72-joint-ipra-source-plan/Shear72JointIPRA.lean.src').read_text();newj=(D/'Shear72JointIPRA.lean.src').read_text();a='open AdaptiveEquationSyntax2011 HAExpressionAssembly HAExpressionNoZeroEquiv\n';b='open AdaptiveEquationSyntax2011 HAExpressionAssembly\n';assert oldj.count(a)==1 and oldj.replace(a,b,1)==newj
orig=Path('research/current2011-shear72-conditional-ipra-endpoint-draft/Shear72ConditionalIPRA.lean.src').read_text();assert orig.split('theorem native_equivalence72',1)[1]==new.split('theorem native_equivalence72',1)[1]
upstream=Path('Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean').read_text();parent=Path('research/current2011-ordinary71-60-ipra/OrdinarySphere7160IPRA.lean').read_text();assembly=Path('Lean/DiophantineConsistency/HAExpressionAssembly.lean').read_text()
for t in ['(∀ v : Fin n → V, ¬InternalZero e v) ↔ ∀ v : Fin m → V, ¬InternalZero f v','rw [classicalNoZero_iff, classicalNoZero_iff]','simpa only [InternalZero, ne_eq] using h V']:assert t in upstream,t
for t in ['theorem classicalNoZero_iff','def PolynomialBridge']:assert t in assembly,t
for t in ['open HAExpressionAssembly FoundationHANoZero','theorem bridge71 : PolynomialBridge','rw [classicalNoZero_iff, classicalNoZero_iff]']:assert t in parent,t
expected=json.loads(BASE.read_text());actual=json.loads((D/'selection.json').read_text())
for name,file in [('DiophantineConsistency.Shear72ConditionalIPRA','Shear72ConditionalIPRA.lean.src'),('DiophantineConsistency.Shear72JointIPRA','Shear72JointIPRA.lean.src')]:
 p=D/file;expected['drafts'][name]={'path':str(p),'sha256':sha256(p.read_bytes()).hexdigest(),'imports':re.findall(r'^import\s+(\S+)',p.read_text(),re.M)}
expected['frontier'].pop('DiophantineConsistency.HAExpressionNoZeroEquiv');assert actual==expected
for n,i in actual['drafts'].items():
 p=Path(i['path']);assert sha256(p.read_bytes()).hexdigest()==i['sha256'],n
 assert re.findall(r'^import\s+(\S+)',p.read_text(),re.M)==i['imports'],n
for n,i in actual['frontier'].items():
 if i['kind']!='external-unexamined':assert sha256(Path(i['path']).read_bytes()).hexdigest()==i['sha256'],n
seen=set();active=set();used=set();order=[]
def visit(n):
 if n in seen:return
 assert n not in active,n
 active.add(n)
 for x in actual['drafts'][n]['imports']:
  if x in actual['drafts']:visit(x)
  else:assert x in actual['frontier'],x;used.add(x)
 active.remove(n);seen.add(n);order.append(n)
visit('DiophantineConsistency.Shear72JointIPRA');assert seen==set(actual['drafts']) and used==set(actual['frontier'])
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'selection_sha256':sha256((D/'selection.json').read_bytes()).hexdigest(),'conditional_exact_delta_checked':True,'native_and_translated_statements_and_proofs_unchanged':True,'joint_exact_namespace_delta_checked':True,'same_nozero_and_source_bridge_compared':True,'selected_draft_count':len(seen),'draft_topological_order':order,'removed_direct_frontier':'DiophantineConsistency.HAExpressionNoZeroEquiv','transitive_provider_audited':False,'lean_executed':False},sort_keys=True,indent=2))
