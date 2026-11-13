from pathlib import Path
from hashlib import sha256
import json,sys,re
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-pell-period-xy-replacements-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
P=Path('research/ordinary13-pell-period-xy-replacements-draft/PellPeriodXYReplacements.lean.src').read_text()
F=Path('research/ordinary13-pell-period-full-wb-conditional-draft/PellPeriodFullWB.lean.src').read_text()
B=Path('research/ordinary13-pell-period-final-replacements-draft/PellPeriodFinalReplacements.lean.src').read_text()
E=Path('research/ordinary13-pell-period-final-body-eval-draft/PellPeriodFinalBodyEval.lean.src').read_text()
R=Path('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text()
G=Path('Lean/DiophantineConsistency/ArithmeticConstructionBoundPell.lean').read_text()
Q=Path('research/ordinary13-pell-run-exponential-bound-draft/PellRunExponentialBound.lean.src').read_text()
V=Path('Lean/DiophantineConsistency/PRAWitnessBoundTerms.lean').read_text()
for label,arity,body in [('R',7,'finalBody'),('Y',6,'bodyR'),('X',5,'bodyY')]:assert f'def body{label} : ArithmeticSemisentence {arity} := ∃⁰ {body}' in F
for tok in ['def boundX : BoundTerm 4 := exp2 (poly ‘2 * (#3 + 2) * #0’) (poly ‘0’)',
 'def boundY : BoundTerm 5 := exp2 (poly ‘2 * (#4 + 2) * #1’) (poly ‘0’)']:assert tok in F
assert '| exp2 A B, e => Exp.exp (A.vval e * Exp.exp (B.vval e))' in V
assert 'xDef.val.Evalb ![x,h,a] ∧ yDef.val.Evalb ![y,h,a]' in B
assert 'def BodyEvaluationBridge : Prop' in B and 'theorem bodyEvaluationBridge : BodyEvaluationBridge' in E
assert 'instance x_defined : 𝚺₁-Function₂[V] xcoord via xDef' in R
assert 'instance y_defined : 𝚺₁-Function₂[V] ycoord via yDef' in R
for name in ('x','y'):assert f'theorem {name}_le (t b : V) : {name}coord t b ≤ power (2 * (b + 2)) t' in G
assert 'theorem power_le_binary_exponential (B u : V)' in Q and 'power B u ≤ Exp.exp (B*u)' in Q
for tok in ['theorem xReplacement (evalBody : BodyEvaluationBridge) : Replacement bodyX boundX',
 'obtain ⟨y,r,t,hfinal⟩ := hx','(evalBody V (t :> r :> y :> x :> e)).mp hfinal',
 'change BodyData t r y x (e 0) (e 1) (e 2) (e 3) at data',
 'x_defined.defined ![x,e 0,e 3]','exact hg.mp data.2.2.1',
 'refine ⟨x, ?_, original⟩','xcoord_le_bound (e 0) (e 3)',
 'theorem yReplacement (evalBody : BodyEvaluationBridge) : Replacement bodyY boundY',
 'obtain ⟨r,t,hfinal⟩ := hy','(evalBody V (t :> r :> y :> e)).mp hfinal',
 'change BodyData t r y (e 0) (e 1) (e 2) (e 3) (e 4) at data',
 'y_defined.defined ![y,e 1,e 4]','exact hg.mp data.2.2.2.1',
 'refine ⟨y, ?_, original⟩','ycoord_le_bound (e 1) (e 4)',
 'xReplacement bodyEvaluationBridge','yReplacement bodyEvaluationBridge']:assert tok in P,tok
xEnv=['h','c','m','a'];yEnv=['x']+xEnv
assert ['t','r','y','x']+xEnv==['t','r','y']+yEnv==['t','r','y','x','h','c','m','a']
assert (xEnv[0],xEnv[3])==('h','a') and (yEnv[1],yEnv[4])==('h','a')
# Evaluate the target bounds and both coordinates independently at small indices.
count=0
for a in range(7):
 x,y=1,0;delta=(a+1)*(a+3)
 for h in range(9):
  xe=[h,2,3,a];ye=[x,h,2,3,a]
  boundX=2**(2*(xe[3]+2)*xe[0]);boundY=2**(2*(ye[4]+2)*ye[1])
  assert boundX==boundY and x<=boundX and y<=boundY
  x,y=(a+2)*x+delta*y,x+(a+2)*y;count+=1
assert 2**(2*(1+2)*3)!=2**(2*(3+2)*1)
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'x_y_binder_context_and_graph_conjuncts_checked':True,'bound_slots_and_growth_chain_checked':True,
 'finite_coordinate_controls_including_zero':count,'body_bridge_and_tactics_elaborated':False,
 'lean_executed':False},indent=2,sort_keys=True))
