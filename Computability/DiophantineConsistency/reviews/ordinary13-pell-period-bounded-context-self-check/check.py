from pathlib import Path
from hashlib import sha256
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-pell-period-bounded-context-self-check')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-pell-period-bounded-formula-draft/PellPeriodBounded.lean.src').read_text()
m=re.search(r'def periodDef : 𝚺₁.Semisentence 2 := \.mkSigma\s*“(.*?)”',p,re.S);assert m
q=' '.join(m.group(1).split())
assert q=='m a. ∃ c h x y r t, !yDef c m a ∧ h=2*m*c ∧ !xDef x h a ∧ !yDef y h a ∧ x=1+c*c*r ∧ y=t*c*c'
# Conventional binder-stack layout expected under the stated quotation and
# finite-vector convention. This is a source-level model, not macro execution.
env=['t','r','y','x','h','c','m','a'];idx={v:i for i,v in enumerate(env)}
args={x:[idx[v] for v in vs] for x,vs in {'first_y':['c','m','a'],'period_x':['x','h','a'],'period_y':['y','h','a']}.items()}
assert args=={'first_y':[5,6,7],'period_x':[3,4,7],'period_y':[2,4,7]}
for token in ['h=2*m*c','x=1+c*c*r','y=t*c*c','periodDef.val.Evalb ![m,a]','(bridge : PeriodEvaluationBridge)','r,t,rfl,rfl,rfl,rfl,hx,hy']:
 assert token in p,token
r=Path('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text()
for token in ['“out time b. ∃ state, !runDef state time b ∧ !pi₁Def out state”','“out time b. ∃ state, !runDef state time b ∧ !pi₂Def out state”','instance x_defined : 𝚺₁-Function₂[V] xcoord via xDef','instance y_defined : 𝚺₁-Function₂[V] ycoord via yDef']:
 assert token in r,token
proof=Path('Lean/DiophantineConsistency/ArithmeticPellRecurrenceChecks.lean').read_text()
assert 'xDef.val.Evalb ![xcoord time b,time,b]' in proof and 'yDef.val.Evalb ![ycoord time b,time,b]' in proof
prior=Path('Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean').read_text()
assert '“r a b. ∃ e u v, !expDef e (4*r) ∧ !yDef u (r+1) b' in prior
bnd=Path('Lean/DiophantineConsistency/StrictSigmaOneInduction.lean').read_text()
for token in ['def bnd : {n : ℕ} → ArithmeticSemiformula ξ n → ArithmeticSemiformula ξ (n + 1)','(Fin.snoc e w : Fin (n + 1) → M)','Fin.cons_snoc_eq_snoc_cons','theorem eval_bnd_imp']:
 assert token in bnd,token
# Direct finite standard-natural controls, using moderate exact recurrences;
# they check the intended argument order but cannot inspect Lean's macro AST.
def pair(m,a):
 A=a+2;delta=(a+1)*(a+3);x,y=1,0
 for _ in range(m):x,y=A*x+delta*y,x+A*y
 return x,y
cases=[]
for m,a in ((1,0),(2,0),(2,1),(3,0)):
 c=pair(m,a)[1];h=2*m*c;x,y=pair(h,a)
 assert c>0 and (x-1)%(c*c)==0 and y%(c*c)==0
 r=(x-1)//(c*c);t=y//(c*c)
 assert c==pair(m,a)[1] and h==2*m*c and x==pair(h,a)[0] and y==pair(h,a)[1] and x==1+c*c*r and y==t*c*c
 cases.append([m,a,c,h])
assert pair(2,0)[1]!=pair(0,2)[1]
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'source_level_debruijn_expectation':idx,'graph_argument_expectation':args,'bounded_outer_context':['m','a','w'],'direct_natural_controls':cases,'macro_generated_ast_inspected':False,'evaluation_bridge_proved':False,'draft_elaborated':False,'lean_executed':False},sort_keys=True,indent=2))
