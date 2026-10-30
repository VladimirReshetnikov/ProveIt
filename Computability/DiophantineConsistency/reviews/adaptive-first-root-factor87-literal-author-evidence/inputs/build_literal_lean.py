"""Generate the 87-row literal and one-hole context from the pinned DAGs."""
from pathlib import Path
import hashlib,json,os
D=Path(__file__).resolve().parents[2];P=D/'candidates/free-j-polarized-positive/source/positive/p13_free_J.json';C=Path(__file__).resolve().parent/'candidate.json'
def require(x,msg):
 if not x:raise RuntimeError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
require(sha(P)=='a6c378ffe706da6ccb17250c31183b0cbff7bdd2c21b85cf0fc393a73bd987b8','parent pin');require(sha(C)=='da6b88365da3ec9db6040373c25de20b30baf63edc9fdf742de2aa4b2c06e6e8','candidate pin')
p=json.loads(P.read_text());c=json.loads(C.read_text());parent=p['source'];child=c['source'];require(len(parent)==88 and len(child)==87,'gate count');inputs=p['witnesses'];ports=p['fixed_numerals'];require(c['witnesses']==inputs and c['fixed_numerals']==ports,'aliases')
def select(rows,outputs,cut=()):
 table={r[0]:r for r in rows};live=set(outputs);todo=list(outputs)
 while todo:
  x=todo.pop()
  if x in cut or x not in table:continue
  for z in table[x][2:]:
   if isinstance(z,str) and z not in live:live.add(z);todo.append(z)
 return [r for r in rows if r[0] in live and r[0] not in cut],live
def aliases(live,option):
 typ='Expr (Option (Fin 13))' if option else 'Expr (Fin 13)';out=[]
 for i,n in enumerate(inputs):
  if n in live:out.append(f'  let {n} : {typ} := .var '+(f'(some {i})' if option else str(i)))
 for i,n in enumerate(ports):
  if n in live:out.append(f'  let {n} : {typ} := .constant (p {i})')
 return out
def emit(rows):return [f'  let {n} := {a} {op} {b}' for n,op,a,b in rows]
root_names=['q3','qm','k','Bt','g31','Y'];rootrows,rootlive=select(parent,root_names);ctxrows,ctxlive=select(parent,['P13'],{'Z'});_,alllive=select(child,['P13']);require(len(alllive.intersection({r[0] for r in child}))==87,'candidate liveness')
lines=['import DiophantineConsistency.AdaptiveEquationSyntax2011','import DiophantineConsistency.AdaptiveFirstRootFactor87Context','','/-! Generated 87-row adaptive output and a shared one-hole context. -/','set_option autoImplicit false','set_option Elab.async false','set_option maxHeartbeats 8000000','noncomputable section','namespace DiophantineConsistency.AdaptiveFirstRootFactor87Literal','open DiophantineConsistency.AdaptiveFirstRootFactor87Syntax','open DiophantineConsistency.AdaptiveFirstRootFactor87Context','','structure RootInputs (σ : Type*) where','  q3 : Expr σ','  qm : Expr σ','  k : Expr σ','  bt : Expr σ','  g : Expr σ','  y : Expr σ','','def rootInputsAt (p : Fin 4 → ℤ) : RootInputs (Fin 13) :=']
lines+=aliases(rootlive,False)+emit(rootrows)+['  ⟨q3, qm, k, Bt, g31, Y⟩','','def contextAt (p : Fin 4 → ℤ) : Expr (Option (Fin 13)) :=']
lines+=aliases(ctxlive,True)+['  let Z : Expr (Option (Fin 13)) := .var none']+emit(ctxrows)+['  P13','','def expressionAt87 (p : Fin 4 → ℤ) : Expr (Fin 13) :=']
lines+=aliases(alllive,False)+emit(child)+['  P13','','theorem maintained_as_context (p : Fin 4 → ℤ) :','    AdaptiveEquationSyntax2011.expressionAt p =','      (contextAt p).subst (oldFill (rootInputsAt p).q3 (rootInputsAt p).qm','        (rootInputsAt p).k (rootInputsAt p).bt (rootInputsAt p).g (rootInputsAt p).y) := by','  rfl','','theorem candidate_as_context (p : Fin 4 → ℤ) :','    expressionAt87 p =','      (contextAt p).subst (newFill (rootInputsAt p).q3 (rootInputsAt p).qm','        (rootInputsAt p).k (rootInputsAt p).bt (rootInputsAt p).g (rootInputsAt p).y) := by','  rfl','','/-- The maintained and candidate expressions have identical split values. -/','theorem split_expression_eq {R : Type*} [CommSemiring R] (p : Fin 4 → ℤ) (v : Fin 13 → R) :','    splitEval (AdaptiveEquationSyntax2011.expressionAt p) v = splitEval (expressionAt87 p) v := by','  rw [maintained_as_context, candidate_as_context]','  exact root_context_split (contextAt p) (rootInputsAt p).q3 (rootInputsAt p).qm','    (rootInputsAt p).k (rootInputsAt p).bt (rootInputsAt p).g (rootInputsAt p).y v','','def expression87 : Expr (Fin 13) := expressionAt87 CurrentWindowCarry2011.ports','def naturalExpression87 : Expr (Fin 13) := AdaptiveEquationSyntax2011.positiveShift expression87','','/-- The actual positive-shifted equations are equivalent in every commutative semiring. -/','theorem current_natural_zero_iff {R : Type*} [CommSemiring R] (v : Fin 13 → R) :','    AdaptiveEquationSyntax2011.InternalZero AdaptiveEquationSyntax2011.naturalExpression v ↔','      AdaptiveEquationSyntax2011.InternalZero naturalExpression87 v := by','  change AdaptiveEquationSyntax2011.InternalZero','      (AdaptiveEquationSyntax2011.positiveShift AdaptiveEquationSyntax2011.expression) v ↔','    AdaptiveEquationSyntax2011.InternalZero (AdaptiveEquationSyntax2011.positiveShift expression87) v','  rw [AdaptiveEquationSyntax2011.internalZero_positiveShift,','    AdaptiveEquationSyntax2011.internalZero_positiveShift]','  change (splitEval (AdaptiveEquationSyntax2011.expressionAt CurrentWindowCarry2011.ports)','      (fun i => v i + 1)).1 =','      (splitEval (AdaptiveEquationSyntax2011.expressionAt CurrentWindowCarry2011.ports)','      (fun i => v i + 1)).2 ↔','    (splitEval (expressionAt87 CurrentWindowCarry2011.ports) (fun i => v i + 1)).1 =','      (splitEval (expressionAt87 CurrentWindowCarry2011.ports) (fun i => v i + 1)).2','  exact Iff.of_eq (congrArg (fun xy : R × R => xy.1 = xy.2)','    (split_expression_eq CurrentWindowCarry2011.ports (fun i => v i + 1)))','','end DiophantineConsistency.AdaptiveFirstRootFactor87Literal','']
path=Path(os.environ.get('ADAPTIVE_FACTOR87_LEAN_OUT',str(D/'Lean/DiophantineConsistency/AdaptiveFirstRootFactor87Literal.lean')));path.parent.mkdir(parents=True,exist_ok=True);path.write_text('\n'.join(lines));print('generated',path,'sha256',sha(path),'candidate gates',len(child),'context gates',len(ctxrows),'root gates',len(rootrows))
