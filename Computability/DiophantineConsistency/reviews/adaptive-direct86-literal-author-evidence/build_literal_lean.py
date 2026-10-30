"""Generate 86-row literal and common one-hole squared-ordinate context."""
from pathlib import Path
import hashlib,json,os
D=Path(__file__).resolve().parents[2];P=D/'research/adaptive-first-root-factor87/candidate.json';C=Path(__file__).resolve().parent/'candidate.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def require(x,m):
 if not x:raise RuntimeError(m)
require(sha(P)=='da6b88365da3ec9db6040373c25de20b30baf63edc9fdf742de2aa4b2c06e6e8','parent pin');require(sha(C)=='e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f','candidate pin')
p=json.loads(P.read_text());c=json.loads(C.read_text());old=p['source'];new=c['source'];inputs=c['witnesses'];ports=c['fixed_numerals'];require(len(old)==87 and len(new)==86,'row count')
def select(rows,outputs,cut=()):
 table={x[0]:x for x in rows};live=set(outputs);todo=list(outputs)
 while todo:
  x=todo.pop()
  if x in cut or x not in table:continue
  for z in table[x][2:]:
   if isinstance(z,str) and z not in live:live.add(z);todo.append(z)
 return [r for r in rows if r[0] in live and r[0] not in cut],live
def aliases(live,typ,option=False):
 out=[]
 for i,n in enumerate(inputs):
  if n in live:out.append(f'  let {n} : {typ} := .var '+(f'(some {i})' if option else str(i)))
 for i,n in enumerate(ports):
  if n in live:out.append(f'  let {n} : {typ} := .constant (p {i})')
 return out
def emit(rows):return [f'  let {n} := {a} {op} {b}' for n,op,a,b in rows]
ctx,ctxlive=select(old,['P13'],{'y2'});vrows,vlive=select(old,['V']);_,nlive=select(new,['P13']);require('u' not in ctxlive and 'u' not in vlive,'unexpected old-offset dependency');require(len(nlive.intersection({r[0] for r in new}))==86,'candidate liveness')
lines=['import DiophantineConsistency.AdaptiveFirstRootFactor87Literal','import DiophantineConsistency.AdaptiveDirectOrdinate86Context','','/-! Generated direct-ordinate literal and conditional one-hole binding. -/','set_option autoImplicit false','set_option Elab.async false','set_option maxHeartbeats 8000000','noncomputable section','namespace DiophantineConsistency.AdaptiveDirectOrdinate86Literal','open LO LO.FirstOrder LO.FirstOrder.Arithmetic','open scoped LO.FirstOrder.Arithmetic','open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context ArithmeticSignedPairs','','def expressionAt86 (p : Fin 4 → ℤ) : Expr (Fin 13) :=']
lines+=aliases(nlive,'Expr (Fin 13)')+emit(new)+['  P13','','def contextAt (p : Fin 4 → ℤ) : Expr (Option (Fin 13)) :=']
lines+=aliases(ctxlive,'Expr (Option (Fin 13))',True)+['  let y2 : Expr (Option (Fin 13)) := .var none']+emit(ctx)+['  P13','','def signedV (p : Fin 4 → ℤ) : Expr (Fin 14) :=']
lines+=aliases(vlive,'Expr (Fin 14)')+emit(vrows)+['  V','','def embed (i : Fin 13) : Fin 14 := ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩','def oldLift (i : Fin 13) : Expr (Fin 14) :=','  if i = 11 then .var 13 else .var (embed i)','def newLift (i : Fin 13) : Expr (Fin 14) := .var (embed i)','def fill (e : Expr (Fin 14)) : Option (Fin 13) → Expr (Fin 14)','  | none => e','  | some i => .var (embed i)','','def oldSquare (p : Fin 4 → ℤ) : Expr (Fin 14) :=','  let y := signedV p + .var 13','  y*y','def newSquare : Expr (Fin 14) :=','  let y : Expr (Fin 14) := .var 11','  y*y','','theorem old_as_context (p : Fin 4 → ℤ) :','    (AdaptiveFirstRootFactor87Literal.expressionAt87 p).subst oldLift =','      (contextAt p).subst (fill (oldSquare p)) := by','  rfl','','theorem new_as_context (p : Fin 4 → ℤ) :','    (expressionAt86 p).subst newLift =','      (contextAt p).subst (fill newSquare) := by','  rfl','','/-- With equivalent squared ordinates, the actual literal zero tests agree. -/','theorem conditional_literal_zero_iff {V : Type*} [ORingStructure V]','    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (p : Fin 4 → ℤ) (v : Fin 14 → V)','    (h : Equivalent (splitEval (oldSquare p) v) (splitEval newSquare v)) :','    (splitEval ((AdaptiveFirstRootFactor87Literal.expressionAt87 p).subst oldLift) v).1 =','      (splitEval ((AdaptiveFirstRootFactor87Literal.expressionAt87 p).subst oldLift) v).2 ↔','    (splitEval ((expressionAt86 p).subst newLift) v).1 =','      (splitEval ((expressionAt86 p).subst newLift) v).2 := by','  rw [old_as_context,new_as_context]','  apply equivalent_zero_iff','  apply splitEval_subst_equiv','  intro i','  cases i with','  | none => exact h','  | some i => exact equivalent_refl _','','def expression86 : Expr (Fin 13) := expressionAt86 CurrentWindowCarry2011.ports','def naturalExpression86 : Expr (Fin 13) := AdaptiveEquationSyntax2011.positiveShift expression86','','end DiophantineConsistency.AdaptiveDirectOrdinate86Literal','']
out=Path(os.environ.get('ADAPTIVE_DIRECT86_LEAN_OUT',str(D/'Lean/DiophantineConsistency/AdaptiveDirectOrdinate86Literal.lean')));out.parent.mkdir(parents=True,exist_ok=True);out.write_text('\n'.join(lines));print('generated',out,'sha256',sha(out),'candidate gates',len(new),'context gates',len(ctx),'signed-V gates',len(vrows))
