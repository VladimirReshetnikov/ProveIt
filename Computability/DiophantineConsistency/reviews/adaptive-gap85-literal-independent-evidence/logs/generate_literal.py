"""Generate the exact candidate and two-hole signed context in Lean."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent;C=D/'candidate.json';raw=C.read_bytes();assert hashlib.sha256(raw).hexdigest()=='c2c2e1bbb267bdc155536c5b3df9641f8faff97dab4b549a1d514d671ebdea00';j=json.loads(raw);w=j['witnesses'];ports=j['fixed_numerals'];rows=j['source'];assert len(rows)==85
def section(context):
 T='Option (Option (Fin 13))' if context else 'Fin 13'; lines=[]
 for i,n in enumerate(w):
  if context and n=='C':continue
  var=f'.var (some (some {i}))' if context else f'.var {i}'
  lines.append(f'  let {n} : Expr ({T}) := {var}')
 for i,n in enumerate(ports):lines.append(f'  let {n} : Expr ({T}) := .constant (p {i})')
 if context:lines.append(f'  let C : Expr ({T}) := .var none')
 for n,op,a,b in rows:
  if context and n in ('g44','qF'):continue
  if context and n=='G':lines.append(f'  let G : Expr ({T}) := .var (some none)')
  else:lines.append(f'  let {n} := {a} {op} {b}')
 lines.append('  P13');return '\n'.join(lines)
source='''import DiophantineConsistency.AdaptiveDirectOrdinate86Literal

/-! Generated 85-gate literal and conditional two-hole binding. The new
positive witness bound needed for an unconditional equivalence is not proved. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85Literal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context ArithmeticSignedPairs

def expressionAt85 (p : Fin 4 → ℤ) : Expr (Fin 13) :=
'''+section(False)+'''

def contextAt (p : Fin 4 → ℤ) : Expr (Option (Option (Fin 13))) :=
'''+section(True)+'''

def embed (i : Fin 13) : Fin 14 := ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
def oldLift (i : Fin 13) : Expr (Fin 14) :=
  if i = 2 then .var 13 else .var (embed i)
def newLift (i : Fin 13) : Expr (Fin 14) := .var (embed i)
def qExpr (p : Fin 4 → ℤ) : Expr (Fin 14) := 1 + .var 0 * .constant (p 0)
def qmExpr (p : Fin 4 → ℤ) : Expr (Fin 14) := .var 0 * .constant (p 0)
def oldGap (p : Fin 4 → ℤ) : Expr (Fin 14) := qExpr p - .var 1 - .var 13
def newGap : Expr (Fin 14) := .var 2
def oldRank (p : Fin 4 → ℤ) : Expr (Fin 14) := .var 13 + (qExpr p - .var 1) * qmExpr p
def newRank (p : Fin 4 → ℤ) : Expr (Fin 14) := (qExpr p - .var 1) * qExpr p - .var 2

def oldFill (p : Fin 4 → ℤ) : Option (Option (Fin 13)) → Expr (Fin 14)
  | none => oldGap p
  | some none => oldRank p
  | some (some i) => .var (embed i)
def newFill (p : Fin 4 → ℤ) : Option (Option (Fin 13)) → Expr (Fin 14)
  | none => newGap
  | some none => newRank p
  | some (some i) => .var (embed i)

theorem old_as_context (p : Fin 4 → ℤ) :
    (AdaptiveDirectOrdinate86Literal.expressionAt86 p).subst oldLift =
      (contextAt p).subst (oldFill p) := by
  rfl

theorem new_as_context (p : Fin 4 → ℤ) :
    (expressionAt85 p).subst newLift = (contextAt p).subst (newFill p) := by
  rfl

/-- The two actual literals have the same zero test when both corresponding
signed subexpressions are equivalent. No positivity bound is asserted. -/
theorem conditional_literal_zero_iff {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hg : Equivalent (splitEval (oldGap p) v) (splitEval newGap v))
    (hr : Equivalent (splitEval (oldRank p) v) (splitEval (newRank p) v)) :
    (splitEval ((AdaptiveDirectOrdinate86Literal.expressionAt86 p).subst oldLift) v).1 =
      (splitEval ((AdaptiveDirectOrdinate86Literal.expressionAt86 p).subst oldLift) v).2 ↔
    (splitEval ((expressionAt85 p).subst newLift) v).1 =
      (splitEval ((expressionAt85 p).subst newLift) v).2 := by
  rw [old_as_context,new_as_context]
  apply equivalent_zero_iff
  apply splitEval_subst_equiv
  intro i
  cases i with
  | none => exact hg
  | some j =>
    cases j with
    | none => exact hr
    | some j => exact equivalent_refl _
end DiophantineConsistency.AdaptiveGap85Literal
'''
out=D.parents[1]/'Lean/DiophantineConsistency/AdaptiveGap85Literal.lean';out.write_text(source);print('wrote',out,'candidate sha',hashlib.sha256(raw).hexdigest())
