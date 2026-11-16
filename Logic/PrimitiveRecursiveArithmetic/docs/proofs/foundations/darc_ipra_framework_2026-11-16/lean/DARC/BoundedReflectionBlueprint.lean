import DARC.StructuralKernel
import IPRADerivations.Core.MultiSums

/-! Blueprint: specialize a fixed bounded formula to primitive-recursive bits. -/
namespace LeanProofs.IPRA.DARC

open LeanProofs.ConciseIPRA LeanProofs.IPRA Syn
open scoped Fm

/-- Syntax is metalevel and finite.  Atomic relations are already accompanied
by a primitive-recursive characteristic symbol and an object-level reflection
proof. -/
inductive BoundedFormula (n : ℕ)
  | atom (bit : PR n) (meaning : Fm PTm n)
  | and (p q : BoundedFormula n)
  | or (p q : BoundedFormula n)
  | imp (p q : BoundedFormula n)
  | allLt (bound : PTm n) (body : BoundedFormula (n + 1))
  | exLt (bound : PTm n) (body : BoundedFormula (n + 1))

/-- Generated truth bit for one fixed formula. -/
def BoundedFormula.bit : BoundedFormula n → PR n := by
  intro p
  induction p with
  | atom b _ => exact b
  | and _ _ bp bq => exact .comp Sym.mul ![bp, bq]
  | or _ _ bp bq => exact .comp sg ![.comp Sym.add ![bp, bq]]
  | imp _ _ bp bq =>
      exact .comp sg ![.comp Sym.add ![.comp Sym.rsub ![bp, oneF], bq]]
  | allLt bound body ih => exact allFoldCode bound ih
  | exLt bound body ih => exact anyFoldCode bound ih

/-- The object formula denoted by the fixed bounded syntax. -/
def BoundedFormula.denote : BoundedFormula n → Fm PTm n := by
  intro p
  induction p with
  | atom _ A => exact A
  | and _ _ P Q => exact P ⋏ Q
  | or _ _ P Q => exact P ⋎ Q
  | imp _ _ P Q => exact P ⟶ Q
  | allLt b _ B => exact boundedAll b B
  | exLt b _ B => exact boundedEx b B

/-- Reflection from generated bit to the original bounded formula.  The atom
case is supplied by the client; all other cases are syntax-directed finite
folds. -/
theorem reflect (p : BoundedFormula n)
    (atomReflect : ∀ bit A, p.HasAtom bit A →
      ([] : List (Fm PTm n)) ⊢[PRAAx] Fm.iff (app bit var ≐ num 1) A) :
    ([] : List (Fm PTm n)) ⊢[PRAAx]
      Fm.iff (app p.bit var ≐ num 1) p.denote := by
  sorry

/-- Positive/negative strategy certificates are primitive recursive for a
fixed bounded formula. -/
theorem strategy_sound (p : BoundedFormula n) :
    ([] : List (Fm PTm n)) ⊢[PRAAx]
      Fm.iff (strategyAccept p (strategyBuild p) var ≐ num 1) p.denote := by
  sorry

end LeanProofs.IPRA.DARC
