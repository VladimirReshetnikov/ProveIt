import DiophantineConsistency.StrictSigmaOneInduction
import DiophantineConsistency.IPRANativeFormulaRew
import DiophantineConsistency.IPRABoundedErasureLogic
/-! Constructive structural erasure of existential bounds in a closed NNF formula.
No arithmetic axiom or bounded-formula decidability is used. -/
set_option autoImplicit false
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open Rewriting
namespace DiophantineConsistency.IPRABoundedErasure
variable {L : Language}

theorem embed_cast_last {n : ℕ} (e : Fin n → Term L ℕ) (b : Term L ℕ) :
    (Rew.embSubsts (Fin.snoc e b)).comp (Rew.castLE (Nat.le_succ n)) = Rew.embSubsts e := by
  ext x
  · rw [Rew.comp_app]
    simp only [Rew.castLe_bvar, Rew.embSubsts_bvar]
    exact congrArg (fun f => f x) (DiophantineConsistency.StrictSigmaOneInduction.snoc_castLE e b)
  · exact Empty.elim x
theorem open_embed {n : ℕ} (e : Fin n → Term L ℕ) :
    (Rew.free (L := L) (n := 0)).comp (Rew.embSubsts e).q =
      Rew.embSubsts ((&0) :> (Rew.shift ∘ e)) := by
  ext x
  · cases x using Fin.cases <;> simp [Rew.comp_app, Rew.q_embSubsts]
  · exact Empty.elim x
end DiophantineConsistency.IPRABoundedErasure

namespace DiophantineConsistency.IPRABoundedErasure
open DiophantineConsistency.StrictSigmaOneInduction
open DiophantineConsistency.IPRANativeFormula
open DiophantineConsistency.IPRANativeFormulaRew
open DiophantineConsistency.IPRABoundedErasureLogic
open HilbertProofᵢ
variable {Λ : Hilbertᵢ ℒₒᵣ}

/-- Erase every guard introduced by `bnd`, under any term valuation and bound.
This derives an object-level intuitionistic proof, for any Hilbert axiom set. -/
noncomputable def bndErasure {n : ℕ} (φ : ArithmeticSemisentence n)
    (e : Fin n → Term ℒₒᵣ ℕ) (b : Term ℒₒᵣ ℕ) :
    Λ ⊢! native (Rew.embSubsts (Fin.snoc e b) ▹ bnd φ) 🡒
      native (Rew.embSubsts e ▹ φ) := by
  induction φ generalizing b with
  | verum => change Λ ⊢! (⊤ : Propositionᵢ ℒₒᵣ) 🡒 ⊤; exact Entailment.C_id
  | falsum => change Λ ⊢! (⊥ : Propositionᵢ ℒₒᵣ) 🡒 ⊥; exact Entailment.C_id
  | rel r v | nrel r v =>
    simp only [bnd, ← TransitiveRewriting.comp_app, embed_cast_last]
    exact Entailment.C_id
  | and φ ψ ihφ ihψ =>
    exact eraseAnd (ihφ e b) (ihψ e b)
  | or φ ψ ihφ ihψ =>
    exact eraseOr (ihφ e b) (ihψ e b)
  | all φ ih | exs φ ih =>
    simp only [bnd, FirstOrder.bexs]
    first | apply eraseAll | apply eraseGuardedEx
    change Λ ⊢! (Rew.free ▹ native ((Rew.embSubsts (Fin.snoc e b)).q ▹ bnd φ)) 🡒
      (Rew.free ▹ native ((Rew.embSubsts e).q ▹ φ))
    rw [native_rew, native_rew, ← TransitiveRewriting.comp_app,
      ← TransitiveRewriting.comp_app, open_embed, open_embed]
    rw [Fin.comp_snoc, DiophantineConsistency.StrictSigmaOneInduction.cons_snoc]
    exact ih ((&0) :> (Rew.shift ∘ e)) (Rew.shift b)
end DiophantineConsistency.IPRABoundedErasure
