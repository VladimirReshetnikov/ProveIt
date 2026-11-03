import DiophantineConsistency.IPRATheoryInstantiation
import DiophantineConsistency.IPRAEqualityOnlyReference

/-! Exploratory language-independent closure of uniformly instantiated proofs. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAReferenceCloseFamily
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open Rewriting HilbertProofᵢ
open DiophantineConsistency.IPRATheoryHilbertBridge

variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L}

def closeFamily (T : Theoryᵢ L Λ) : ∀ (n : ℕ) (φ : Semisentenceᵢ L n),
    (∀ v : Fin n → Term L ℕ, extended T ⊢! Rew.embSubsts v ▹ φ) →
    T ⊢! ∀⁰* φ
  | 0, φ, h => by
    have hp := h Fin.elim0
    have hr : (Rew.embSubsts (Fin.elim0 : Fin 0 → Term L ℕ)) = (Rew.emb : Rew L Empty 0 ℕ 0) := by
      ext i
      · exact Fin.elim0 i
      · exact Empty.elim i
    rw [hr] at hp
    apply extendedToTheory T
    simpa only [allClosure_zero, Rewriting.emb] using hp
  | n+1, φ, h => by
    have hh (v : Fin n → Term L ℕ) : extended T ⊢! Rew.embSubsts v ▹ (∀⁰ φ) := by
      apply HilbertProofᵢ.gen
      have hp := h (Fin.cases (&0) (fun i => Rew.shift (v i)))
      have hr : (Rew.free : Rew L ℕ 1 ℕ 0).comp (Rew.embSubsts v).q =
          Rew.embSubsts (Fin.cases (&0) (fun i => Rew.shift (v i))) := by
        ext i
        · cases i using Fin.cases with
          | zero => simp [Rew.comp_app]
          | succ j => simp [Rew.comp_app, Rew.free_bShift_app]
        · exact Empty.elim i
      change extended T ⊢! Rew.free ▹ ((Rew.embSubsts v).q ▹ φ)
      rw [← TransitiveRewriting.comp_app, hr]
      exact hp
    have hc := closeFamily T n (∀⁰ φ) hh
    simpa only [allClosure_succ] using hc

end DiophantineConsistency.IPRAReferenceCloseFamily
