import DiophantineConsistency.IPRATheoryHilbertBridge
import Foundation.FirstOrder.Intuitionistic.Deduction
set_option autoImplicit false
namespace DiophantineConsistency.IPRATheoryInstantiation
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open Rewriting HilbertProofᵢ
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L}

noncomputable def allInst : {n : ℕ} → (φ : Semipropositionᵢ L n) →
    (v : Fin n → Term L ℕ) → Λ ⊢! (∀⁰* φ) 🡒 (Rew.subst v ▹ φ)
  | 0, φ, v => by
    have hv : (Rew.subst v : Rew L ℕ 0 ℕ 0) = Rew.id := by
      ext x
      · exact Fin.elim0 x
      · simp
    simpa only [allClosure_zero, hv, ReflectiveRewriting.id_app] using
      (Entailment.C_id (φ := φ))
  | n+1, φ, v => by
    have hfirst := allInst (∀⁰ φ) (v ∘ Fin.succ)
    have hlast := HilbertProofᵢ.all₁ (Λ := Λ) ((Rew.subst (v ∘ Fin.succ)).q ▹ φ) (v 0)
    have hrew : (Rew.subst ![v 0]).comp (Rew.subst (v ∘ Fin.succ)).q = Rew.subst v := by
      ext x
      · cases x using Fin.cases <;> simp [Rew.comp_app, Rew.q_subst]
      · simp [Rew.comp_app, Rew.q_subst]
    have hh := Entailment.C_trans hfirst hlast
    simpa only [allClosure_succ, Rewriting.app_all, ← TransitiveRewriting.comp_app, hrew] using hh
end DiophantineConsistency.IPRATheoryInstantiation

namespace DiophantineConsistency.IPRATheoryInstantiation
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open Rewriting HilbertProofᵢ
open DiophantineConsistency.IPRATheoryHilbertBridge
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L} {T : Theoryᵢ L Λ}

noncomputable def instantiateTheory {n : ℕ} (φ : Semisentenceᵢ L n)
    (h : T ⊢! ∀⁰* φ) (v : Fin n → Term L ℕ) :
    extended T ⊢! (Rew.embSubsts v ▹ φ) := by
  have hc : extended T ⊢! ∀⁰* (Rew.emb ▹ φ) := by
    simpa only [Rewriting.emb_allClosure] using theoryToExtended T h
  have hi := (allInst (Λ := extended T) (Rew.emb ▹ φ) v) ⨀ hc
  have he : (Rew.subst v).comp Rew.emb = Rew.embSubsts v := by
    ext x
    · simp [Rew.comp_app]
    · exact Empty.elim x
  simpa only [← TransitiveRewriting.comp_app, he] using hi
end DiophantineConsistency.IPRATheoryInstantiation
