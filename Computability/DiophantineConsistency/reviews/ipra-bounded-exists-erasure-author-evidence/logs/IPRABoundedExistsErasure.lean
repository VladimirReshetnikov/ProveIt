import DiophantineConsistency.IPRABoundedErasure

/-! Pure intuitionistic elimination of the outer bound existential. -/
set_option autoImplicit false
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open Rewriting
namespace DiophantineConsistency.IPRABoundedExistsErasure
open DiophantineConsistency.StrictSigmaOneInduction
open DiophantineConsistency.IPRANativeFormula
open DiophantineConsistency.IPRANativeFormulaRew
open HilbertProofᵢ DiophantineConsistency.IPRABoundedErasure

noncomputable def existsErasure {Λ : Hilbertᵢ ℒₒᵣ} (φ : ArithmeticSentence) :
    Λ ⊢! (native (Rew.emb ▹ (∃⁰ bnd φ))) 🡒 native (Rew.emb ▹ φ) := by
  have h := bndErasure (Λ := Λ) φ Fin.elim0 (&0)
  let ψ : Semipropositionᵢ ℒₒᵣ 1 := native (Rew.emb ▹ bnd φ)
  let χ : Propositionᵢ ℒₒᵣ := native (Rew.emb ▹ φ)
  have hemb : Rew.embSubsts (Fin.snoc (Fin.elim0 : Fin 0 → Term ℒₒᵣ ℕ) (&0)) =
      (Rew.free (L := ℒₒᵣ) (n := 0)).comp Rew.emb := by
    ext x
    · have hx : x = 0 := Fin.fin_one_eq_zero x
      subst x
      simp [Rew.comp_app, Fin.snoc]
    · exact Empty.elim x
  have hx : free (χ/[]) = χ := by
    have hrew : (Rew.free (L := ℒₒᵣ) (n := 0)).comp (Rew.subst ![]) = Rew.shift := by
      have hs : (Rew.subst ![] : Rew ℒₒᵣ ℕ 0 ℕ 1) = Rew.bShift := by
        ext x
        · exact Fin.elim0 x
        · simp
      rw [hs]
      exact Rew.bShift_free_eq_shift
    have he := smul_ext' (φ := χ) hrew
    rw [TransitiveRewriting.comp_app] at he
    rw [he]
    dsimp [χ]
    rw [native_rew, ← TransitiveRewriting.comp_app, Rew.shift_comp_emb]
  have hh : Λ ⊢! free ψ 🡒 χ := by
    rw [hemb, TransitiveRewriting.comp_app, ← native_rew] at h
    simpa only [Rew.embSubsts_zero] using h
  have hg : Λ ⊢! free (ψ 🡒 χ/[]) := by
    simpa only [LogicalConnective.HomClass.map_imply, hx] using hh
  have hr : Λ ⊢! (∃⁰ ψ) 🡒 χ := HilbertProofᵢ.ex₂ ψ χ ⨀ HilbertProofᵢ.gen hg
  change Λ ⊢! (∃⁰ native (Rew.emb.q ▹ bnd φ)) 🡒 χ
  rw [Rew.q_emb]
  exact hr
end DiophantineConsistency.IPRABoundedExistsErasure
