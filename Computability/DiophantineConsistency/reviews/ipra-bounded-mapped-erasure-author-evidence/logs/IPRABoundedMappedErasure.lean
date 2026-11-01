import DiophantineConsistency.StrictSigmaOneInduction
import DiophantineConsistency.IPRANativeFormulaRew
import DiophantineConsistency.IPRABoundedErasureLogic
/-! Constructive structural and outer existential bound erasure under any language map.
No arithmetic axiom or bounded-formula decidability is used. -/
set_option autoImplicit false
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open Rewriting
namespace DiophantineConsistency.IPRABoundedMappedErasure
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
end DiophantineConsistency.IPRABoundedMappedErasure

namespace DiophantineConsistency.IPRABoundedMappedErasure
open DiophantineConsistency.StrictSigmaOneInduction
open DiophantineConsistency.IPRANativeFormula
open DiophantineConsistency.IPRANativeFormulaRew
open DiophantineConsistency.IPRABoundedErasureLogic
open HilbertProofᵢ
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L}

/-- Erase every guard introduced by `bnd`, under any term valuation and bound.
This derives an object-level intuitionistic proof, for any Hilbert axiom set. -/
noncomputable def bndErasure (f : ℒₒᵣ →ᵥ L) {n : ℕ} (φ : ArithmeticSemisentence n)
    (e : Fin n → Term ℒₒᵣ ℕ) (b : Term ℒₒᵣ ℕ) :
    Λ ⊢! native (Semiformula.lMap f (Rew.embSubsts (Fin.snoc e b) ▹ bnd φ)) 🡒
      native (Semiformula.lMap f (Rew.embSubsts e ▹ φ)) := by
  induction φ generalizing b with
  | verum => change Λ ⊢! (⊤ : Propositionᵢ L) 🡒 ⊤; exact Entailment.C_id
  | falsum => change Λ ⊢! (⊥ : Propositionᵢ L) 🡒 ⊥; exact Entailment.C_id
  | rel r v =>
    simp only [bnd, ← TransitiveRewriting.comp_app, embed_cast_last]
    exact Entailment.C_id
  | nrel r v =>
    simp only [bnd, ← TransitiveRewriting.comp_app, embed_cast_last]
    exact Entailment.C_id
  | and φ ψ ihφ ihψ =>
    exact eraseAnd (ihφ e b) (ihψ e b)
  | or φ ψ ihφ ihψ =>
    exact eraseOr (ihφ e b) (ihψ e b)
  | all φ ih =>
    simp only [bnd]
    apply eraseAll
    change Λ ⊢! (Rew.free ▹ native (Semiformula.lMap f ((Rew.embSubsts (Fin.snoc e b)).q ▹ bnd φ))) 🡒
      (Rew.free ▹ native (Semiformula.lMap f ((Rew.embSubsts e).q ▹ φ)))
    rw [native_rew, native_rew, ← Semiformula.lMap_free, ← Semiformula.lMap_free, ← TransitiveRewriting.comp_app,
      ← TransitiveRewriting.comp_app, open_embed, open_embed]
    rw [Fin.comp_snoc, DiophantineConsistency.StrictSigmaOneInduction.cons_snoc]
    exact ih ((&0) :> (Rew.shift ∘ e)) (Rew.shift b)
  | exs φ ih =>
    simp only [bnd, FirstOrder.bexs]
    apply eraseGuardedEx
    change Λ ⊢! (Rew.free ▹ native (Semiformula.lMap f ((Rew.embSubsts (Fin.snoc e b)).q ▹ bnd φ))) 🡒
      (Rew.free ▹ native (Semiformula.lMap f ((Rew.embSubsts e).q ▹ φ)))
    rw [native_rew, native_rew, ← Semiformula.lMap_free, ← Semiformula.lMap_free, ← TransitiveRewriting.comp_app,
      ← TransitiveRewriting.comp_app, open_embed, open_embed]
    rw [Fin.comp_snoc, DiophantineConsistency.StrictSigmaOneInduction.cons_snoc]
    exact ih ((&0) :> (Rew.shift ∘ e)) (Rew.shift b)
end DiophantineConsistency.IPRABoundedMappedErasure

namespace DiophantineConsistency.IPRABoundedMappedErasure
open DiophantineConsistency.StrictSigmaOneInduction DiophantineConsistency.IPRANativeFormula DiophantineConsistency.IPRANativeFormulaRew HilbertProofᵢ
/-- Erase the outer bound existential after any such language map. -/
noncomputable def existsErasure {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L} (f : ℒₒᵣ →ᵥ L) (φ : ArithmeticSentence) :
    Λ ⊢! (native (Semiformula.lMap f (Rew.emb ▹ (∃⁰ bnd φ)))) 🡒 native (Semiformula.lMap f (Rew.emb ▹ φ)) := by
  have h := bndErasure (Λ := Λ) f φ Fin.elim0 (&0)
  let ψ : Semipropositionᵢ L 1 := native (Semiformula.lMap f (Rew.emb ▹ bnd φ))
  let χ : Propositionᵢ L := native (Semiformula.lMap f (Rew.emb ▹ φ))
  have hemb : Rew.embSubsts (Fin.snoc (Fin.elim0 : Fin 0 → Term ℒₒᵣ ℕ) (&0)) =
      (Rew.free (L := ℒₒᵣ) (n := 0)).comp Rew.emb := by
    ext x
    · have hx : x = 0 := Fin.fin_one_eq_zero x
      subst x
      simp [Rew.comp_app, Fin.snoc]
    · exact Empty.elim x
  have hx : free (χ/[]) = χ := by
    have hrew : (Rew.free (L := L) (n := 0)).comp (Rew.subst ![]) = Rew.shift := by
      have hs : (Rew.subst ![] : Rew L ℕ 0 ℕ 1) = Rew.bShift := by
        ext x
        · exact Fin.elim0 x
        · simp
      rw [hs]
      exact Rew.bShift_free_eq_shift
    have he := smul_ext' (φ := χ) hrew
    rw [TransitiveRewriting.comp_app] at he
    rw [he]
    dsimp [χ]
    rw [native_rew, ← Semiformula.lMap_shift, ← TransitiveRewriting.comp_app, Rew.shift_comp_emb]
  have hh : Λ ⊢! free ψ 🡒 χ := by
    rw [hemb, TransitiveRewriting.comp_app, Semiformula.lMap_free, ← native_rew] at h
    simpa only [Rew.embSubsts_zero] using h
  have hg : Λ ⊢! free (ψ 🡒 χ/[]) := by
    simpa only [LogicalConnective.HomClass.map_imply, hx] using hh
  have hr : Λ ⊢! (∃⁰ ψ) 🡒 χ := HilbertProofᵢ.ex₂ ψ χ ⨀ HilbertProofᵢ.gen hg
  change Λ ⊢! (∃⁰ native (Semiformula.lMap f (Rew.emb.q ▹ bnd φ))) 🡒 χ
  rw [Rew.q_emb]
  exact hr
end DiophantineConsistency.IPRABoundedMappedErasure
