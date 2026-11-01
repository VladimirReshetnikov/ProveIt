import DiophantineConsistency.IPRAOrderErasure

/-! Preliminary rewriting compatibility for the equality-only erasure. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAOrderErasureRew
open LO LO.FirstOrder IPRAOrderErasure
open scoped LO.FirstOrder
variable {ξ₁ ξ₂ : Type} {n₁ n₂ : ℕ}

def eraseRew (ω : Rew PRALanguage.language ξ₁ n₁ ξ₂ n₂) :
    Rew IPRAEqualityOnlyReference.language ξ₁ n₁ ξ₂ n₂ :=
  Rew.bind (fun i => Semiterm.lMap termsToReference (ω (.bvar i)))
    (fun x => Semiterm.lMap termsToReference (ω (.fvar x)))

theorem erase_term_rew (ω : Rew PRALanguage.language ξ₁ n₁ ξ₂ n₂)
    (t : Semiterm PRALanguage.language ξ₁ n₁) :
    Semiterm.lMap termsToReference (ω t) = eraseRew ω (Semiterm.lMap termsToReference t) := by
  induction t with
  | bvar i => rfl
  | fvar i => rfl
  | func f v ih =>
    simp only [Rew.func, Semiterm.lMap_func, termsToReference, Function.comp_def]
    congr 1
    funext i
    exact ih i

theorem eraseRew_q (ω : Rew PRALanguage.language ξ₁ n₁ ξ₂ n₂) :
    eraseRew ω.q = (eraseRew ω).q := by
  ext x
  · refine Fin.cases ?_ (fun i => ?_) x
    · rfl
    · simp [eraseRew, Rew.q, Semiterm.lMap_bShift, Function.comp_def]
  · simp [eraseRew, Rew.q, Semiterm.lMap_bShift, Function.comp_def]

theorem erase_rew (ω : Rew PRALanguage.language ξ₁ n₁ ξ₂ n₂)
    (φ : Semiformulaᵢ PRALanguage.language ξ₁ n₁) :
    erase (ω ▹ φ) = eraseRew ω ▹ erase φ := by
  change erase (Semiformulaᵢ.rewAux ω φ) = Semiformulaᵢ.rewAux (eraseRew ω) (erase φ)
  induction φ using Semiformulaᵢ.rec' generalizing n₂ <;>
    simp [erase, Semiformulaᵢ.rewAux, ← eraseRew_q, *, Function.comp_def]
  case hRel r v =>
    cases r <;> simp [erase, Semiformulaᵢ.rewAux, erase_term_rew, Function.comp_def]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Rew.func, Function.comp_def]
    · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
      simp [Rew.func, Function.comp_def]
      funext x
      exact Fin.elim0 x
  all_goals rfl

end DiophantineConsistency.IPRAOrderErasureRew
