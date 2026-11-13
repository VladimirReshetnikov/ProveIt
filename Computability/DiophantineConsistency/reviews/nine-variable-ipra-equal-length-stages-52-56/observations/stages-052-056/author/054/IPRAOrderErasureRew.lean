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

theorem eraseRew_subst {ξ : Type} {n m : ℕ}
    (v : Fin n → Semiterm PRALanguage.language ξ m) :
    eraseRew (Rew.subst v) =
      Rew.subst (fun i => Semiterm.lMap termsToReference (v i)) := by
  ext x <;> simp [eraseRew, Rew.subst]

theorem eraseRew_free {n : ℕ} :
    eraseRew (Rew.free : Rew PRALanguage.language ℕ (n+1) ℕ n) = Rew.free := by
  ext x
  · refine Fin.lastCases ?_ (fun i => ?_) x <;> simp [eraseRew]
  · simp [eraseRew]

theorem eraseRew_emb {ξ : Type} {n : ℕ} :
    eraseRew (Rew.emb : Rew PRALanguage.language Empty n ξ n) = Rew.emb := by
  ext x
  · simp [eraseRew]
  · exact Empty.elim x

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

theorem erase_free {n : ℕ} (φ : Semiformulaᵢ PRALanguage.language ℕ (n+1)) :
    erase (Rewriting.free φ) = Rewriting.free (erase φ) := by
  simpa only [Rewriting.free, eraseRew_free] using
    erase_rew (Rew.free : Rew PRALanguage.language ℕ (n+1) ℕ n) φ

theorem erase_emb {ξ : Type} {n : ℕ} (φ : Semisentenceᵢ PRALanguage.language n) :
    erase (Rewriting.emb (ξ := ξ) φ) = Rewriting.emb (ξ := ξ) (erase φ) := by
  simpa only [Rewriting.emb, eraseRew_emb] using
    erase_rew (Rew.emb : Rew PRALanguage.language Empty n ξ n) φ

theorem erase_subst {ξ : Type} {n m : ℕ}
    (φ : Semiformulaᵢ PRALanguage.language ξ n)
    (v : Fin n → Semiterm PRALanguage.language ξ m) :
    erase (φ ⇜ v) = erase φ ⇜ (fun i => Semiterm.lMap termsToReference (v i)) := by
  simpa only [Rewriting.subst, eraseRew_subst] using erase_rew (Rew.subst v) φ

theorem erase_subst_zero (φ : Propositionᵢ PRALanguage.language) :
    erase (φ/[] : Semiformulaᵢ PRALanguage.language ℕ 1) =
      ((erase φ)/[] : Semiformulaᵢ IPRAEqualityOnlyReference.language ℕ 1) := by
  rw [erase_subst]
  congr 2
  funext i
  exact Fin.elim0 i

theorem erase_subst_one (φ : Semiformulaᵢ PRALanguage.language ℕ 1)
    (t : Term PRALanguage.language ℕ) :
    erase (φ/[t]) = (erase φ)/[Semiterm.lMap termsToReference t] := by
  rw [erase_subst]
  congr 2
  funext i
  refine Fin.cases ?_ (fun j => Fin.elim0 j) i
  rfl

end DiophantineConsistency.IPRAOrderErasureRew
