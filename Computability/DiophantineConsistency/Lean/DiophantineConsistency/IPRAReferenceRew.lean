import DiophantineConsistency.IPRAOrderErasure

/-! Preliminary rewriting compatibility for the equality-only embedding. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAReferenceRew
open LO LO.FirstOrder IPRAOrderErasure
open scoped LO.FirstOrder
variable {ξ₁ ξ₂ : Type} {n₁ n₂ : ℕ}

def embedRew (ω : Rew IPRAEqualityOnlyReference.language ξ₁ n₁ ξ₂ n₂) :
    Rew PRALanguage.language ξ₁ n₁ ξ₂ n₂ :=
  Rew.bind (fun i => Semiterm.lMap toNative (ω (.bvar i)))
    (fun x => Semiterm.lMap toNative (ω (.fvar x)))

theorem embed_term_rew (ω : Rew IPRAEqualityOnlyReference.language ξ₁ n₁ ξ₂ n₂)
    (t : Semiterm IPRAEqualityOnlyReference.language ξ₁ n₁) :
    Semiterm.lMap toNative (ω t) = embedRew ω (Semiterm.lMap toNative t) := by
  induction t with
  | bvar i => rfl
  | fvar i => rfl
  | func f v ih =>
    simp only [Rew.func, Semiterm.lMap_func, toNative, Function.comp_def]
    congr 1
    funext i
    exact ih i

theorem embedRew_q (ω : Rew IPRAEqualityOnlyReference.language ξ₁ n₁ ξ₂ n₂) :
    embedRew ω.q = (embedRew ω).q := by
  ext x
  · refine Fin.cases ?_ (fun i => ?_) x
    · rfl
    · simp [embedRew, Rew.q, Semiterm.lMap_bShift, Function.comp_def]
  · simp [embedRew, Rew.q, Semiterm.lMap_bShift, Function.comp_def]

theorem embedRew_subst {ξ : Type} {n m : ℕ}
    (v : Fin n → Semiterm IPRAEqualityOnlyReference.language ξ m) :
    embedRew (Rew.subst v) =
      Rew.subst (fun i => Semiterm.lMap toNative (v i)) := by
  ext x <;> simp [embedRew, Rew.subst]

theorem embedRew_free {n : ℕ} :
    embedRew (Rew.free : Rew IPRAEqualityOnlyReference.language ℕ (n+1) ℕ n) = Rew.free := by
  ext x
  · refine Fin.lastCases ?_ (fun i => ?_) x <;> simp [embedRew]
  · simp [embedRew]

theorem embedRew_emb {ξ : Type} {n : ℕ} :
    embedRew (Rew.emb : Rew IPRAEqualityOnlyReference.language Empty n ξ n) = Rew.emb := by
  ext x
  · simp [embedRew]
  · exact Empty.elim x

theorem embed_rew (ω : Rew IPRAEqualityOnlyReference.language ξ₁ n₁ ξ₂ n₂)
    (φ : Semiformulaᵢ IPRAEqualityOnlyReference.language ξ₁ n₁) :
    embed (ω ▹ φ) = embedRew ω ▹ embed φ := by
  change embed (Semiformulaᵢ.rewAux ω φ) = Semiformulaᵢ.rewAux (embedRew ω) (embed φ)
  induction φ using Semiformulaᵢ.rec' generalizing n₂ <;>
    simp [embed, Semiformulaᵢ.rewAux, ← embedRew_q, *, Function.comp_def]
  case hRel r v =>
    cases r
    simp [embed, Semiformulaᵢ.rewAux, embed_term_rew, Function.comp_def]
  all_goals rfl

theorem embed_free {n : ℕ}
    (φ : Semiformulaᵢ IPRAEqualityOnlyReference.language ℕ (n+1)) :
    embed (Rewriting.free φ) = Rewriting.free (embed φ) := by
  simpa only [Rewriting.free, embedRew_free] using
    embed_rew (Rew.free : Rew IPRAEqualityOnlyReference.language ℕ (n+1) ℕ n) φ

theorem embed_emb {ξ : Type} {n : ℕ}
    (φ : Semisentenceᵢ IPRAEqualityOnlyReference.language n) :
    embed (Rewriting.emb (ξ := ξ) φ) = Rewriting.emb (ξ := ξ) (embed φ) := by
  simpa only [Rewriting.emb, embedRew_emb] using
    embed_rew (Rew.emb : Rew IPRAEqualityOnlyReference.language Empty n ξ n) φ

theorem embed_subst {ξ : Type} {n m : ℕ}
    (φ : Semiformulaᵢ IPRAEqualityOnlyReference.language ξ n)
    (v : Fin n → Semiterm IPRAEqualityOnlyReference.language ξ m) :
    embed (φ ⇜ v) = embed φ ⇜ (fun i => Semiterm.lMap toNative (v i)) := by
  simpa only [Rewriting.subst, embedRew_subst] using embed_rew (Rew.subst v) φ

theorem embed_subst_zero (φ : Propositionᵢ IPRAEqualityOnlyReference.language) :
    embed (φ/[] : Semiformulaᵢ IPRAEqualityOnlyReference.language ℕ 1) =
      ((embed φ)/[] : Semiformulaᵢ PRALanguage.language ℕ 1) := by
  rw [embed_subst]
  congr 2
  funext i
  exact Fin.elim0 i

theorem embed_subst_one (φ : Semiformulaᵢ IPRAEqualityOnlyReference.language ℕ 1)
    (t : Term IPRAEqualityOnlyReference.language ℕ) :
    embed (φ/[t]) = (embed φ)/[Semiterm.lMap toNative t] := by
  rw [embed_subst]
  congr 2
  funext i
  refine Fin.cases ?_ (fun j => Fin.elim0 j) i
  rfl

theorem embed_preserves_open {ξ : Type} {n : ℕ}
    (φ : Semiformulaᵢ IPRAEqualityOnlyReference.language ξ n) :
    IPRAQuantifierFree.OpenI φ → IPRAQuantifierFree.OpenI (embed φ) := by
  induction φ with
  | falsum => simp [embed, IPRAQuantifierFree.OpenI]
  | rel r v => cases r; simp [embed, IPRAQuantifierFree.OpenI]
  | and φ ψ ihφ ihψ => simp only [embed, IPRAQuantifierFree.OpenI]; exact fun h => ⟨ihφ h.1, ihψ h.2⟩
  | or φ ψ ihφ ihψ => simp only [embed, IPRAQuantifierFree.OpenI]; exact fun h => ⟨ihφ h.1, ihψ h.2⟩
  | imp φ ψ ihφ ihψ => simp only [embed, IPRAQuantifierFree.OpenI]; exact fun h => ⟨ihφ h.1, ihψ h.2⟩
  | all φ ih => simp [IPRAQuantifierFree.OpenI]
  | exs φ ih => simp [IPRAQuantifierFree.OpenI]

end DiophantineConsistency.IPRAReferenceRew
