import ZFCinPA.QTemplate
import ZFCinPA.QInterp

set_option autoImplicit false
noncomputable section

/-!
# The WF interpretation commutes with template translation

`intT` is the meta-level WF interpretation over an enlarged template
language: `ℒₛₑₜ` atoms become the lifted bisimilarity/membership formulas
`eqS`/`memS`, quantifiers are guarded by the lifted domain `domS`, and
placeholder atoms are kept. `interp_translate` is the bridge at internal
codes:

`interp PN (translateFormula Ks φ) = translateFormula (IK ∘ Ks) (intT φ)`,

where `IK K` is the internal interpretation of the placeholder meaning `K`.
Every internal code identity needed for Separation, Replacement and the
congruence laws (`sepBody`, `repBody` and `congruenceFormula` are template
translations) then follows from this single lemma.
-/

namespace LeanProofs.ZFCinPA.QTInterp

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.QInterp

variable {k : ℕ} {arities : Fin k → ℕ}

/-! ## The meta interpretation over a template language -/

section Meta

variable {ξ : Type*}

/-- The meaning of an `ℒₛₑₜ` atom. -/
def atomT {n m : ℕ} : (ℒₛₑₜ).Rel m → (Fin m → Semiterm (setTemplateLanguage k arities) ξ n) →
    Semiformula (setTemplateLanguage k arities) ξ n
  | .eq, v => Rew.embSubsts v ▹ liftSet eqS
  | .mem, v => Rew.embSubsts v ▹ liftSet memS

/-- The domain guard at the newest bound variable. -/
def domT (n : ℕ) : Semiformula (setTemplateLanguage k arities) ξ (n + 1) :=
  Rew.embSubsts ![#0] ▹ liftSet domS

/-- The WF interpretation of a template formula. -/
def intT : {n : ℕ} → Semiformula (setTemplateLanguage k arities) ξ n →
    Semiformula (setTemplateLanguage k arities) ξ n
  | _, .rel (Sum.inl R) v => atomT R v
  | _, .rel (Sum.inr r) v => .rel (Sum.inr r) v
  | _, .nrel (Sum.inl R) v => ∼atomT R v
  | _, .nrel (Sum.inr r) v => .nrel (Sum.inr r) v
  | _, ⊤ => ⊤
  | _, ⊥ => ⊥
  | _, φ ⋏ ψ => intT φ ⋏ intT ψ
  | _, φ ⋎ ψ => intT φ ⋎ intT ψ
  | n, ∀⁰ φ => ∀⁰ (∼domT n ⋎ intT φ)
  | n, ∃⁰ φ => ∃⁰ (domT n ⋏ intT φ)

@[simp] lemma intT_rel_inl {n m : ℕ} (R : (ℒₛₑₜ).Rel m)
    (v : Fin m → Semiterm (setTemplateLanguage k arities) ξ n) :
    intT (.rel (Sum.inl R) v) = atomT R v := rfl
@[simp] lemma intT_rel_inr {n m : ℕ} (r : (multiPlaceholderLanguage k arities).Rel m)
    (v : Fin m → Semiterm (setTemplateLanguage k arities) ξ n) :
    intT (.rel (L := setTemplateLanguage k arities) (Sum.inr r) v) = .rel (Sum.inr r) v := rfl
@[simp] lemma intT_nrel_inl {n m : ℕ} (R : (ℒₛₑₜ).Rel m)
    (v : Fin m → Semiterm (setTemplateLanguage k arities) ξ n) :
    intT (.nrel (Sum.inl R) v) = ∼atomT R v := rfl
@[simp] lemma intT_nrel_inr {n m : ℕ} (r : (multiPlaceholderLanguage k arities).Rel m)
    (v : Fin m → Semiterm (setTemplateLanguage k arities) ξ n) :
    intT (.nrel (L := setTemplateLanguage k arities) (Sum.inr r) v) = .nrel (Sum.inr r) v := rfl
@[simp] lemma intT_verum {n : ℕ} : intT (⊤ : Semiformula (setTemplateLanguage k arities) ξ n) = ⊤ := rfl
@[simp] lemma intT_falsum {n : ℕ} : intT (⊥ : Semiformula (setTemplateLanguage k arities) ξ n) = ⊥ := rfl
@[simp] lemma intT_and {n : ℕ} (φ ψ : Semiformula (setTemplateLanguage k arities) ξ n) :
    intT (φ ⋏ ψ) = intT φ ⋏ intT ψ := rfl
@[simp] lemma intT_or {n : ℕ} (φ ψ : Semiformula (setTemplateLanguage k arities) ξ n) :
    intT (φ ⋎ ψ) = intT φ ⋎ intT ψ := rfl
@[simp] lemma intT_all {n : ℕ} (φ : Semiformula (setTemplateLanguage k arities) ξ (n + 1)) :
    intT (∀⁰ φ) = ∀⁰ (∼domT n ⋎ intT φ) := rfl
@[simp] lemma intT_exs {n : ℕ} (φ : Semiformula (setTemplateLanguage k arities) ξ (n + 1)) :
    intT (∃⁰ φ) = ∃⁰ (domT n ⋏ intT φ) := rfl

/-- The interpretation commutes with negation. -/
@[simp] lemma intT_neg : ∀ {n : ℕ} (φ : Semiformula (setTemplateLanguage k arities) ξ n),
    intT (∼φ) = ∼intT φ
  | _, .rel (Sum.inl R) v => rfl
  | _, .rel (Sum.inr r) v => rfl
  | _, .nrel (Sum.inl R) v => by
      show atomT R v = ∼∼atomT R v
      simp
  | _, .nrel (Sum.inr r) v => rfl
  | _, ⊤ => by simp
  | _, ⊥ => by simp
  | _, φ ⋏ ψ => by simp [intT_neg φ, intT_neg ψ]
  | _, φ ⋎ ψ => by simp [intT_neg φ, intT_neg ψ]
  | _, ∀⁰ φ => by simp [intT_neg φ]
  | _, ∃⁰ φ => by simp [intT_neg φ]

@[simp] lemma intT_imp {n : ℕ} (φ ψ : Semiformula (setTemplateLanguage k arities) ξ n) :
    intT (φ 🡒 ψ) = intT φ 🡒 intT ψ := by
  simp [FirstOrder.Semiformula.imp_eq]

@[simp] lemma intT_iff {n : ℕ} (φ ψ : Semiformula (setTemplateLanguage k arities) ξ n) :
    intT (φ 🡘 ψ) = intT φ 🡘 intT ψ := by
  simp [LogicalConnective.iff]

end Meta

/-! ## Embedding sentences -/

section Embedding

variable {ξ : Type*}

lemma emb_comp_embSubstsT {ο : Type*} [IsEmpty ο] {n m : ℕ}
    (v : Fin m → Semiterm (setTemplateLanguage k arities) ο n) :
    ((Rew.emb : Rew (setTemplateLanguage k arities) ο n ξ n).comp (Rew.embSubsts v)) =
      Rew.embSubsts (fun i ↦ Rew.emb (v i)) :=
  ConstructibleInterpretation.emb_comp_embSubsts_language v

lemma emb_atomT {ο : Type*} [IsEmpty ο] {n m : ℕ} (R : (ℒₛₑₜ).Rel m)
    (v : Fin m → Semiterm (setTemplateLanguage k arities) ο n) :
    (Rew.emb ▹ atomT R v : Semiformula (setTemplateLanguage k arities) ξ n) =
      atomT R (fun i ↦ Rew.emb (v i)) := by
  cases R with
  | eq => rw [atomT, atomT, ← TransitiveRewriting.comp_app, emb_comp_embSubstsT]
  | mem => rw [atomT, atomT, ← TransitiveRewriting.comp_app, emb_comp_embSubstsT]

lemma emb_domT {ο : Type*} [IsEmpty ο] {n : ℕ} :
    (Rew.emb ▹ (domT n : Semiformula (setTemplateLanguage k arities) ο (n + 1)) :
      Semiformula (setTemplateLanguage k arities) ξ (n + 1)) = domT n :=
  ConstructibleInterpretation.emb_guard (liftSet domS)

/-- The interpretation commutes with embedding sentences into formulas. -/
lemma emb_intT {ο : Type*} [IsEmpty ο] :
    ∀ {n : ℕ} (φ : Semiformula (setTemplateLanguage k arities) ο n),
      (Rew.emb ▹ intT φ : Semiformula (setTemplateLanguage k arities) ξ n) = intT (Rew.emb ▹ φ)
  | _, .rel (Sum.inl R) v => emb_atomT R v
  | _, .rel (Sum.inr r) v => rfl
  | _, .nrel (Sum.inl R) v => by
      show Rew.emb ▹ (∼atomT R v) = ∼atomT R (fun i ↦ Rew.emb (v i))
      rw [LogicalConnective.HomClass.map_neg, emb_atomT]
  | _, .nrel (Sum.inr r) v => rfl
  | _, ⊤ => by simp
  | _, ⊥ => by simp
  | _, φ ⋏ ψ => by simp [emb_intT φ, emb_intT ψ]
  | _, φ ⋎ ψ => by simp [emb_intT φ, emb_intT ψ]
  | _, ∀⁰ φ => by
      simp only [intT_all, Rewriting.app_all, Rew.q_emb, LogicalConnective.HomClass.map_or,
        LogicalConnective.HomClass.map_neg]
      rw [emb_domT, emb_intT φ]
  | _, ∃⁰ φ => by
      simp only [intT_exs, Rewriting.app_exs, Rew.q_emb, LogicalConnective.HomClass.map_and]
      rw [emb_domT, emb_intT φ]

end Embedding

/-! ## The bridge at internal codes -/

section Internal

open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.InternalInterpretation LeanProofs.BoundedPAConsistency.InternalRelativization

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The interpreted placeholder meaning. -/
def IK {a : ℕ} (K : Bootstrapping.Semiformula V ℒₛₑₜ a) : Bootstrapping.Semiformula V ℒₛₑₜ a :=
  ⟨interp (PN : V) K.val, isSemiformula_interp good_PN K.isSemiformula⟩

@[simp] lemma IK_val {a : ℕ} (K : Bootstrapping.Semiformula V ℒₛₑₜ a) :
    (IK K).val = interp (PN : V) K.val := rfl

lemma embSubsts_app {n m : ℕ} (v : Fin m → SyntacticSemiterm (setTemplateLanguage k arities) n)
    (σ : Semisentence (setTemplateLanguage k arities) m) :
    (Rew.embSubsts v ▹ σ : Semiproposition (setTemplateLanguage k arities) n) =
      Rew.subst v ▹ (Rewriting.emb σ : Semiproposition (setTemplateLanguage k arities) m) :=
  LTemplate.embSubsts_app v σ

/-- A translated lifted sentence under a substitution. -/
lemma translate_embSubsts_liftSet (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {n m : ℕ} (v : Fin m → SyntacticSemiterm (setTemplateLanguage k arities) n)
    (σ : SetTheorySemisentence m) :
    (translateFormula Ks (Rew.embSubsts v ▹ liftSet σ)).val =
      subst ℒₛₑₜ (SemitermVec.val fun i ↦ translateTerm (V := V) (v i)) (⌜σ⌝ : V) :=
  LTemplate.translate_embSubsts_liftSet Ks v σ

lemma translate_domT (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i)) (n : ℕ) :
    (translateFormula Ks (domT n : Semiproposition (setTemplateLanguage k arities) (n + 1))).val =
      (⌜domS⌝ : V) := by
  rw [domT, translate_embSubsts_liftSet]
  exact ConstructibleInterpretation.subst_unary_bvar0 _ (by simp) (by simp)

lemma translate_atomT_eq (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {n : ℕ} (v : Fin 2 → SyntacticSemiterm (setTemplateLanguage k arities) n) :
    (translateFormula Ks (atomT Language.Set.Rel.eq v)).val =
      subst ℒₛₑₜ (SemitermVec.val fun i ↦ translateTerm (V := V) (v i)) (⌜eqS⌝ : V) := by
  rw [atomT, translate_embSubsts_liftSet]

lemma translate_atomT_mem (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {n : ℕ} (v : Fin 2 → SyntacticSemiterm (setTemplateLanguage k arities) n) :
    (translateFormula Ks (atomT Language.Set.Rel.mem v)).val =
      subst ℒₛₑₜ (SemitermVec.val fun i ↦ translateTerm (V := V) (v i)) (⌜memS⌝ : V) := by
  rw [atomT, translate_embSubsts_liftSet]

private theorem interp_translate_rel
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {n m : ℕ} (R : (setTemplateLanguage k arities).Rel m)
    (v : Fin m → SyntacticSemiterm (setTemplateLanguage k arities) n) :
    interp (PN : V) (translateFormula Ks (Semiformula.rel R v)).val =
      (translateFormula (fun i ↦ IK (Ks i)) (intT (Semiformula.rel R v))).val := by
  cases R with
  | inl R =>
      have hu := (Bootstrapping.Semiformula.rel R
        (fun i ↦ translateTerm (V := V) (v i))).isSemiformula.isUFormula
      rw [Bootstrapping.Semiformula.rel_val] at hu
      change interp (PN : V) (Bootstrapping.Semiformula.rel R
        (fun i ↦ translateTerm (V := V) (v i))).val = _
      rw [Bootstrapping.Semiformula.rel_val,
        interp_rel (IsUFormula.rel.mp hu).1 (IsUFormula.rel.mp hu).2, intT_rel_inl, atomOf_PN]
      cases R with
      | eq => rw [if_pos (by change ((0 : ℕ) : V) = 0; simp), translate_atomT_eq]
      | mem => rw [if_neg (by change ((1 : ℕ) : V) ≠ 0; simp), translate_atomT_mem]
  | inr r =>
      change interp (PN : V) ((Ks r.1).subst fun j ↦ translateTerm (v (Fin.cast r.2 j))).val =
        ((IK (Ks r.1)).subst fun j ↦ translateTerm (v (Fin.cast r.2 j))).val
      rw [Bootstrapping.Semiformula.val_substs, Bootstrapping.Semiformula.val_substs, IK_val,
        interp_subst good_PN (Ks r.1).isSemiformula (SemitermVec.isSemitermVec _)]

/-- **Interpretation commutes with template translation.** -/
theorem interp_translate (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i)) :
    ∀ {n : ℕ} (φ : Semiproposition (setTemplateLanguage k arities) n),
      interp (PN : V) (translateFormula Ks φ).val =
        (translateFormula (fun i ↦ IK (Ks i)) (intT φ)).val
  | _, .rel R v => interp_translate_rel Ks R v
  | _, .nrel R v => by
      change interp (PN : V) (translateFormula Ks (∼Semiformula.rel R v)).val =
        (translateFormula (fun i ↦ IK (Ks i)) (intT (∼Semiformula.rel R v))).val
      rw [intT_neg, translateFormula_neg, translateFormula_neg,
        Bootstrapping.Semiformula.val_neg, Bootstrapping.Semiformula.val_neg,
        ← interp_neg good_PN (translateFormula Ks (Semiformula.rel R v)).isSemiformula,
        interp_translate_rel Ks R v]
  | _, ⊤ => by simp [translateFormula]
  | _, ⊥ => by simp [translateFormula]
  | _, φ ⋏ ψ => by
      change interp (PN : V) (translateFormula Ks φ ⋏ translateFormula Ks ψ).val =
        (translateFormula (fun i ↦ IK (Ks i)) (intT φ) ⋏
          translateFormula (fun i ↦ IK (Ks i)) (intT ψ)).val
      rw [Bootstrapping.Semiformula.val_and, Bootstrapping.Semiformula.val_and,
        interp_and (translateFormula Ks φ).isSemiformula.isUFormula
          (translateFormula Ks ψ).isSemiformula.isUFormula,
        interp_translate Ks φ, interp_translate Ks ψ]
  | _, φ ⋎ ψ => by
      change interp (PN : V) (translateFormula Ks φ ⋎ translateFormula Ks ψ).val =
        (translateFormula (fun i ↦ IK (Ks i)) (intT φ) ⋎
          translateFormula (fun i ↦ IK (Ks i)) (intT ψ)).val
      rw [Bootstrapping.Semiformula.val_or, Bootstrapping.Semiformula.val_or,
        interp_or (translateFormula Ks φ).isSemiformula.isUFormula
          (translateFormula Ks ψ).isSemiformula.isUFormula,
        interp_translate Ks φ, interp_translate Ks ψ]
  | n, ∀⁰ φ => by
      change interp (PN : V) (∀⁰ translateFormula Ks φ).val =
        (∀⁰ (translateFormula (fun i ↦ IK (Ks i)) (∼domT n) ⋎
          translateFormula (fun i ↦ IK (Ks i)) (intT φ))).val
      rw [translateFormula_neg, Bootstrapping.Semiformula.val_all, Bootstrapping.Semiformula.val_all,
        Bootstrapping.Semiformula.val_or, Bootstrapping.Semiformula.val_neg,
        interp_all (translateFormula Ks φ).isSemiformula.isUFormula, dom_PN,
        translate_domT, interp_translate Ks φ]
  | n, ∃⁰ φ => by
      change interp (PN : V) (∃⁰ translateFormula Ks φ).val =
        (∃⁰ (translateFormula (fun i ↦ IK (Ks i)) (domT n) ⋏
          translateFormula (fun i ↦ IK (Ks i)) (intT φ))).val
      rw [Bootstrapping.Semiformula.val_exs, Bootstrapping.Semiformula.val_exs,
        Bootstrapping.Semiformula.val_and,
        interp_exs (translateFormula Ks φ).isSemiformula.isUFormula, dom_PN,
        translate_domT, interp_translate Ks φ]

/-- The sentence form: a compiled interpreted template is the interpretation
of the translated template. -/
theorem interp_translate_emb (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (σ : Sentence (setTemplateLanguage k arities)) :
    interp (PN : V) (translateFormula Ks (Rewriting.emb σ)).val =
      (translateFormula (fun i ↦ IK (Ks i)) (Rewriting.emb (intT σ))).val := by
  rw [interp_translate Ks, emb_intT]

end Internal

end LeanProofs.ZFCinPA.QTInterp
