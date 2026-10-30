import ZFCinPA.ValidatorSeedLogicalImages222
import ZFCinPA.ConstructibleInterpretation

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! # Fixed-sentence images in the moving-marker seed interpretation

For a FIXED standard sentence `σ`, the tagged image required by
`ValidatorSeedMarkerRelativization222.AxiomImages` follows from a semantic
fact by completeness: if in every model of `seedTheory` the tagged domain
`{x | t ∈ x}` of every empty `t` satisfies `σ`, then `seedTheory` proves the
free-marker sentence `Empty(&0) → σ^{&0 ∈ ·}`. Internalization gives the
image at marker `0`, and the internal eigenvariable shift carries it to every
internal marker `j`. Only the finitely many standard sentences supplied by a
client go through completeness; schema instances are not handled here.
-/
namespace LeanProofs.ZFCinPA.ValidatorSeedFixedImages222
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA

/-! ## External free-marker relativization -/

section External

/-- The tagged domain at binder depth `n + 1`: the marker `&0` is a member
of the innermost bound variable. -/
def domM (n : ℕ) : SetTheorySemiproposition (n + 1) :=
  Semiformula.rel Language.Mem.mem ![&0, #0]

/-- Relativization of a closed semiformula to the free-marker tagged domain. -/
def relM : {n : ℕ} → SetTheorySemisentence n → SetTheorySemiproposition n
  | _, .rel R v => Rew.emb ▹ (Semiformula.rel R v : SetTheorySemisentence _)
  | _, .nrel R v => Rew.emb ▹ (Semiformula.nrel R v : SetTheorySemisentence _)
  | _, ⊤ => ⊤
  | _, ⊥ => ⊥
  | _, φ ⋏ ψ => relM φ ⋏ relM ψ
  | _, φ ⋎ ψ => relM φ ⋎ relM ψ
  | n, ∀⁰ φ => ∀⁰ (∼domM n ⋎ relM φ)
  | n, ∃⁰ φ => ∃⁰ (domM n ⋏ relM φ)

/-- `&0` is empty. -/
def emptyM : SetTheoryProposition :=
  ∀⁰ (Semiformula.rel Language.Mem.mem ![#0, &0] 🡒 ⊥)

/-- The free-marker statement: if the marker is empty, `σ` holds tagged. -/
def markerImage (σ : SetTheorySentence) : SetTheoryProposition := emptyM 🡒 relM σ

end External

/-! ## Semantics: relativization is evaluation in the tagged substructure -/

section Semantics

variable {M : Type} [SetStructure M]

/-- The tagged domain of a marker, as a set structure. -/
@[reducible] def tagStructure (t : M) : SetStructure {x : M // t ∈ x} :=
  ⟨fun s a => a.1 ∈ s.1⟩

attribute [local instance] tagStructure

lemma val_tag (t : M) {n : ℕ} (u : Semiterm ℒₛₑₜ Empty n) (b : Fin n → {x : M // t ∈ x})
    (f : ℕ → M) :
    (Rew.emb u : Semiterm ℒₛₑₜ ℕ n).val (Subtype.val ∘ b) f = (u.val b Empty.elim).1 := by
  cases u with
  | bvar x => rfl
  | fvar x => exact x.elim
  | func g v => exact g.elim

lemma comp_vecCons_tag (t : M) {n : ℕ} (y : {x : M // t ∈ x}) (b : Fin n → {x : M // t ∈ x}) :
    (Subtype.val ∘ (y :> b)) = (y.1 :> Subtype.val ∘ b) :=
  funext fun i => Fin.cases rfl (fun _ => rfl) i

lemma eval_domM (t : M) {n : ℕ} (x : M) (b : Fin n → M) (f : ℕ → M) (hf : f 0 = t) :
    (domM n).Eval (x :> b) f ↔ t ∈ x := by
  simp [domM, hf]

theorem eval_relM (t : M) :
    ∀ {n : ℕ} (φ : SetTheorySemisentence n) (b : Fin n → {x : M // t ∈ x}) (f : ℕ → M),
      f 0 = t → ((relM φ).Eval (Subtype.val ∘ b) f ↔ φ.Eval b Empty.elim)
  | _, .rel R v, b, f, _ => by
      cases R with
      | eq =>
          change ((Rew.emb (v 0)).val (Subtype.val ∘ b) f =
            (Rew.emb (v 1)).val (Subtype.val ∘ b) f) ↔
              ((v 0).val b Empty.elim = (v 1).val b Empty.elim)
          rw [val_tag, val_tag]
          exact Subtype.ext_iff.symm
      | mem =>
          change ((Rew.emb (v 0)).val (Subtype.val ∘ b) f ∈
            (Rew.emb (v 1)).val (Subtype.val ∘ b) f) ↔
              ((v 0).val b Empty.elim ∈ (v 1).val b Empty.elim)
          rw [val_tag, val_tag]
          exact Iff.rfl
  | _, .nrel R v, b, f, _ => by
      cases R with
      | eq =>
          change ¬((Rew.emb (v 0)).val (Subtype.val ∘ b) f =
            (Rew.emb (v 1)).val (Subtype.val ∘ b) f) ↔
              ¬((v 0).val b Empty.elim = (v 1).val b Empty.elim)
          rw [val_tag, val_tag]
          exact not_congr Subtype.ext_iff.symm
      | mem =>
          change ¬((Rew.emb (v 0)).val (Subtype.val ∘ b) f ∈
            (Rew.emb (v 1)).val (Subtype.val ∘ b) f) ↔
              ¬((v 0).val b Empty.elim ∈ (v 1).val b Empty.elim)
          rw [val_tag, val_tag]
          exact Iff.rfl
  | _, ⊤, b, f, _ => by simp [relM]
  | _, ⊥, b, f, _ => by simp [relM]
  | _, φ ⋏ ψ, b, f, hf => by
      simp only [relM, LogicalConnective.HomClass.map_and]
      exact and_congr (eval_relM t φ b f hf) (eval_relM t ψ b f hf)
  | _, φ ⋎ ψ, b, f, hf => by
      simp only [relM, LogicalConnective.HomClass.map_or]
      exact or_congr (eval_relM t φ b f hf) (eval_relM t ψ b f hf)
  | _, ∀⁰ φ, b, f, hf => by
      simp only [relM, Semiformula.eval_all, LogicalConnective.HomClass.map_or,
        LogicalConnective.HomClass.map_neg]
      constructor
      · intro h x
        have := (h x.1).resolve_left (by rw [eval_domM t x.1 _ f hf]; exact not_not.mpr x.2)
        rw [← comp_vecCons_tag] at this
        exact (eval_relM t φ _ f hf).mp this
      · intro h x
        by_cases hx : t ∈ x
        · right
          have := (eval_relM t φ (⟨x, hx⟩ :> b) f hf).mpr (h ⟨x, hx⟩)
          rwa [comp_vecCons_tag] at this
        · left
          rw [eval_domM t x _ f hf]
          exact hx
  | _, ∃⁰ φ, b, f, hf => by
      simp only [relM, Semiformula.eval_ex, LogicalConnective.HomClass.map_and]
      constructor
      · rintro ⟨x, hx, h⟩
        rw [eval_domM t x _ f hf] at hx
        refine ⟨⟨x, hx⟩, (eval_relM t φ _ f hf).mp ?_⟩
        rwa [comp_vecCons_tag]
      · rintro ⟨x, h⟩
        refine ⟨x.1, (eval_domM t x.1 _ f hf).mpr x.2, ?_⟩
        have := (eval_relM t φ (x :> b) f hf).mpr h
        rwa [comp_vecCons_tag] at this

theorem eval_emptyM (f : ℕ → M) : emptyM.Evalf f ↔ ∀ z : M, z ∉ f 0 := by
  simp [emptyM]

/-- The free-marker image holds at a valuation iff, when the marker is
empty, its tagged substructure satisfies `σ`. -/
theorem eval_markerImage (σ : SetTheorySentence) (f : ℕ → M) :
    (markerImage σ).Evalf f ↔
      ((∀ z : M, z ∉ f 0) → σ.Eval (![] : Fin 0 → {x : M // f 0 ∈ x}) Empty.elim) := by
  have h := eval_relM (f 0) σ (![] : Fin 0 → {x : M // f 0 ∈ x}) f rfl
  have hb : (Subtype.val ∘ (![] : Fin 0 → {x : M // f 0 ∈ x})) = ![] :=
    funext fun i => i.elim0
  rw [hb] at h
  simp only [markerImage, LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq,
    eval_emptyM]
  exact imp_congr_right fun _ => h

end Semantics

/-! ## Completeness and internalization -/

section Completeness

variable {T : SetTheory} [𝗘𝗤 ℒₛₑₜ ⪯ T]

attribute [local instance] tagStructure

/-- The semantic premise for a fixed sentence: in every model of `T`, the
tagged domain of every empty marker satisfies `σ`. -/
def TaggedValid (T : SetTheory) (σ : SetTheorySentence) : Prop :=
  ∀ (M : Type) [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* T] (t : M),
    (∀ z : M, z ∉ t) → σ.Eval (![] : Fin 0 → {x : M // t ∈ x}) Empty.elim

theorem proves_markerImage (σ : SetTheorySentence) (h : TaggedValid T σ) :
    T ⊢ (markerImage σ).univCl := by
  refine SetTheory.provable_of_models.{0} T _ ?_
  intro M _ _ _
  rw [models_iff_proposition]
  intro f
  rw [eval_markerImage]
  exact h M (f 0)

end Completeness

/-! ## Internally, in every model of `𝗜𝚺₁` -/

section Internal

open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.InternalRelativization
open ValidatorFullSeedTheory222 ValidatorSeedSourceBasis222 ValidatorSeedMarkerDischarge222
open ValidatorSeedMarkerRelativization222

variable {W : Type} [ORingStructure W] [W↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A proved universal closure opens to an internal proof of the open formula. -/
theorem provable_open_of_univCl {T : SetTheory} [T.Δ₁] (φ : SetTheoryProposition)
    (h : T ⊢ φ.univCl) : Bootstrapping.Provable T (⌜φ⌝ : W) := by
  have hp := internalize_provability (V := W) h
  rw [quote_univCl_eq] at hp
  obtain ⟨d, hd⟩ := hp
  have hq := ModelCodedSpecialization.specializedProofCode_isProof T ((0 + φ.fvSup : ℕ) : W)
    (⌜(Rew.fixitr 0 φ.fvSup ▹ φ : Semiformula ℒₛₑₜ ℕ (0 + φ.fvSup))⌝ : W) d
    (by simpa using (LO.FirstOrder.Semiformula.quote_isSemiformula (V := W)
      (Rew.fixitr 0 φ.fvSup ▹ φ : Semiformula ℒₛₑₜ ℕ (0 + φ.fvSup)))) hd
  rw [subst_fvarVec_quote_lang, quote_subst_fvar_fixitr] at hq
  exact ⟨_, hq⟩

lemma quote_domM (n : ℕ) : (⌜(domM n : SetTheorySemiproposition (n + 1))⌝ : W) = domainCode 0 := by
  simp [domM, domainCode, memberCode, LO.FirstOrder.Semiformula.quote_rel, Matrix.vecHead,
    Matrix.vecTail]
  change ((1 : ℕ) : W) = 1
  simp

lemma quote_emptyM : (⌜emptyM⌝ : W) = emptyCode 0 := by
  rw [emptyM, LO.FirstOrder.Semiformula.quote_all, FirstOrder.Semiformula.imp_eq,
    LO.FirstOrder.Semiformula.quote_or, ConstructibleInterpretation.quote_neg_set]
  simp [emptyCode, memberCode, Bootstrapping.imp, LO.FirstOrder.Semiformula.quote_rel,
    Matrix.vecHead, Matrix.vecTail]
  congr 2
  change ((1 : ℕ) : W) = 1
  simp

lemma isUFormula_quote_set {n : ℕ} (ψ : SetTheorySemiproposition n) :
    IsUFormula ℒₛₑₜ (⌜ψ⌝ : W) :=
  (LO.FirstOrder.Semiformula.quote_isSemiformula ψ).isUFormula

/-- **The code of the external free-marker relativization is the internal
tagged relativization at marker `0`.** -/
theorem quote_relM : ∀ {n : ℕ} (φ : SetTheorySemisentence n),
    (⌜relM φ⌝ : W) = tagRel 0 ⌜(Rew.emb ▹ φ : SetTheorySemiproposition n)⌝
  | _, .rel R v => by
      have h := isUFormula_quote_set (W := W)
        (Rew.emb ▹ (Semiformula.rel R v : SetTheorySemisentence _) : SetTheorySemiproposition _)
      simp only [Semiformula.rew_rel] at h ⊢
      rw [LO.FirstOrder.Semiformula.quote_rel] at h
      simp only [relM]
      rw [Semiformula.rew_rel, tagRel, LO.FirstOrder.Semiformula.quote_rel,
        relativize_rel (IsUFormula.rel.mp h).1 (IsUFormula.rel.mp h).2]
  | _, .nrel R v => by
      have h := isUFormula_quote_set (W := W)
        (Rew.emb ▹ (Semiformula.nrel R v : SetTheorySemisentence _) : SetTheorySemiproposition _)
      simp only [Semiformula.rew_nrel] at h ⊢
      rw [LO.FirstOrder.Semiformula.quote_nrel] at h
      simp only [relM]
      rw [Semiformula.rew_nrel, tagRel, LO.FirstOrder.Semiformula.quote_nrel,
        relativize_nrel (IsUFormula.nrel.mp h).1 (IsUFormula.nrel.mp h).2]
  | _, ⊤ => by simp [relM, tagRel]
  | _, ⊥ => by simp [relM, tagRel]
  | _, φ ⋏ ψ => by
      simp only [relM]
      rw [LogicalConnective.HomClass.map_and, LO.FirstOrder.Semiformula.quote_and,
        LO.FirstOrder.Semiformula.quote_and, quote_relM φ, quote_relM ψ, tagRel, tagRel, tagRel,
        relativize_and (isUFormula_quote_set _) (isUFormula_quote_set _)]
  | _, φ ⋎ ψ => by
      simp only [relM]
      rw [LogicalConnective.HomClass.map_or, LO.FirstOrder.Semiformula.quote_or,
        LO.FirstOrder.Semiformula.quote_or, quote_relM φ, quote_relM ψ, tagRel, tagRel, tagRel,
        relativize_or (isUFormula_quote_set _) (isUFormula_quote_set _)]
  | n, ∀⁰ φ => by
      simp only [relM]
      rw [Rewriting.app_all, Rew.q_emb, LO.FirstOrder.Semiformula.quote_all,
        LO.FirstOrder.Semiformula.quote_or, ConstructibleInterpretation.quote_neg_set, quote_domM,
        quote_relM φ,
        LO.FirstOrder.Semiformula.quote_all, tagRel, tagRel,
        relativize_all (isUFormula_quote_set _)]
  | n, ∃⁰ φ => by
      simp only [relM]
      rw [Rewriting.app_exs, Rew.q_emb, LO.FirstOrder.Semiformula.quote_ex,
        LO.FirstOrder.Semiformula.quote_and, quote_domM, quote_relM φ,
        LO.FirstOrder.Semiformula.quote_ex, tagRel, tagRel,
        relativize_exs (isUFormula_quote_set _)]

theorem quote_markerImage (σ : SetTheorySentence) :
    (⌜markerImage σ⌝ : W) = Bootstrapping.imp ℒₛₑₜ (emptyCode 0) (tagRel 0 (⌜σ⌝ : W)) := by
  rw [markerImage, FirstOrder.Semiformula.imp_eq, LO.FirstOrder.Semiformula.quote_or,
    ConstructibleInterpretation.quote_neg_set, quote_emptyM, quote_relM]
  rfl

/-- The image at marker `0` moves to every internal marker by the
eigenvariable shift; the closed sentence code is shift-fixed. -/
theorem fixed_image_all {T : SetTheory} [T.Δ₁] (σ : SetTheorySentence)
    (h0 : Bootstrapping.Provable T (Bootstrapping.imp ℒₛₑₜ (emptyCode 0) (tagRel 0 (⌜σ⌝ : W))))
    (j : W) : Bootstrapping.Provable T (Bootstrapping.imp ℒₛₑₜ (emptyCode j) (tagRel j (⌜σ⌝ : W))) := by
  have hσ : IsFormula ℒₛₑₜ (⌜σ⌝ : W) := by simp
  have hshift : shift ℒₛₑₜ (⌜σ⌝ : W) = ⌜σ⌝ := by
    rw [LO.FirstOrder.Sentence.quote_def, ← LO.FirstOrder.Semiformula.quote_shift]
    congr 1
    rw [Rewriting.shift, ← TransitiveRewriting.comp_app, Rew.shift_comp_emb]
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact h0
  case succ j ih =>
    have hd := Derivable.shift ih.toDerivable
    have he : shift ℒₛₑₜ (Bootstrapping.imp ℒₛₑₜ (emptyCode j) (tagRel j (⌜σ⌝ : W))) =
        Bootstrapping.imp ℒₛₑₜ (emptyCode (j + 1)) (tagRel (j + 1) (⌜σ⌝ : W)) := by
      simp only [Bootstrapping.imp]
      rw [shift_or (empty_typed j).isUFormula.neg (tagRel_typed j hσ).isUFormula,
        shift_neg (empty_typed j), shift_empty, tagRel_shift j hσ.isUFormula, hshift]
    simp only [mem_setShift_insert, setShift_empty, he] at hd
    exact hd.toProvable

/-- **The fixed image theorem.** A semantically tagged-valid fixed sentence
has its tagged image at every internal marker. -/
theorem fixed_image (σ : SetTheorySentence) (h : TaggedValid seedTheory σ) (j : W) :
    Bootstrapping.Provable seedTheory
      (Bootstrapping.imp ℒₛₑₜ (emptyCode j) (tagRel j (⌜σ⌝ : W))) := by
  apply fixed_image_all σ _ j
  have hp := provable_open_of_univCl (W := W) (markerImage σ) (proves_markerImage σ h)
  rwa [quote_markerImage] at hp

/-- The `AxiomImages` form of a fixed image. -/
theorem fixed_image_derivable (σ : SetTheorySentence) (h : TaggedValid seedTheory σ) (j : W) :
    Derivable seedTheory (insert (tagRel j (⌜σ⌝ : W)) (insert (emptyGuard j) (sideSet j))) := by
  exact ValidatorSeedGicImages222.derivable_of_tagged_imp (by simp) (fixed_image σ h j)

end Internal

end LeanProofs.ZFCinPA.ValidatorSeedFixedImages222
