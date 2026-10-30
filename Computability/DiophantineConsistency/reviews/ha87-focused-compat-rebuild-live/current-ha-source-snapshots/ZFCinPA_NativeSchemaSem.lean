import ZFCinPA.SchemaSourceSyntax
import ZFCinPA.NTInterp

set_option autoImplicit false
noncomputable section

/-!
# Separation and Replacement under the WF interpretation: the templates

Two fixed template sentences over one placeholder `R`, each of the shape
`intT (congruence of R) → intT (schema body for R)`, proved in every model
of the native template theory `templN`:

* `sepT` (`R` unary): from the interpreted congruence law of `R`, the
  interpreted separation body. A GIC instance at the raw matrix
  `u ∈ x ∧ v = u ∧ R u` collects exactly `{u ∈ x | R u}`; its members are in
  the domain, so it is in the domain (WF closure); congruence of `R` under
  bisimilarity transports membership up to bisimilarity.
* `replT` (`R` binary): from the interpreted congruence law, the interpreted
  (globally total) replacement body. A GIC instance at the raw matrix
  `u ∈ X ∧ D v ∧ R u v` collects one image of each `u ∈ X`; functionality up
  to bisimilarity identifies any other image with a collected one.

Compiled at internal codes (`NativeSchema`), `IK K` replaces `R` and
`NTInterp.interp_translate` turns the compiled sentences into the internal
interpretations of `congruenceFormula` and `sepBody`/`repBody`.
-/

namespace LeanProofs.ZFCinPA.NativeSchemaSem

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.SetPlaceholderQuotient
open LeanProofs.ZFCinPA.NativeSet LeanProofs.ZFCinPA.NativeInterp LeanProofs.ZFCinPA.NTemplate
open LeanProofs.ZFCinPA.NTInterp
open SetTheory.BusyBeaver.ZFC

local instance {k : ℕ} {arities : Fin k → ℕ} : Language.Mem (setTemplateLanguage k arities) :=
  ⟨Sum.inl Language.Set.Rel.mem⟩

/-! ## Raw facts in a model of the native theory -/

section Facts

variable {M : Type} [Nonempty M] [SetStructure M] [M↓[ℒₛₑₜ] ⊧* nativeTheory]

abbrev Eqv (x y : M) : Prop := ProfileCollection.Eqv (memRel M) x y
abbrev Mem (x y : M) : Prop := ProfileComposition.Member (memRel M) x y

lemma eqv_refl (x : M) : Eqv x x := ProfileModel.eqv_refl_of_model (memRel M) wM hM x

lemma eqv_symm {x y : M} (h : Eqv x y) : Eqv y x :=
  ProfileModel.eqv_symm_of_model (memRel M) wM hM h

lemma eqv_trans {x y z : M} (h₁ : Eqv x y) (h₂ : Eqv y z) : Eqv x z :=
  CompositionModel.eqv_trans_of_model (memRel M) wM hM h₁ h₂

lemma D_iff (x : M) : D x ↔ WellFoundedPart.WF (qm (M := M)) (cl x) := eval_domS x _

lemma D_member {x y : M} (hy : D y) (h : Mem x y) : D x :=
  (D_iff x).2 (WellFoundedPart.wf_mem ((D_iff y).1 hy) h)

lemma D_mem {x y : M} (hy : D y) (h : x ∈ y) : D x := D_member hy ⟨x, h, eqv_refl x⟩

lemma D_closed {b : M} (h : ∀ v, v ∈ b → D v) : D b := by
  refine (D_iff b).2 (WellFoundedPart.quotient_wf_closure (memRel M) wM hM (cl b) fun X hX => ?_)
  obtain ⟨x, rfl⟩ := Quotient.exists_rep X
  obtain ⟨u, hu, hxu⟩ := hX
  have e : cl x = cl u := (QuotientModel.mk_eq_iff (memRel M) wM hM x u).2 hxu
  change WellFoundedPart.WF qm (cl x)
  rw [e]
  exact (D_iff u).1 (h u hu)

lemma eval_domS_any (w : Fin 1 → M) (ε : Empty → M) : domS.Eval w ε ↔ D (w 0) := by
  rw [show w = ![w 0] from funext fun i => by rw [Fin.fin_one_eq_zero i]; rfl,
    show ε = Empty.elim from funext fun e => e.elim]
  rfl

end Facts

/-! ## Evaluating the interpretation in template models -/

section Eval

variable {k : ℕ} {arities : Fin k → ℕ}

variable {M : Type} [Nonempty M] [SetStructure M]
variable [s : Structure (setTemplateLanguage k arities) M]
variable [Structure.Eq (setTemplateLanguage k arities) M]
variable [Structure.Mem (setTemplateLanguage k arities) M]
variable [M↓[ℒₛₑₜ] ⊧* nativeTheory]

omit [Nonempty M] [SetStructure M] [Structure.Eq (setTemplateLanguage k arities) M]
  [Structure.Mem (setTemplateLanguage k arities) M] [M↓[ℒₛₑₜ] ⊧* nativeTheory] in
@[simp] lemma intT_rel_eq {ξ : Type*} {n : ℕ} (v : Fin 2 → Semiterm (setTemplateLanguage k arities) ξ n) :
    intT (Semiformula.rel (Language.Eq.eq : (setTemplateLanguage k arities).Rel 2) v) =
      atomT Language.Set.Rel.eq v := rfl

omit [Nonempty M] [SetStructure M] [Structure.Eq (setTemplateLanguage k arities) M]
  [Structure.Mem (setTemplateLanguage k arities) M] [M↓[ℒₛₑₜ] ⊧* nativeTheory] in
@[simp] lemma intT_nrel_eq {ξ : Type*} {n : ℕ} (v : Fin 2 → Semiterm (setTemplateLanguage k arities) ξ n) :
    intT (Semiformula.nrel (Language.Eq.eq : (setTemplateLanguage k arities).Rel 2) v) =
      ∼atomT Language.Set.Rel.eq v := rfl

omit [Nonempty M] [SetStructure M] [Structure.Eq (setTemplateLanguage k arities) M]
  [Structure.Mem (setTemplateLanguage k arities) M] [M↓[ℒₛₑₜ] ⊧* nativeTheory] in
@[simp] lemma intT_rel_mem {ξ : Type*} {n : ℕ} (v : Fin 2 → Semiterm (setTemplateLanguage k arities) ξ n) :
    intT (Semiformula.rel (Language.Mem.mem : (setTemplateLanguage k arities).Rel 2) v) =
      atomT Language.Set.Rel.mem v := rfl

omit [Nonempty M] [SetStructure M] [Structure.Eq (setTemplateLanguage k arities) M]
  [Structure.Mem (setTemplateLanguage k arities) M] [M↓[ℒₛₑₜ] ⊧* nativeTheory] in
@[simp] lemma intT_nrel_mem {ξ : Type*} {n : ℕ} (v : Fin 2 → Semiterm (setTemplateLanguage k arities) ξ n) :
    intT (Semiformula.nrel (Language.Mem.mem : (setTemplateLanguage k arities).Rel 2) v) =
      ∼atomT Language.Set.Rel.mem v := rfl

omit [Nonempty M] [SetStructure M] [Structure.Eq (setTemplateLanguage k arities) M]
  [Structure.Mem (setTemplateLanguage k arities) M] [M↓[ℒₛₑₜ] ⊧* nativeTheory] in
@[simp] lemma intT_rel_ph {ξ : Type*} {n : ℕ} (i : Fin k)
    (v : Fin (arities i) → Semiterm (setTemplateLanguage k arities) ξ n) :
    intT (Semiformula.rel (placeholderRel i) v) = Semiformula.rel (placeholderRel i) v := rfl

omit [Nonempty M] [SetStructure M] [Structure.Eq (setTemplateLanguage k arities) M]
  [Structure.Mem (setTemplateLanguage k arities) M] [M↓[ℒₛₑₜ] ⊧* nativeTheory] in
@[simp] lemma intT_nrel_ph {ξ : Type*} {n : ℕ} (i : Fin k)
    (v : Fin (arities i) → Semiterm (setTemplateLanguage k arities) ξ n) :
    intT (Semiformula.nrel (placeholderRel i) v) = Semiformula.nrel (placeholderRel i) v := rfl

lemma eval_atomT_eq {ξ : Type*} {n : ℕ} (v : Fin 2 → Semiterm (setTemplateLanguage k arities) ξ n)
    (e : Fin n → M) (f : ξ → M) :
    (atomT Language.Set.Rel.eq v).Eval e f ↔ Eqv ((v 0).val e f) ((v 1).val e f) := by
  simp only [atomT, Semiformula.eval_embSubsts, eval_liftSet]
  exact eval_eqS' _ _

lemma eval_atomT_mem {ξ : Type*} {n : ℕ} (v : Fin 2 → Semiterm (setTemplateLanguage k arities) ξ n)
    (e : Fin n → M) (f : ξ → M) :
    (atomT Language.Set.Rel.mem v).Eval e f ↔ Mem ((v 0).val e f) ((v 1).val e f) := by
  simp only [atomT, Semiformula.eval_embSubsts, eval_liftSet]
  exact eval_memS' _ _

lemma eval_domT {ξ : Type*} {n : ℕ} (x : M) (e : Fin n → M) (f : ξ → M) :
    (domT n : Semiformula (setTemplateLanguage k arities) ξ (n + 1)).Eval (x :> e) f ↔ D x := by
  simp only [domT, Semiformula.eval_embSubsts, eval_liftSet]
  rw [eval_domS_any]
  simp

end Eval

/-! ## The domain structure -/

section SD

variable {k : ℕ} {arities : Fin k → ℕ}
variable (M : Type) [Nonempty M] [SetStructure M]
variable [s : Structure (setTemplateLanguage k arities) M]
variable [M↓[ℒₛₑₜ] ⊧* nativeTheory]

/-- The domain, as a type. -/
abbrev SD := {x : M // D x}

instance sd_nonempty : Nonempty (SD M) := by
  obtain ⟨⟨q, hq⟩⟩ := WellFoundedPart.quotient_domain_nonempty (memRel M) wM hM
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  exact ⟨⟨x, (D_iff x).2 hq⟩⟩

variable {M}

/-- The meaning of a template relation symbol on the domain: `=` is
bisimilarity, `∈` is membership up to bisimilarity, placeholders are kept. -/
def sdRel : {m : ℕ} → (setTemplateLanguage k arities).Rel m → (Fin m → SD M) → Prop
  | _, Sum.inl Language.Set.Rel.eq, v => Eqv (v 0).1 (v 1).1
  | _, Sum.inl Language.Set.Rel.mem, v => Mem (v 0).1 (v 1).1
  | _, Sum.inr r, v => s.rel (Sum.inr r) (fun i ↦ (v i).1)

instance sdStructure : Structure (setTemplateLanguage k arities) (SD M) where
  func := fun _ f _ ↦ by rcases f with f | f <;> exact f.elim
  rel := fun _ r v ↦ sdRel r v

@[simp] lemma sd_rel_eq (v : Fin 2 → SD M) :
    Structure.rel (L := setTemplateLanguage k arities) (Language.Eq.eq : (setTemplateLanguage k arities).Rel 2) v ↔
      Eqv (v 0).1 (v 1).1 := Iff.rfl

@[simp] lemma sd_rel_mem (v : Fin 2 → SD M) :
    Structure.rel (L := setTemplateLanguage k arities) (Language.Mem.mem : (setTemplateLanguage k arities).Rel 2) v ↔
      Mem (v 0).1 (v 1).1 := Iff.rfl

@[simp] lemma sd_rel_ph (i : Fin k) (v : Fin (arities i) → SD M) :
    Structure.rel (L := setTemplateLanguage k arities) (M := SD M) (placeholderRel i) v ↔
      s.rel (placeholderRel i) (fun j ↦ (v j).1) := Iff.rfl

omit [Nonempty M] in
lemma val_term {ξ : Type*} {n : ℕ} (t : Semiterm (setTemplateLanguage k arities) ξ n)
    (b : Fin n → SD M) (f : ξ → SD M) :
    t.val (s := s) (Subtype.val ∘ b) (Subtype.val ∘ f) = (t.val b f).1 :=
  LTemplate.val_template_subtype t b f

omit [Nonempty M] in
lemma val_cons' {n : ℕ} (x : SD M) (b : Fin n → SD M) :
    Subtype.val ∘ (x :> b) = (x.1 :> Subtype.val ∘ b) :=
  Matrix.comp_vecCons Subtype.val x b

variable [Structure.Eq (setTemplateLanguage k arities) M]
variable [Structure.Mem (setTemplateLanguage k arities) M]

private theorem eval_intT_rel {ξ : Type*} {n m : ℕ}
    (R : (setTemplateLanguage k arities).Rel m)
    (v : Fin m → Semiterm (setTemplateLanguage k arities) ξ n)
    (b : Fin n → SD M) (f : ξ → SD M) :
    (intT (.rel R v)).Eval (Subtype.val ∘ b) (Subtype.val ∘ f) ↔ (Semiformula.rel R v).Eval b f := by
  cases R with
  | inl R =>
      cases R with
      | eq =>
          change (atomT Language.Set.Rel.eq v).Eval _ _ ↔ _
          rw [eval_atomT_eq, val_term, val_term]
          rfl
      | mem =>
          change (atomT Language.Set.Rel.mem v).Eval _ _ ↔ _
          rw [eval_atomT_mem, val_term, val_term]
          rfl
  | inr r =>
      change s.rel (Sum.inr r) (fun i ↦ (v i).val (Subtype.val ∘ b) (Subtype.val ∘ f)) ↔
        s.rel (Sum.inr r) (fun i ↦ ((v i).val b f).1)
      simp only [val_term]

/-- **Evaluation of the interpretation in a template model**: `intT φ` at
domain elements holds in `M` iff `φ` holds in the domain structure. -/
theorem eval_intT {ξ : Type*} :
    ∀ {n : ℕ} (φ : Semiformula (setTemplateLanguage k arities) ξ n) (b : Fin n → SD M) (f : ξ → SD M),
      (intT φ).Eval (Subtype.val ∘ b) (Subtype.val ∘ f) ↔ φ.Eval b f
  | _, .rel R v, b, f => eval_intT_rel R v b f
  | _, .nrel R v, b, f => by
      change (intT (∼Semiformula.rel R v)).Eval _ _ ↔ (∼Semiformula.rel R v).Eval _ _
      rw [intT_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq,
        LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
      exact not_congr (eval_intT_rel R v b f)
  | _, ⊤, b, f => by simp
  | _, ⊥, b, f => by simp
  | _, φ ⋏ ψ, b, f => by
      simp only [intT_and, LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq,
        eval_intT φ b f, eval_intT ψ b f]
  | _, φ ⋎ ψ, b, f => by
      simp only [intT_or, LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
        eval_intT φ b f, eval_intT ψ b f]
  | n, ∀⁰ φ, b, f => by
      simp only [intT_all, Semiformula.eval_all, LogicalConnective.HomClass.map_or,
        LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.or_eq,
        LogicalConnective.Prop.neg_eq, eval_domT]
      apply ConstructibleInterpretation.forall_guard id Function.surjective_id
      intro u
      rw [← val_cons' u b, eval_intT φ (u :> b) f]
      rfl
  | n, ∃⁰ φ, b, f => by
      simp only [intT_exs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
        LogicalConnective.Prop.and_eq, eval_domT]
      apply ConstructibleInterpretation.exists_guard id Function.surjective_id
      intro u
      rw [← val_cons' u b, eval_intT φ (u :> b) f]
      rfl

/-- A sentence's interpretation holds in `M` iff the sentence holds in the domain. -/
theorem models_intT_iff (σ : Sentence (setTemplateLanguage k arities)) :
    M↓[setTemplateLanguage k arities] ⊧ intT σ ↔ (SD M)↓[setTemplateLanguage k arities] ⊧ σ := by
  simp only [models_iff]
  have h := eval_intT (M := M) (ξ := Empty) σ (![] : Fin 0 → SD M) Empty.elim
  have e1 : (Subtype.val ∘ (![] : Fin 0 → SD M)) = ![] := funext fun i ↦ i.elim0
  have e2 : (Subtype.val ∘ (Empty.elim : Empty → SD M)) = Empty.elim := funext fun e ↦ e.elim
  rw [e1, e2] at h
  rw [show (![] : Fin 0 → M) = fun i ↦ i.elim0 from funext fun i ↦ i.elim0,
    show (![] : Fin 0 → SD M) = fun i ↦ i.elim0 from funext fun i ↦ i.elim0] at h
  exact h

end SD

/-! ## The unary template -/

abbrev ar1 : Fin 1 → ℕ := fun _ ↦ 1
abbrev SL := setTemplateLanguage 1 ar1

local instance : Language.Mem SL := ⟨Sum.inl Language.Set.Rel.mem⟩

/-- The placeholder atom `R(#0)`. -/
def R1 : Semisentence SL 1 := SchemaSourceSyntax.R1

/-- The congruence law of `R`. -/
def cong1 : Sentence SL := setPlaceholderCongruenceSentence 1 ar1 0

/-- The separation body for `R`. -/
def sepS : Sentence SL := SchemaSourceSyntax.sepS

/-- **The separation template.** -/
def sepT : Sentence SL := intT cong1 🡒 intT sepS

/-- The GIC matrix `u ∈ &0 ∧ v = u ∧ R u` (`u = #0`, `v = #1`). -/
def sepMat : Semiproposition SL 2 := SchemaSourceSyntax.sepMat

theorem sepT_provable : templN 1 ar1 ⊢ sepT := by
  apply templ_provableN
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* nativeTheory := pure_modelsN (k := 1) (arities := ar1)
  simp only [sepT, Semantics.Imp.models_imply, models_intT_iff]
  intro hc
  simp [models_iff, cong1, setPlaceholderCongruenceSentence, Theory.Eq.relExt, Matrix.conj,
    Semiformula.Operator.eq_def, Matrix.constant_eq_singleton] at hc
  have cong : ∀ x y : M, D x → D y → Eqv x y →
      Structure.rel (L := SL) (placeholderRel 0) ![x] → Structure.rel (L := SL) (placeholderRel 0) ![y] :=
    fun x y hx hy hxy hr ↦ hc ![⟨x, hx⟩, ⟨y, hy⟩] hxy hr
  simp [models_iff, sepS, R1, Semiformula.Operator.mem_def, Matrix.constant_eq_singleton]
  intro x hx
  obtain ⟨b, hb1, hb2⟩ := gic_iffN (k := 1) (arities := ar1) sepMat (fun _ ↦ x) x
  simp [sepMat, SchemaSourceSyntax.sepMat] at hb1 hb2
  exact ⟨b, SchemaSourceSyntax.separation_witness (memRel M) D Eqv
    (fun v ↦ Structure.rel (L := SL) (placeholderRel 0) ![v])
    (fun h hv ↦ D_mem h hv) (fun h ↦ D_closed h) (fun h ↦ eqv_symm h)
    cong hx hb1 (fun u hu hR ↦ (hb2 u hu hR).1)⟩

/-! ## The binary template -/

abbrev ar2 : Fin 1 → ℕ := fun _ ↦ 2
abbrev RL := setTemplateLanguage 1 ar2

/-- The placeholder atom `R(#0, #1)`. -/
def R2 : Semisentence RL 2 := SchemaSourceSyntax.R2

/-- The congruence law of `R`. -/
def cong2 : Sentence RL := setPlaceholderCongruenceSentence 1 ar2 0

/-- The (globally total) replacement body for `R`. -/
def repS : Sentence RL := SchemaSourceSyntax.repS

/-- **The replacement template.** -/
def replT : Sentence RL := intT cong2 🡒 intT repS

/-- The GIC matrix `u ∈ &0 ∧ D v ∧ R u v` (`u = #0`, `v = #1`). -/
def repMat : Semiproposition RL 2 := SchemaSourceSyntax.repMat domS

lemma eval_repMat {M : Type} [Nonempty M] [SetStructure M]
    [s : Structure RL M] [Structure.Eq RL M] [Structure.Mem RL M] [M↓[ℒₛₑₜ] ⊧* nativeTheory]
    (f : ℕ → M) (u v : M) :
    repMat.Eval ![u, v] f ↔ u ∈ f 0 ∧ D v ∧ Structure.rel (L := RL) (placeholderRel 0) ![u, v] :=
  SchemaSourceSyntax.eval_repMat domS f u v

lemma vec2_val {M : Type} [Nonempty M] [SetStructure M] [M↓[ℒₛₑₜ] ⊧* nativeTheory] (p q : SD M) :
    (fun j ↦ ((![p, q] : Fin 2 → SD M) j).1) = ![p.1, q.1] :=
  funext fun j ↦ by match j with | 0 => rfl | 1 => rfl

theorem replT_provable : templN 1 ar2 ⊢ replT := by
  apply templ_provableN
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* nativeTheory := pure_modelsN (k := 1) (arities := ar2)
  simp only [replT, Semantics.Imp.models_imply, models_intT_iff]
  intro hc
  simp [models_iff, cong2, setPlaceholderCongruenceSentence, Theory.Eq.relExt, Matrix.conj,
    Matrix.vecTail, Semiformula.Operator.eq_def] at hc
  let Rr : M → M → Prop := fun u v ↦ Structure.rel (L := RL) (placeholderRel 0) ![u, v]
  have cong : ∀ x1 x2 y1 y2 : M, D x1 → D x2 → D y1 → D y2 → Eqv x1 y1 → Eqv x2 y2 →
      Rr x1 x2 → Rr y1 y2 := by
    intro x1 x2 y1 y2 h1 h2 h3 h4 e1 e2 hr
    have key := hc ![⟨x1, h1⟩, ⟨x2, h2⟩, ⟨y1, h3⟩, ⟨y2, h4⟩] e1 e2
      (by
        convert hr using 2
        rename_i j
        match j with | 0 => rfl | 1 => rfl)
    convert key using 2
    rename_i j
    match j with | 0 => rfl | 1 => rfl
  simp [models_iff, repS, R2, Semiformula.Operator.mem_def, Semiformula.Operator.eq_def,
    FirstOrder.Semiformula.existsUnique, FirstOrder.Semiformula.bexsMem, LO.FirstOrder.bexs,
    vec2_val]
  intro hf X hX
  obtain ⟨b, hb1, hb2⟩ := gic_iffN (k := 1) (arities := ar2) repMat (fun _ ↦ X) X
  simp only [eval_repMat] at hb1 hb2
  exact ⟨b, SchemaSourceSyntax.replacement_witness (memRel M) D Eqv Rr
    (fun h hv ↦ D_mem h hv) (fun h ↦ D_closed h) eqv_refl
    (fun h ↦ eqv_symm h) (fun h₁ h₂ ↦ eqv_trans h₁ h₂)
    cong hf hX hb1 hb2⟩

end LeanProofs.ZFCinPA.NativeSchemaSem
