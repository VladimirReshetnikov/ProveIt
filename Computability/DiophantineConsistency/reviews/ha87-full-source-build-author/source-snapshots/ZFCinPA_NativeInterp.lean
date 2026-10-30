import ZFCinPA.InternalInterpretation
import ZFCinPA.ConstructibleInterpretation
import ZFCinPA.NativeTheory
import BusyBeaver.ZFC.WFModel

set_option autoImplicit false
noncomputable section

/-!
# The well-founded interpretation of `𝗭𝗙` in the native theory (`R3`), semantics

The external comparison `WFTheory.c254_of_zf_refutation` reads `𝗭𝗙` in every
native CP/GIC model `M` through two steps: the bisimulation quotient `M/≈`
(`QuotientModel`), and its internally well-founded part
(`WellFoundedPart.Domain`, a model of `𝗭𝗙` by `WFModel.quotient_models_ZF`).
Composed, this is one interpretation of `ℒₛₑₜ` in `M`:

* domain `domS(x)`: the class of `x` is well-founded in the quotient
  (the quotient translation of `wfForm`);
* `x = y` read as bisimilarity `eqS`, `x ∈ y` as membership up to
  bisimilarity `memS`.

All three are closed `ℒₛₑₜ` sentences obtained from the native forms by
`toSet`, so their meanings come from `eval_toSet`. `intF` is the meta-level
interpretation, clause for clause the internal `InternalInterpretation.interp`;
`eval_intF` evaluates it in `M` as the original formula in the well-founded
part of the quotient, sending each element to its class.
-/

namespace LeanProofs.ZFCinPA.NativeInterp

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA
open SetTheory.BusyBeaver.ZFC

/-- Close a translated native formula with at least one bound slot: any free
variable goes to `#0` (none occurs in the forms used here). -/
def closeS {k : ℕ} (φ : SetTheorySemiproposition (k + 1)) : Semisentence ℒₛₑₜ (k + 1) :=
  Rew.rewrite (fun _ ↦ (#0 : Semiterm ℒₛₑₜ Empty (k + 1))) ▹ φ

/-- Bisimilarity, `#0 ≈ #1`. -/
def eqS : Semisentence ℒₛₑₜ 2 := closeS (toSet 2 (ProfileSyntax.eqvForm 0 1))

/-- Membership up to bisimilarity, `#0 ∈≈ #1`. -/
def memS : Semisentence ℒₛₑₜ 2 := closeS (toSet 2 (QuotientModel.memberForm 0 1))

/-- The well-founded part of the quotient. -/
def domS : Semisentence ℒₛₑₜ 1 :=
  closeS (toSet 1 (QuotientModel.translate (WellFoundedPart.wfForm 0)))

/-! ## The meta-level interpretation -/

/-- The meaning of an atom. -/
def atomI {ξ : Type*} {n k : ℕ} : (ℒₛₑₜ).Rel k → (Fin k → Semiterm ℒₛₑₜ ξ n) → Semiformula ℒₛₑₜ ξ n
  | .eq, v => Rew.embSubsts v ▹ eqS
  | .mem, v => Rew.embSubsts v ▹ memS

/-- The domain guard at the newest bound variable. -/
def domAtS {ξ : Type*} (n : ℕ) : Semiformula ℒₛₑₜ ξ (n + 1) := Rew.embSubsts ![#0] ▹ domS

/-- The interpretation, clause for clause `InternalInterpretation.interp`. -/
def intF {ξ : Type*} : {n : ℕ} → Semiformula ℒₛₑₜ ξ n → Semiformula ℒₛₑₜ ξ n
  | _, .rel R v => atomI R v
  | _, .nrel R v => ∼atomI R v
  | _, ⊤ => ⊤
  | _, ⊥ => ⊥
  | _, φ ⋏ ψ => intF φ ⋏ intF ψ
  | _, φ ⋎ ψ => intF φ ⋎ intF ψ
  | n, ∀⁰ φ => ∀⁰ (∼domAtS n ⋎ intF φ)
  | n, ∃⁰ φ => ∃⁰ (domAtS n ⋏ intF φ)

/-! ## Semantics in a model of the native theory -/

section Semantics

variable {M : Type} [Nonempty M] [SetStructure M] [M↓[ℒₛₑₜ] ⊧* NativeSet.nativeTheory]

theorem eval_closeS {k : ℕ} (φ : SetTheorySemiproposition (k + 1)) (b : Fin (k + 1) → M)
    (ε : Empty → M) : (closeS φ).Eval b ε ↔ φ.Eval b (fun _ ↦ b 0) := by
  simp [closeS, Semiformula.eval_rewrite]

theorem eval_eqS (x y : M) (ε : Empty → M) :
    eqS.Eval ![x, y] ε ↔ ProfileCollection.Eqv (memRel M) x y := by
  rw [eqS, eval_closeS]
  exact (eval_toSet_pair (ProfileSyntax.eqvForm 0 1) x y (fun _ ↦ x)).trans (ProfileSyntax.sat_eqvForm _ _ 0 1)

theorem eval_memS (x y : M) (ε : Empty → M) :
    memS.Eval ![x, y] ε ↔ ProfileComposition.Member (memRel M) x y := by
  rw [memS, eval_closeS]
  exact (eval_toSet_pair (QuotientModel.memberForm 0 1) x y (fun _ ↦ x)).trans (QuotientModel.sat_memberForm _ _ 0 1)

/-- The native CP/GIC structure of `M` and an explicit inhabitant. -/
abbrev hM : ProfileModel.ModelsCPGIC (memRel M) := NativeSet.models_cpgic.1
abbrev wM : M := Classical.arbitrary M

/-- The quotient membership. -/
abbrev qm : QuotientModel.Domain (memRel M) wM hM → QuotientModel.Domain (memRel M) wM hM → Prop :=
  QuotientModel.quotientMember (memRel M) wM hM

/-- The class of an element. -/
abbrev cl (x : M) : QuotientModel.Domain (memRel M) wM hM := QuotientModel.mk (memRel M) wM hM x

theorem eval_domS (x : M) (ε : Empty → M) :
    domS.Eval ![x] ε ↔ WellFoundedPart.WF (qm (M := M)) (cl x) := by
  rw [domS, eval_closeS]
  simp only [Matrix.cons_val_zero]
  refine (eval_toSet_single _ x (fun _ ↦ x)).trans ?_
  rw [QuotientModel.sat_translate, ← QuotientModel.sat_quotient (memRel M) wM hM,
    WellFoundedPart.sat_wfForm]
  rfl

theorem eval_eqS' (w : Fin 2 → M) (ε : Empty → M) :
    eqS.Eval w ε ↔ ProfileCollection.Eqv (memRel M) (w 0) (w 1) := by
  rw [show w = ![w 0, w 1] from funext fun i ↦ by match i with | 0 => rfl | 1 => rfl]
  exact eval_eqS _ _ ε

theorem eval_memS' (w : Fin 2 → M) (ε : Empty → M) :
    memS.Eval w ε ↔ ProfileComposition.Member (memRel M) (w 0) (w 1) := by
  rw [show w = ![w 0, w 1] from funext fun i ↦ by match i with | 0 => rfl | 1 => rfl]
  exact eval_memS _ _ ε

/-- The domain predicate on `M`. -/
abbrev D (x : M) : Prop := domS.Eval ![x] Empty.elim

/-- The well-founded part of the quotient. -/
abbrev WQ (M : Type) [Nonempty M] [SetStructure M] [M↓[ℒₛₑₜ] ⊧* NativeSet.nativeTheory] :=
  WellFoundedPart.Domain (qm (M := M))

instance : SetStructure (WQ M) := ⟨fun s a ↦ WellFoundedPart.domainMem qm a s⟩

/-- The class of a domain element, in the well-founded part. -/
def cls (x : {x : M // D x}) : WQ M := ⟨cl x.1, (eval_domS x.1 Empty.elim).mp x.2⟩

theorem term_cases {ξ : Type*} {n : ℕ} (t : Semiterm ℒₛₑₜ ξ n) (b : Fin n → {x : M // D x})
    (f : ξ → {x : M // D x}) :
    ∃ u : {x : M // D x}, t.val (Subtype.val ∘ b) (Subtype.val ∘ f) = u.1 ∧
      t.val (cls ∘ b) (cls ∘ f) = cls u :=
  ConstructibleInterpretation.term_cases_between Subtype.val cls t b f

theorem val_cons {n : ℕ} (x : {x : M // D x}) (b : Fin n → {x : M // D x}) :
    Subtype.val ∘ (x :> b) = (x.1 :> Subtype.val ∘ b) :=
  Matrix.comp_vecCons Subtype.val x b

theorem cls_cons {n : ℕ} (x : {x : M // D x}) (b : Fin n → {x : M // D x}) :
    cls ∘ (x :> b) = (cls x :> cls ∘ b) :=
  Matrix.comp_vecCons cls x b

theorem eval_domAtS {ξ : Type*} {n : ℕ} (x : M) (e : Fin n → M) (ε : ξ → M) :
    (domAtS n : Semiformula ℒₛₑₜ ξ (n + 1)).Eval (x :> e) ε ↔ D x := by
  simp [domAtS, Semiformula.eval_embSubsts, Matrix.constant_eq_singleton]

theorem eval_atomI {ξ : Type*} {n k : ℕ} (R : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ ξ n)
    (b : Fin n → {x : M // D x}) (f : ξ → {x : M // D x}) :
    (atomI R v).Eval (Subtype.val ∘ b) (Subtype.val ∘ f) ↔
      (Semiformula.rel R v).Eval (cls ∘ b) (cls ∘ f) := by
  refine ConstructibleInterpretation.eval_paramAtom cls eqS memS (ProfileCollection.Eqv (memRel M))
    (ProfileComposition.Member (memRel M)) eval_eqS' eval_memS' ?_ ?_ R v b f
  · intro u w
    rw [← QuotientModel.mk_eq_iff (memRel M) wM hM]
    exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
  · intro u w
    rfl

private theorem cls_surj : Function.Surjective (cls (M := M)) := by
  rintro ⟨q, hq⟩
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  have hx : D x := (eval_domS x Empty.elim).mpr hq
  exact ⟨⟨x, hx⟩, rfl⟩

/-- **Evaluation of the interpretation**: in a model of the native theory, the
interpretation of `φ` at domain elements holds iff `φ` holds at their classes
in the well-founded part of the quotient. -/
theorem eval_intF {ξ : Type*} :
    ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ n) (b : Fin n → {x : M // D x}) (f : ξ → {x : M // D x}),
      (intF φ).Eval (Subtype.val ∘ b) (Subtype.val ∘ f) ↔ φ.Eval (cls ∘ b) (cls ∘ f)
  | _, .rel R v, b, f => eval_atomI R v b f
  | _, .nrel R v, b, f => by
      have h := eval_atomI R v b f
      simp only [intF]
      simp [h]
  | _, ⊤, b, f => by simp [intF]
  | _, ⊥, b, f => by simp [intF]
  | _, φ ⋏ ψ, b, f => by simp [intF, eval_intF φ b f, eval_intF ψ b f]
  | _, φ ⋎ ψ, b, f => by simp [intF, eval_intF φ b f, eval_intF ψ b f]
  | n, ∀⁰ φ, b, f => by
      simp only [intF, Semiformula.eval_all, LogicalConnective.HomClass.map_or,
        LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.or_eq,
        LogicalConnective.Prop.neg_eq, eval_domAtS]
      apply ConstructibleInterpretation.forall_guard cls cls_surj
      intro u
      rw [← val_cons u b, eval_intF φ (u :> b) f, cls_cons]
  | n, ∃⁰ φ, b, f => by
      simp only [intF, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
        LogicalConnective.Prop.and_eq, eval_domAtS]
      apply ConstructibleInterpretation.exists_guard cls cls_surj
      intro u
      rw [← val_cons u b, eval_intF φ (u :> b) f, cls_cons]

end Semantics

/-! ## Codes: the interpretation parameter and the quotation bridge -/

section Codes

open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.InternalInterpretation LeanProofs.BoundedPAConsistency.InternalRelativization

@[simp] lemma intF_rel {ξ : Type*} {n k : ℕ} (R : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ ξ n) :
    intF (.rel R v) = atomI R v := rfl
@[simp] lemma intF_nrel {ξ : Type*} {n k : ℕ} (R : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ ξ n) :
    intF (.nrel R v) = ∼atomI R v := rfl
@[simp] lemma intF_verum {ξ : Type*} {n : ℕ} : intF (⊤ : Semiformula ℒₛₑₜ ξ n) = ⊤ := rfl
@[simp] lemma intF_falsum {ξ : Type*} {n : ℕ} : intF (⊥ : Semiformula ℒₛₑₜ ξ n) = ⊥ := rfl
@[simp] lemma intF_and {ξ : Type*} {n : ℕ} (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    intF (φ ⋏ ψ) = intF φ ⋏ intF ψ := rfl
@[simp] lemma intF_or {ξ : Type*} {n : ℕ} (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    intF (φ ⋎ ψ) = intF φ ⋎ intF ψ := rfl
@[simp] lemma intF_all {ξ : Type*} {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    intF (∀⁰ φ) = ∀⁰ (∼domAtS n ⋎ intF φ) := rfl
@[simp] lemma intF_exs {ξ : Type*} {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    intF (∃⁰ φ) = ∃⁰ (domAtS n ⋏ intF φ) := rfl

variable {W : Type} [ORingStructure W] [W↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **The interpretation parameter** `⟪domain, ⟪equality, membership⟫⟫`. -/
def PN : W := ⟪(⌜domS⌝ : W), ⟪(⌜eqS⌝ : W), (⌜memS⌝ : W)⟫⟫

lemma shift_quote_sen {k : ℕ} (σ : Semisentence ℒₛₑₜ k) : shift ℒₛₑₜ (⌜σ⌝ : W) = ⌜σ⌝ :=
  ConstructibleInterpretation.shift_quote_sen σ

lemma isSemiformula_quote_sen {k : ℕ} (σ : Semisentence ℒₛₑₜ k) :
    IsSemiformula ℒₛₑₜ (k : W) (⌜σ⌝ : W) :=
  ConstructibleInterpretation.isSemiformula_quote_sen σ

@[simp] lemma dom_PN : dom (PN : W) = ⌜domS⌝ := by simp [PN, dom]

lemma atomOf_PN (R : W) : atomOf (PN : W) R = if R = 0 then ⌜eqS⌝ else ⌜memS⌝ := by
  simp [atomOf, PN]

lemma good_PN : Good (PN : W) :=
  ConstructibleInterpretation.good_quoted_parameter domS eqS memS

lemma embSubsts_eq_comp' {ξ : Type*} {n k : ℕ} (v : Fin k → Semiterm ℒₛₑₜ ξ n) :
    (Rew.embSubsts v : Rew ℒₛₑₜ Empty k ξ n) = (Rew.subst v).comp Rew.emb :=
  ConstructibleInterpretation.embSubsts_eq_comp_general v

lemma quote_embSubsts {k n : ℕ} (σ : Semisentence ℒₛₑₜ k) (v : Fin k → SyntacticSemiterm ℒₛₑₜ n) :
    (⌜(Rew.embSubsts v ▹ σ : SetTheorySemiproposition n)⌝ : W) =
      subst ℒₛₑₜ (SemitermVec.val fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm W ℒₛₑₜ n)) ⌜σ⌝ :=
  ConstructibleInterpretation.quote_embSubsts σ v

lemma quote_domAtS (n : ℕ) : (⌜(domAtS n : SetTheorySemiproposition (n + 1))⌝ : W) = ⌜domS⌝ := by
  rw [domAtS, quote_embSubsts]
  exact ConstructibleInterpretation.subst_unary_bvar0 _ (by simp) (by simp)

private theorem quote_intF_rel {n k : ℕ} (R : (ℒₛₑₜ).Rel k)
    (v : Fin k → SyntacticSemiterm ℒₛₑₜ n) :
    (⌜intF (Semiformula.rel R v)⌝ : W) = interp (PN : W) ⌜Semiformula.rel R v⌝ := by
      have h := ConstructibleInterpretation.isUFormula_quote (W := W) (.rel R v : SetTheorySemiproposition _)
      rw [LO.FirstOrder.Semiformula.quote_rel] at h
      rw [intF_rel, LO.FirstOrder.Semiformula.quote_rel,
        interp_rel (IsUFormula.rel.mp h).1 (IsUFormula.rel.mp h).2, atomOf_PN]
      cases R with
      | eq => rw [if_pos (by change ((0 : ℕ) : W) = 0; simp)]; exact quote_embSubsts (W := W) eqS v
      | mem => rw [if_neg (by change ((1 : ℕ) : W) ≠ 0; simp)]; exact quote_embSubsts (W := W) memS v

/-- **The code of the meta interpretation is the internal interpretation.** -/
theorem quote_intF : ∀ {n : ℕ} (φ : SetTheorySemiproposition n),
    (⌜intF φ⌝ : W) = interp (PN : W) ⌜φ⌝
  | _, .rel R v => quote_intF_rel R v
  | _, .nrel R v => by
      change (⌜∼intF (Semiformula.rel R v)⌝ : W) =
        interp (PN : W) ⌜∼(Semiformula.rel R v : SetTheorySemiproposition _)⌝
      rw [ConstructibleInterpretation.quote_neg_set, ConstructibleInterpretation.quote_neg_set,
        ← interp_neg good_PN (LO.FirstOrder.Semiformula.quote_isSemiformula
          (Semiformula.rel R v : SetTheorySemiproposition _)), quote_intF_rel]
  | _, ⊤ => by simp
  | _, ⊥ => by simp
  | _, φ ⋏ ψ => by
      rw [intF_and, LO.FirstOrder.Semiformula.quote_and, LO.FirstOrder.Semiformula.quote_and,
        quote_intF φ, quote_intF ψ,
        interp_and (ConstructibleInterpretation.isUFormula_quote φ)
          (ConstructibleInterpretation.isUFormula_quote ψ)]
  | _, φ ⋎ ψ => by
      rw [intF_or, LO.FirstOrder.Semiformula.quote_or, LO.FirstOrder.Semiformula.quote_or,
        quote_intF φ, quote_intF ψ,
        interp_or (ConstructibleInterpretation.isUFormula_quote φ)
          (ConstructibleInterpretation.isUFormula_quote ψ)]
  | n, ∀⁰ φ => by
      rw [intF_all, LO.FirstOrder.Semiformula.quote_all, LO.FirstOrder.Semiformula.quote_or,
        ConstructibleInterpretation.quote_neg_set, quote_domAtS, quote_intF φ,
        LO.FirstOrder.Semiformula.quote_all, interp_all (ConstructibleInterpretation.isUFormula_quote φ),
        dom_PN]
  | n, ∃⁰ φ => by
      rw [intF_exs, LO.FirstOrder.Semiformula.quote_ex, LO.FirstOrder.Semiformula.quote_and,
        quote_domAtS, quote_intF φ, LO.FirstOrder.Semiformula.quote_ex,
        interp_exs (ConstructibleInterpretation.isUFormula_quote φ), dom_PN]

end Codes

end LeanProofs.ZFCinPA.NativeInterp
