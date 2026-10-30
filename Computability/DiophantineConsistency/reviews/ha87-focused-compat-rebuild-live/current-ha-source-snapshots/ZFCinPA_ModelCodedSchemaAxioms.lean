import ZFCinPA.ZFDelta1
import ZFCinPA.FiniteTheoryRecognizer
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed

/-!
Literal represented Separation/Replacement axiom constructors for shift-fixed
internal set-language matrices. The code may be nonstandard. IΣ1 suffices for
the arithmetic metamodel; no model of the object set theory is assumed.

Shift-fixedness is retained explicitly: this does not implement arbitrary
free-parameter closure, L/WF relativization, internal source-proof translation,
or a C254/ZFC consistency comparison.
-/
namespace LeanProofs.ZFCinPA.ModelCodedSchemaAxioms

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA
open scoped LO.FirstOrder.Arithmetic
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Direct all-internal recognizer witnesses, rather than Nat quote inversion. -/
lemma schemaRecognizer_of_closed_body {a : Nat} (bodyVal : V → V)
    (K : Semiformula V ℒₛₑₜ a) (body : Formula V ℒₛₑₜ)
    (hshift : body.shift = body) (hbody : bodyVal K.val = body.val)
    (hbound : K.val ≤ body.val) :
    SchemaRecognizer ℒₛₑₜ a bodyVal body.val := by
  have he : subst ℒₛₑₜ (fvarVec (0 : V)) body.val = body.val := by
    rw [fvarVec_zero]
    change (body.subst (![] : SemitermVec V ℒₛₑₜ 0 0)).val = body.val
    simp
  refine ⟨0, by simp, body.val, le_rfl, by simp, body.isUFormula,
    ?_, ?_, K.val, ?_, K.isSemiformula, ?_⟩
  · exact congrArg Semiformula.val hshift
  · have hb : bv ℒₛₑₜ body.val ≤ 0 := by simpa using body.isSemiformula.bv_le
    exact le_antisymm hb (by simp)
  · simpa only [he] using hbound
  · exact he.trans hbody.symm

/-- The embedded identity vector has the same raw code at target level3. -/
lemma sep_core_subst_identity (K : Semiformula V ℒₛₑₜ 1) :
    subst ℒₛₑₜ (sepSubstConst : V) K.val = K.val := by
  have hv : (sepSubstConst : V) = (^#0 ∷ 0) := by
    rw [val_sepSubstConst]
    simp
  rw [hv]
  exact Bootstrapping.subst_eq_self K.isSemiformula (by simp) (by simp)

/-- The collection-clause vector is the raw identity on both core slots. -/
lemma rep_core_subst_identity (K : Semiformula V ℒₛₑₜ 2) :
    subst ℒₛₑₜ (repSubst3Const : V) K.val = K.val := by
  have hv : (repSubst3Const : V) = (^#0 ∷ (^#1 ∷ 0)) := by
    rw [val_repSubst3Const]
    simp
  rw [hv]
  apply Bootstrapping.subst_eq_self K.isSemiformula (by simp)
  intro i hi
  have hi' : i < (2 : V) := by simpa using hi
  rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hi') with rfl | rfl <;> simp

lemma sep_body_shift_fixed (K : Semiformula V ℒₛₑₜ 1) (hK : K.shift = K) :
    (sepBody K).shift = sepBody K := by
  have hZY : (⌜sepAtomZY⌝ : Semiformula V ℒₛₑₜ 3).shift = ⌜sepAtomZY⌝ := by
    rw [← FirstOrder.Semiformula.typed_quote_shift]
    rfl
  have hZX : (⌜sepAtomZX⌝ : Semiformula V ℒₛₑₜ 3).shift = ⌜sepAtomZX⌝ := by
    rw [← FirstOrder.Semiformula.typed_quote_shift]
    rfl
  simp only [sepBody, Semiformula.shift_all, Semiformula.shift_exs,
    Semiformula.shift_iff, Semiformula.shift_and, hZY, hZX,
    Semiformula.shift_substs, hK]
  simp

lemma rep_body_shift_fixed (K : Semiformula V ℒₛₑₜ 2) (hK : K.shift = K) :
    (repBody K).shift = repBody K := by
  have hEq : (⌜repAtomEq⌝ : Semiformula V ℒₛₑₜ 3).shift = ⌜repAtomEq⌝ := by
    rw [← FirstOrder.Semiformula.typed_quote_shift]
    rfl
  have hYY : (⌜repAtomYY⌝ : Semiformula V ℒₛₑₜ 3).shift = ⌜repAtomYY⌝ := by
    rw [← FirstOrder.Semiformula.typed_quote_shift]
    rfl
  have hXX : (⌜repAtomXX⌝ : Semiformula V ℒₛₑₜ 4).shift = ⌜repAtomXX⌝ := by
    rw [← FirstOrder.Semiformula.typed_quote_shift]
    rfl
  simp only [repBody, Semiformula.shift_all, Semiformula.shift_exs,
    Semiformula.shift_imp, Semiformula.shift_iff, Semiformula.shift_and,
    hEq, hYY, hXX, Semiformula.shift_substs, hK]
  simp

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma union_class_iff (T U : Theory ℒₛₑₜ) [T.Δ₁] [U.Δ₁] (p : V) :
    p ∈ (T ∪ U).Δ₁Class ↔ p ∈ T.Δ₁Class ∨ p ∈ U.Δ₁Class := FiniteTheoryRecognizer.union_class_iff T U p

lemma separation_class_iff (p : V) :
    p ∈ separationTheory.Δ₁Class ↔ SepR p := by
  change (V ⊧/![p] sepCh.val) ↔ _
  simp

lemma replacement_class_iff (p : V) :
    p ∈ replacementTheory.Δ₁Class ↔ RepR p := by
  change (V ⊧/![p] repCh.val) ↔ _
  simp

/-- An internal ZF axiom is an equality, fixed, separation, or replacement axiom. -/
lemma mem_ZF_class {p : V} (h : p ∈ (𝗭𝗙 : SetTheory).Δ₁Class) :
    p ∈ (𝗘𝗤 ℒₛₑₜ : SetTheory).Δ₁Class ∨ p ∈ zfFixed.Δ₁Class ∨ SepR p ∨ RepR p := by
  change p ∈ (𝗘𝗤 ℒₛₑₜ ∪ zfFixed ∪ separationTheory ∪ replacementTheory : SetTheory).Δ₁Class at h
  simpa only [union_class_iff, separation_class_iff, replacement_class_iff, or_assoc] using h

/-- Actual internal ZF axiom membership for every shift-fixed unary code. -/
theorem sepBody_mem_zf_of_shift_fixed (K : Semiformula V ℒₛₑₜ 1)
    (hK : K.shift = K) : (sepBody K).val ∈ (𝗭𝗙 : SetTheory).Δ₁Class := by
  have hs : SepR (sepBody K).val := by
    apply schemaRecognizer_of_closed_body sepBodyVal K (sepBody K)
      (sep_body_shift_fixed K hK) (sepBodyVal_eq K)
    have h := subst_le_sepBodyVal K.val
    rw [sep_core_subst_identity K, sepBodyVal_eq K] at h
    exact h
  change (sepBody K).val ∈
    (((𝗘𝗤 ℒₛₑₜ ∪ zfFixed) ∪ separationTheory) ∪ replacementTheory).Δ₁Class
  rw [union_class_iff, union_class_iff, union_class_iff]
  exact Or.inl (Or.inr ((separation_class_iff _).mpr hs))

/-- Actual internal ZF axiom membership for every shift-fixed binary code. -/
theorem repBody_mem_zf_of_shift_fixed (K : Semiformula V ℒₛₑₜ 2)
    (hK : K.shift = K) : (repBody K).val ∈ (𝗭𝗙 : SetTheory).Δ₁Class := by
  have hs : RepR (repBody K).val := by
    apply schemaRecognizer_of_closed_body repBodyVal K (repBody K)
      (rep_body_shift_fixed K hK) (repBodyVal_eq K)
    have h := subst3_le_repBodyVal K.val
    rw [rep_core_subst_identity K, repBodyVal_eq K] at h
    exact h
  change (repBody K).val ∈
    (((𝗘𝗤 ℒₛₑₜ ∪ zfFixed) ∪ separationTheory) ∪ replacementTheory).Δ₁Class
  rw [union_class_iff]
  exact Or.inr ((replacement_class_iff _).mpr hs)

/-- Preserve the literal represented axiom proof, without changing its recognizer. -/
private lemma axiom_isProof (T : Theory ℒₛₑₜ) [T.Δ₁] (φ : Formula V ℒₛₑₜ)
    (hm : φ.val ∈ T.Δ₁Class) :
    Proof T (TProof.byAxm (T := T.internalize V) hm).val φ.val := by
  simp only [TProof.byAxm, TDerivation.byAxm_val, Sequent.val_insert, Sequent.val_empty]
  change DerivationOf T (axm (insert φ.val ∅) φ.val) {φ.val}
  refine ⟨?_, Derivation.axm (by simp) (by simp) hm⟩
  simp

noncomputable def zfSeparationProof (K : Semiformula V ℒₛₑₜ 1) (hK : K.shift = K) :
    (𝗭𝗙 : SetTheory).internalize V ⊢! sepBody K :=
  TProof.byAxm (sepBody_mem_zf_of_shift_fixed K hK)

noncomputable def zfReplacementProof (K : Semiformula V ℒₛₑₜ 2) (hK : K.shift = K) :
    (𝗭𝗙 : SetTheory).internalize V ⊢! repBody K :=
  TProof.byAxm (repBody_mem_zf_of_shift_fixed K hK)

theorem zfSeparationProof_isProof (K : Semiformula V ℒₛₑₜ 1) (hK : K.shift = K) :
    Proof (𝗭𝗙 : SetTheory) (zfSeparationProof K hK).val (sepBody K).val := by
  exact axiom_isProof _ _ _

theorem zfReplacementProof_isProof (K : Semiformula V ℒₛₑₜ 2) (hK : K.shift = K) :
    Proof (𝗭𝗙 : SetTheory) (zfReplacementProof K hK).val (repBody K).val := by
  exact axiom_isProof _ _ _

noncomputable def zfcSeparationProof (K : Semiformula V ℒₛₑₜ 1) (hK : K.shift = K) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! sepBody K :=
  TProof.byAxm ((union_class_iff (𝗭𝗙 : SetTheory) 𝗔𝗖 _).mpr
    (Or.inl (sepBody_mem_zf_of_shift_fixed K hK)))

noncomputable def zfcReplacementProof (K : Semiformula V ℒₛₑₜ 2) (hK : K.shift = K) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! repBody K :=
  TProof.byAxm ((union_class_iff (𝗭𝗙 : SetTheory) 𝗔𝗖 _).mpr
    (Or.inl (repBody_mem_zf_of_shift_fixed K hK)))

theorem zfcSeparationProof_isProof (K : Semiformula V ℒₛₑₜ 1) (hK : K.shift = K) :
    Proof (𝗭𝗙𝗖 : SetTheory) (zfcSeparationProof K hK).val (sepBody K).val := by
  exact axiom_isProof _ _ _

theorem zfcReplacementProof_isProof (K : Semiformula V ℒₛₑₜ 2) (hK : K.shift = K) :
    Proof (𝗭𝗙𝗖 : SetTheory) (zfcReplacementProof K hK).val (repBody K).val := by
  exact axiom_isProof _ _ _

end LeanProofs.ZFCinPA.ModelCodedSchemaAxioms
