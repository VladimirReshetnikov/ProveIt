import ZFCinPA.LReplBase

set_option autoImplicit false
noncomputable section

/-!
# Choice transport in arithmetic: `Con(ZF) → Con(ZFC)`

`hSchema`, the last hypothesis of
`ConstructibleInterpretation.provable_falsum_ZF_of_ZFC`, holds in every model
of `𝗜𝚺₁`: every internal separation or replacement axiom code has an internal
`𝗭𝗙`-derivation of its relativization to `L`, with no side formulas
(`LSepBase.sep_obligation`, `LReplBase.repl_obligation`). Hence internal
`𝗭𝗙𝗖`-refutations yield internal `𝗭𝗙`-refutations (`provable_falsum_ZF_of_ZFC`),
and by completeness

`𝗜𝚺₁ ⊢ Con(𝗭𝗙) → Con(𝗭𝗙𝗖)` (`iSigma1_proves_con_ZF_imp_con_ZFC`),

so also `𝗣𝗔 ⊢ Con(𝗭𝗙) → Con(𝗭𝗙𝗖)` (`peano_proves_con_ZF_imp_con_ZFC`).
-/

namespace LeanProofs.ZFCinPA.LSchema

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.BoundedPAConsistency.InternalRelativization
open LeanProofs.ZFCinPA.ConstructibleInterpretation (domL)
open scoped LO.FirstOrder.Arithmetic

section Internal

variable {W : Type} [ORingStructure W] [W↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma separation_class_iff (p : W) : p ∈ separationTheory.Δ₁Class ↔ SepR p := by
  change (W ⊧/![p] sepCh.val) ↔ _
  simp

lemma replacement_class_iff (p : W) : p ∈ replacementTheory.Δ₁Class ↔ RepR p := by
  change (W ⊧/![p] repCh.val) ↔ _
  simp

/-- **`hSchema`**: every internal separation or replacement axiom code has an
internal `𝗭𝗙`-derivation of its relativization to `L` (no side formulas). -/
theorem hSchema : ∀ p : W, IsFormula ℒₛₑₜ p →
    p ∈ separationTheory.Δ₁Class ∨ p ∈ replacementTheory.Δ₁Class →
    ∃ m, Derivable 𝗭𝗙 (insert (relativize ℒₛₑₜ (⌜domL⌝ : W) p) (domSet ℒₛₑₜ (⌜domL⌝ : W) m)) := by
  intro p _ h
  refine ⟨0, ?_⟩
  have hempty : domSet ℒₛₑₜ (⌜domL⌝ : W) 0 = ∅ := mem_ext fun y => by simp [mem_domSet_iff]
  rw [hempty]
  rcases h with h | h
  · exact (LSepBase.sep_obligation ((separation_class_iff p).1 h)).toDerivable
  · exact (LReplBase.repl_obligation ((replacement_class_iff p).1 h)).toDerivable

/-- **Choice transport in `IΣ₁`.** In every model of `𝗜𝚺₁`, an internal
`𝗭𝗙𝗖`-refutation yields an internal `𝗭𝗙`-refutation. -/
theorem provable_falsum_ZF_of_ZFC (h : Bootstrapping.Provable 𝗭𝗙𝗖 (^⊥ : W)) :
    Bootstrapping.Provable 𝗭𝗙 (^⊥ : W) :=
  ConstructibleInterpretation.provable_falsum_ZF_of_ZFC hSchema h

theorem consistent_ZFC_of_ZF (h : (𝗭𝗙 : SetTheory).Consistent W) :
    (𝗭𝗙𝗖 : SetTheory).Consistent W := by
  have e : (⌜(⊥ : Sentence ℒₛₑₜ)⌝ : W) = ^⊥ := by
    simp [LO.FirstOrder.Sentence.quote_def, LO.FirstOrder.Semiformula.quote_def]
  intro hZFC
  apply h
  unfold LO.FirstOrder.Theory.Consistent at *
  rw [e] at hZFC ⊢
  exact provable_falsum_ZF_of_ZFC hZFC

/-- Internally, `𝗭𝗙`'s axiom class is contained in `𝗭𝗙𝗖`'s. -/
lemma zf_subset_zfc : (𝗭𝗙 : SetTheory).internalize W ⊆ (𝗭𝗙𝗖 : SetTheory).internalize W :=
  fun _ hp ↦ ConstructibleInterpretation.mem_class_union.mpr (Or.inl hp)

/-- An internal `𝗭𝗙`-refutation is an internal `𝗭𝗙𝗖`-refutation. -/
theorem provable_falsum_ZFC_of_ZF (h : Bootstrapping.Provable 𝗭𝗙 (^⊥ : W)) :
    Bootstrapping.Provable 𝗭𝗙𝗖 (^⊥ : W) := by
  have h' : (𝗭𝗙 : SetTheory).internalize W ⊢ (⊥ : Bootstrapping.Formula W ℒₛₑₜ) :=
    Bootstrapping.tprovable_iff_provable.mpr (by simpa using h)
  simpa using Bootstrapping.tprovable_iff_provable.mp (Bootstrapping.TProof.of_subset zf_subset_zfc h')

theorem consistent_ZF_of_ZFC (h : (𝗭𝗙𝗖 : SetTheory).Consistent W) :
    (𝗭𝗙 : SetTheory).Consistent W := by
  have e : (⌜(⊥ : Sentence ℒₛₑₜ)⌝ : W) = ^⊥ := by
    simp [LO.FirstOrder.Sentence.quote_def, LO.FirstOrder.Semiformula.quote_def]
  intro hZF
  apply h
  unfold LO.FirstOrder.Theory.Consistent at *
  rw [e] at hZF ⊢
  exact provable_falsum_ZFC_of_ZF hZF

end Internal

/-- **`𝗜𝚺₁ ⊢ Con(𝗭𝗙) → Con(𝗭𝗙𝗖)`.** -/
theorem iSigma1_proves_con_ZF_imp_con_ZFC :
    𝗜𝚺₁ ⊢ ((𝗭𝗙 : SetTheory).consistent : ArithmeticSentence) 🡒 (𝗭𝗙𝗖 : SetTheory).consistent := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ hM
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := hM
  simp only [Semantics.Imp.models_imply]
  intro h
  have h' : (𝗭𝗙 : SetTheory).Consistent M := by simpa [models_iff] using h
  simpa [models_iff] using consistent_ZFC_of_ZF h'

/-- **`𝗜𝚺₁ ⊢ Con(𝗭𝗙) ↔ Con(𝗭𝗙𝗖)`.** -/
theorem iSigma1_proves_con_ZF_iff_con_ZFC :
    𝗜𝚺₁ ⊢ ((𝗭𝗙 : SetTheory).consistent : ArithmeticSentence) 🡘 (𝗭𝗙𝗖 : SetTheory).consistent := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ hM
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := hM
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' : (𝗭𝗙 : SetTheory).Consistent M := by simpa [models_iff] using h
    simpa [models_iff] using consistent_ZFC_of_ZF h'
  · have h' : (𝗭𝗙𝗖 : SetTheory).Consistent M := by simpa [models_iff] using h
    simpa [models_iff] using consistent_ZF_of_ZFC h'

/-- **`𝗣𝗔 ⊢ Con(𝗭𝗙) ↔ Con(𝗭𝗙𝗖)`.** -/
theorem peano_proves_con_ZF_iff_con_ZFC :
    𝗣𝗔 ⊢ ((𝗭𝗙 : SetTheory).consistent : ArithmeticSentence) 🡘 (𝗭𝗙𝗖 : SetTheory).consistent :=
  Entailment.WeakerThan.pbl iSigma1_proves_con_ZF_iff_con_ZFC

/-- **`𝗣𝗔 ⊢ Con(𝗭𝗙) → Con(𝗭𝗙𝗖)`.** -/
theorem peano_proves_con_ZF_imp_con_ZFC :
    𝗣𝗔 ⊢ ((𝗭𝗙 : SetTheory).consistent : ArithmeticSentence) 🡒 (𝗭𝗙𝗖 : SetTheory).consistent :=
  Entailment.WeakerThan.pbl iSigma1_proves_con_ZF_imp_con_ZFC

end LeanProofs.ZFCinPA.LSchema
