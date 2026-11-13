import ZFCinPA.QSchema
import ZFCinPA.LSchema

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! # Internal ZF/ZFC refutations become actual C222 refutations

In every model of `𝗜𝚺₁`, an internal `𝗭𝗙𝗖`-refutation becomes an internal
`𝗭𝗙`-refutation (`LSchema`, the constructible interpretation), then a
refutation in the quotient-interface theory `qTheory` (the well-founded
quotient interpretation `QSchema`), then a refutation in the concrete C222
seed theory (`ValidatorSeedQTheory222`, the moving-marker tagged
interpretation), and finally an actual C222 History222 value-two witness.
No step uses standard-model truth: every transformation acts on arbitrary
internal codes of the model.
-/
namespace LeanProofs.ZFCinPA.ValidatorConsistencyLower222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open scoped LO.FirstOrder.Arithmetic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **An internal `𝗭𝗙`-refutation yields an actual C222 refutation.** -/
theorem refutation222_of_ZF (h : Bootstrapping.Provable (𝗭𝗙 : SetTheory) (^⊥ : V)) :
    ∃ d : V, _root_.SetTheory.BusyBeaver.ZFC.ArithmeticHistory222.value d = 2 :=
  ValidatorSeedQTheory222.qTheory_refutation_witness (QSchema.provable_falsum_native_of_ZF h)

/-- **An internal `𝗭𝗙𝗖`-refutation yields an actual C222 refutation.** -/
theorem refutation222_of_ZFC (h : Bootstrapping.Provable (𝗭𝗙𝗖 : SetTheory) (^⊥ : V)) :
    ∃ d : V, _root_.SetTheory.BusyBeaver.ZFC.ArithmeticHistory222.value d = 2 :=
  refutation222_of_ZF (LSchema.provable_falsum_ZF_of_ZFC h)

/-- The same, at the level of Foundation's consistency sentence. -/
theorem refutation222_of_not_consistent
    (h : ¬ ((𝗭𝗙𝗖 : SetTheory).consistent : ArithmeticSentence).Evalb (M := V) ![]) :
    ∃ d : V, _root_.SetTheory.BusyBeaver.ZFC.ArithmeticHistory222.value d = 2 := by
  apply refutation222_of_ZFC
  simp only [consistent.defined] at h
  have hb := not_not.mp h
  simpa [Sentence.quote_def, Semiformula.quote_def] using hb

end LeanProofs.ZFCinPA.ValidatorConsistencyLower222
