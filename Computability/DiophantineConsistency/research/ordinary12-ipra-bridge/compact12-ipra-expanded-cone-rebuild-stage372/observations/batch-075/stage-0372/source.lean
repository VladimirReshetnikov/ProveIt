import ZFCinPA.R2Fixed
import ZFCinPA.NativeSchema

set_option autoImplicit false
noncomputable section

/-!
# R2 closed: native refutations are validator refutations

Every internal axiom code of `NativeSet.nativeTheory` encodes to a validator
theorem at every odd environment and even stream (`axOK_native`): the equality
axioms, irreflexivity and the container axiom by `R2Fixed`, and every internal
GIC instance by `R2Ax.gic_axiom`. With the generic translation
`R2Main.cProv_falsum_of_provable`, in every model of `𝗜𝚺₂`

`Provable nativeTheory ⊥ → CProv 1`   (`cProv_falsum_of_native`),

and composed with `R3` (`NativeSchema.provable_falsum_native_of_ZF`),

`Provable 𝗭𝗙 ⊥ → CProv 1`   (`cProv_falsum_of_ZF`),

so that `𝗜𝚺₂` and `𝗣𝗔` prove: if the literal validator accepts no proof of
falsity, then `𝗭𝗙` is consistent (`peano_proves_validator_imp_con_ZF`).
-/

namespace LeanProofs.ZFCinPA.R2Native

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorProvability254 LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254
open LeanProofs.ZFCinPA.ValidatorNativeGicSlots254
open LeanProofs.ZFCinPA.NativeSet LeanProofs.ZFCinPA.R2Main
open scoped LO.FirstOrder.Arithmetic

section Internal

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]

/-- **Every internal axiom of the native theory is a validator theorem.** -/
theorem axOK_native : AxOK nativeTheory V := by
  intro p _ hp F s hF hs
  change p ∈ ((𝗘𝗤 ℒₛₑₜ ∪ nativeFixed) ∪ gicTheory : SetTheory).Δ₁Class at hp
  rcases (NTemplate.union_class_iff _ _ p).mp hp with hp | hp
  · rcases (NTemplate.union_class_iff _ _ p).mp hp with hp | hp
    · obtain ⟨σ, hσ, rfl⟩ :=
        ConstructibleInterpretation.mem_ch_ofFinite (𝗘𝗤 ℒₛₑₜ) Theory.EqAxiom.finite hp
      cases hσ with
      | refl => exact R2Fixed.refl_ax F s
      | symm => exact R2Fixed.symm_ax F s
      | trans => exact R2Fixed.trans_ax F s
      | funcExt f => cases f
      | relExt r =>
          cases r with
          | eq => exact R2Fixed.relExt_eq_ax F s
          | mem => exact R2Fixed.relExt_mem_ax F s
    · obtain ⟨σ, hσ, rfl⟩ := ConstructibleInterpretation.mem_ch_ofList [containerAx, irAx] hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
      rcases hσ with rfl | rfl
      · exact R2Fixed.container_ax hF hs
      · exact R2Fixed.irr_ax F s
  · exact R2Ax.gic_axiom ((NTemplate.gic_class_iff p).mp hp) hF hs

/-- **R2**: an internal refutation in the native theory is a validator proof of falsity. -/
theorem cProv_falsum_of_native (h : Provable nativeTheory (^⊥ : V)) : CProv (1 : V) :=
  cProv_falsum_of_provable axOK_native h

/-- **R3 then R2**: an internal `𝗭𝗙`-refutation is a validator proof of falsity. -/
theorem cProv_falsum_of_ZF (h : Provable (𝗭𝗙 : SetTheory) (^⊥ : V)) : CProv (1 : V) :=
  cProv_falsum_of_native (NativeSchema.provable_falsum_native_of_ZF h)

/-- If the validator accepts no proof of falsity, `𝗭𝗙` is consistent. -/
theorem consistent_ZF_of_validator (h : ¬∃ code : V, ArithmeticHistory254.value code = 2) :
    (𝗭𝗙 : SetTheory).Consistent V := by
  have e : (⌜(⊥ : Sentence ℒₛₑₜ)⌝ : V) = ^⊥ := by
    simp [LO.FirstOrder.Sentence.quote_def, LO.FirstOrder.Semiformula.quote_def]
  intro hZF
  rw [e] at hZF
  obtain ⟨code, hc⟩ := cProv_falsum_of_ZF hZF
  exact h ⟨code, by simpa [one_add_one_eq_two] using hc⟩

end Internal

/-- The literal validator accepts no proof of falsity (the same sentence as
Codex's `ValidatorConsistencyForward254.validatorConsistencySentence`). -/
def validatorConsistent : ArithmeticSentence := ∼“∃ code, !ArithmeticHistory254.valueDef 2 code”

lemma validatorConsistent_eval {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    validatorConsistent.Evalb (M := V) ![] ↔ ¬∃ code : V, ArithmeticHistory254.value code = 2 := by
  simp [validatorConsistent, eq_comm]

/-- **`𝗜𝚺₂ ⊢ validator consistency → Con(𝗭𝗙)`.** -/
theorem iSigma2_proves_validator_imp_con_ZF :
    𝗜𝚺 2 ⊢ validatorConsistent 🡒 ((𝗭𝗙 : SetTheory).consistent : ArithmeticSentence) := by
  apply LO.FirstOrder.Arithmetic.complete.{0} (𝗜𝚺 2) _
  intro M _ hM
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 2 := hM
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := mod_ISigma_of_le (show 1 ≤ 2 by norm_num)
  simp only [Semantics.Imp.models_imply]
  intro h
  have h' : ¬∃ code : M, ArithmeticHistory254.value code = 2 := by
    simpa [models_iff, validatorConsistent_eval] using h
  simpa [models_iff] using consistent_ZF_of_validator h'

/-- **`𝗣𝗔 ⊢ validator consistency → Con(𝗭𝗙)`.** -/
theorem peano_proves_validator_imp_con_ZF :
    𝗣𝗔 ⊢ validatorConsistent 🡒 ((𝗭𝗙 : SetTheory).consistent : ArithmeticSentence) :=
  Entailment.weakening (inferInstance : 𝗜𝚺 2 ⪯ 𝗣𝗔) iSigma2_proves_validator_imp_con_ZF

end LeanProofs.ZFCinPA.R2Native
