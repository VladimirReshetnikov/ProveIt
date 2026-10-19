import ZFCinPA.RotationInterpreterConsistency240
import BusyBeaver.ZFC.ArithmeticBlankControlRotation240

set_option autoImplicit false

/-!
The fixed Rotation240 blank-halting sentence and the fixed register-interpreter
halting sentence agree in every IΣ₁ model. Their physical seed and packed table
are identified explicitly; no new evaluator, table, seed or halting sentence is
introduced. Completeness gives the IΣ₁ sentence equivalence. The existing W7
register-side theorems then give the IΣ₂ and PA ZF/ZFC consistency endpoints.

This source composes the imported proofs and retains their assumptions. Its
source-only preparation does not attest a fresh compiler run of the upstream
W7 closure. Source, machine and calibration attribution of Mira-Cult,
Jeff Ketchersid, Andrew James Wade and ProveIt is retained.
-/
namespace LeanProofs.ZFCinPA.BinaryConsistencyRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open _root_.SetTheory.BusyBeaver.ZFC
open scoped LO.FirstOrder.Arithmetic

/-- Both named interfaces decode the very same packed Rotation240 rows. -/
theorem control_table_eq :
    ControlCatalogueRotation240.table = ControlBisimRotation240.tableR := rfl

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Physical fields are [0,0,0,3,0,0,3,0,0] in both interfaces. -/
theorem seedFile_eq_enc : ArithmeticStartupFrameRotation240.seedFile (V := V) =
    ArithmeticL2.enc (⟨3,0,0,0,3,0,0,0,0⟩ : ArithmeticL2.AS V) :=
  ArithmeticStartupFrameRotation240.seedFile_pairs.trans
    (RotationInterpreterConsistency240.enc_seed (V := V)).symm

/-- The two literal sentences agree at arbitrary internal time witnesses. -/
theorem blankSentence_iff_rotationHaltsSentence_eval :
    ArithmeticMachineRunRotation240.haltingSentence.val.Evalb (M := V) ![] ↔
      RotationInterpreterConsistency240.rotationHaltsSentence.Evalb (M := V) ![] := by
  apply (ArithmeticBlankControlRotation240.blankSentence_iff_control_halts (V := V)).trans
  simpa only [control_table_eq, seedFile_eq_enc] using
    (RotationInterpreterConsistency240.rotationHaltsSentence_eval (V := V)).symm

end Model

/-- IΣ₁ proves the equivalence of the existing parameter-free halting sentences. -/
theorem isigma1_proves_blank_iff_rotation_halts :
    𝗜𝚺₁ ⊢ ArithmeticMachineRunRotation240.haltingSentence.val 🡘
      RotationInterpreterConsistency240.rotationHaltsSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  have h := (models_iff (M := M)
    (σ := ArithmeticMachineRunRotation240.haltingSentence.val)).trans
    ((blankSentence_iff_rotationHaltsSentence_eval (V := M)).trans
      (models_iff (M := M)
        (σ := RotationInterpreterConsistency240.rotationHaltsSentence)).symm)
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply]
  exact ⟨h.mp,h.mpr⟩

private theorem transfer {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {C : ArithmeticSentence}
    (hr : M↓[ℒₒᵣ] ⊧ (C 🡘 ∼RotationInterpreterConsistency240.rotationHaltsSentence)) :
    M↓[ℒₒᵣ] ⊧ (C 🡘 ∼ArithmeticMachineRunRotation240.haltingSentence.val) := by
  have hb := (models_iff (M := M)
    (σ := ArithmeticMachineRunRotation240.haltingSentence.val)).trans
    ((blankSentence_iff_rotationHaltsSentence_eval (V := M)).trans
      (models_iff (M := M)
        (σ := RotationInterpreterConsistency240.rotationHaltsSentence)).symm)
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply,
    Semantics.Not.models_not] at hr ⊢
  constructor
  · intro hc hh
    exact hr.1 hc (hb.mp hh)
  · intro hn
    exact hr.2 (fun hh => hn (hb.mpr hh))

/-- IΣ₂ proves that ZF is consistent exactly when the exact binary blank run never halts. -/
theorem iSigma2_proves_con_ZF_iff_not_binary_halts :
    𝗜𝚺 2 ⊢ ((𝗭𝗙 : SetTheory).consistent : ArithmeticSentence) 🡘
      ∼ArithmeticMachineRunRotation240.haltingSentence.val := by
  apply LO.FirstOrder.Arithmetic.complete.{0} (𝗜𝚺 2) _
  intro M _ hM
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 2 := hM
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := mod_ISigma_of_le (show 1 ≤ 2 by norm_num)
  exact transfer (models_of_provable hM
    RotationInterpreterConsistency240.iSigma2_proves_con_ZF_iff_not_rotation_halts)

/-- IΣ₂ proves the corresponding ZFC endpoint for the same literal blank sentence. -/
theorem iSigma2_proves_con_ZFC_iff_not_binary_halts :
    𝗜𝚺 2 ⊢ ((𝗭𝗙𝗖 : SetTheory).consistent : ArithmeticSentence) 🡘
      ∼ArithmeticMachineRunRotation240.haltingSentence.val := by
  apply LO.FirstOrder.Arithmetic.complete.{0} (𝗜𝚺 2) _
  intro M _ hM
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 2 := hM
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := mod_ISigma_of_le (show 1 ≤ 2 by norm_num)
  exact transfer (models_of_provable hM
    RotationInterpreterConsistency240.iSigma2_proves_con_ZFC_iff_not_rotation_halts)

theorem peano_proves_con_ZF_iff_not_binary_halts :
    𝗣𝗔 ⊢ ((𝗭𝗙 : SetTheory).consistent : ArithmeticSentence) 🡘
      ∼ArithmeticMachineRunRotation240.haltingSentence.val :=
  Entailment.weakening (inferInstance : 𝗜𝚺 2 ⪯ 𝗣𝗔)
    iSigma2_proves_con_ZF_iff_not_binary_halts

theorem peano_proves_con_ZFC_iff_not_binary_halts :
    𝗣𝗔 ⊢ ((𝗭𝗙𝗖 : SetTheory).consistent : ArithmeticSentence) 🡘
      ∼ArithmeticMachineRunRotation240.haltingSentence.val :=
  Entailment.weakening (inferInstance : 𝗜𝚺 2 ⪯ 𝗣𝗔)
    iSigma2_proves_con_ZFC_iff_not_binary_halts

end LeanProofs.ZFCinPA.BinaryConsistencyRotation240
