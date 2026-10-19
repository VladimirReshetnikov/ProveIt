import ZFCinPA.BinaryConsistencyRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open _root_.SetTheory.BusyBeaver.ZFC
open LeanProofs.ZFCinPA.BinaryConsistencyRotation240
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.BinaryConsistencyRotation240.control_table_eq
#print axioms LeanProofs.ZFCinPA.BinaryConsistencyRotation240.seedFile_eq_enc
#print axioms LeanProofs.ZFCinPA.BinaryConsistencyRotation240.blankSentence_iff_rotationHaltsSentence_eval
#print axioms LeanProofs.ZFCinPA.BinaryConsistencyRotation240.isigma1_proves_blank_iff_rotation_halts
#print axioms LeanProofs.ZFCinPA.BinaryConsistencyRotation240.iSigma2_proves_con_ZF_iff_not_binary_halts
#print axioms LeanProofs.ZFCinPA.BinaryConsistencyRotation240.iSigma2_proves_con_ZFC_iff_not_binary_halts
#print axioms LeanProofs.ZFCinPA.BinaryConsistencyRotation240.peano_proves_con_ZF_iff_not_binary_halts
#print axioms LeanProofs.ZFCinPA.BinaryConsistencyRotation240.peano_proves_con_ZFC_iff_not_binary_halts

example : ControlCatalogueRotation240.table = ControlBisimRotation240.tableR := control_table_eq

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example : ArithmeticStartupFrameRotation240.seedFile (V := V) =
    ArithmeticL2.enc (⟨3,0,0,0,3,0,0,0,0⟩ : ArithmeticL2.AS V) := seedFile_eq_enc
example : ArithmeticMachineRunRotation240.haltingSentence.val.Evalb (M := V) ![] ↔
    LeanProofs.ZFCinPA.RotationInterpreterConsistency240.rotationHaltsSentence.Evalb (M := V) ![] :=
  blankSentence_iff_rotationHaltsSentence_eval
example : 𝗜𝚺₁ ⊢ ArithmeticMachineRunRotation240.haltingSentence.val 🡘
    LeanProofs.ZFCinPA.RotationInterpreterConsistency240.rotationHaltsSentence :=
  isigma1_proves_blank_iff_rotation_halts
example : 𝗜𝚺 2 ⊢ ((𝗭𝗙 : SetTheory).consistent : ArithmeticSentence) 🡘
    ∼ArithmeticMachineRunRotation240.haltingSentence.val :=
  iSigma2_proves_con_ZF_iff_not_binary_halts
example : 𝗜𝚺 2 ⊢ ((𝗭𝗙𝗖 : SetTheory).consistent : ArithmeticSentence) 🡘
    ∼ArithmeticMachineRunRotation240.haltingSentence.val :=
  iSigma2_proves_con_ZFC_iff_not_binary_halts
example : 𝗣𝗔 ⊢ ((𝗭𝗙 : SetTheory).consistent : ArithmeticSentence) 🡘
    ∼ArithmeticMachineRunRotation240.haltingSentence.val := peano_proves_con_ZF_iff_not_binary_halts
example : 𝗣𝗔 ⊢ ((𝗭𝗙𝗖 : SetTheory).consistent : ArithmeticSentence) 🡘
    ∼ArithmeticMachineRunRotation240.haltingSentence.val := peano_proves_con_ZFC_iff_not_binary_halts

-- Both semantic directions retain internal time witnesses through the existing sentences.
example (h : ArithmeticMachineRunRotation240.haltingSentence.val.Evalb (M := V) ![]) :
    LeanProofs.ZFCinPA.RotationInterpreterConsistency240.rotationHaltsSentence.Evalb (M := V) ![] :=
  blankSentence_iff_rotationHaltsSentence_eval.mp h
example (h : LeanProofs.ZFCinPA.RotationInterpreterConsistency240.rotationHaltsSentence.Evalb
    (M := V) ![]) : ArithmeticMachineRunRotation240.haltingSentence.val.Evalb (M := V) ![] :=
  blankSentence_iff_rotationHaltsSentence_eval.mpr h
