import ZFCinPA.SeparationKernel

/-!
# Kernel audit for the model-coded Separation and ω-induction kernel

This deliberately small module checks the public interface of
`ZFCinPA.SeparationKernel` and prints the axioms of its substantive
theorems.  Keeping the audit separate prevents diagnostic output from
becoming part of the library-facing module.
-/

set_option autoImplicit false

namespace LeanProofs.ZFCinPA.SeparationKernelAudit

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA
open LeanProofs.ZFCinPA.SeparationKernel

/-! ## The internalized Separation axiom -/

#check @zfc_delta1ch_eq
#check @mem_zfc_delta1Class_of_sepR
#check @sepBody_shift_fixed
#check @sepBody_mem_zfc_delta1Class_of_shift_fixed
#check @zfcSeparationProofOfShiftFixed

/-! ## The one-placeholder source language and its compiler translation -/

#check (inferInstance : (setTemplateLanguage).DecidableEq)
#check @setHom
#check @translateTerm
#check @translateFormula
#check @setTemplateTranslation
#check @translateFormula_lMap_set
#check @translateFormula_lMap_set_emb

/-! ## The ω-induction source formulas and their specializations -/

#check @srcMem
#check @srcP
#check @liftSet
#check @srcSeparation
#check @isInductive
#check @isVonNeumannNat
#check @inductiveSetExists
#check @srcOmegaZero
#check @srcOmegaSucc
#check @srcOmegaConcl
#check @srcOmegaInduction

#check @isEmptyQ
#check @isSuccQ
#check @isVonNeumannNatQ

#check @translate_srcSeparation
#check @translate_srcOmegaZero
#check @translate_srcOmegaSucc
#check @translate_srcOmegaConcl
#check @translate_srcOmegaInduction

/-! ## The source theory, its fixed derivation, and the kernel -/

#check @omegaSourceTheory
#check @omegaTheoryTranslation
#check @compileOmegaTemplate
#check @zfc_proves_inductiveSetExists
#check @liftedInductiveSetExistsProof
#check @omegaSourceProof
#check @zfcOmegaInductionOfShiftFixed

/-! ## Smoke test: the kernel elaborates over `ℕ` -/

#check fun (K : Bootstrapping.Semiformula ℕ ℒₛₑₜ 1)
    (hK : Bootstrapping.shift ℒₛₑₜ K.val = K.val)
    (hzero : (𝗭𝗙𝗖 : SetTheory).internalize ℕ ⊢! ∀⁰ (isEmptyQ 🡒 K))
    (hsucc : (𝗭𝗙𝗖 : SetTheory).internalize ℕ ⊢!
      ∀⁰ ∀⁰ (K.subst ![.bvar 1] 🡒 (isSuccQ 🡒 K.subst ![.bvar 0]))) =>
  zfcOmegaInductionOfShiftFixed K hK hzero hsucc

/-! ## Assumption audit

Everything is built on Foundation's classical development, so
`Classical.choice` is expected throughout; nothing beyond Lean's three
standard axioms should appear — in particular no `sorry` and no
theory-specific axiom. -/

#print axioms sepBody_shift_fixed
#print axioms sepBody_mem_zfc_delta1Class_of_shift_fixed
#print axioms zfcSeparationProofOfShiftFixed
#print axioms translate_srcSeparation
#print axioms translate_srcOmegaInduction
#print axioms zfc_proves_inductiveSetExists
#print axioms omegaSourceProof
#print axioms zfcOmegaInductionOfShiftFixed

end LeanProofs.ZFCinPA.SeparationKernelAudit
