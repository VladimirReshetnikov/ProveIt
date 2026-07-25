import ZFCinPA.NumeralOmega

/-!
# Audit for the uniform internal ω-membership of the numeral chain

Three things must stay visible.

* **The statement is uniform.**  `zfcInternal_numChain_omega` takes an
  *arbitrary* element `x : V` of the ambient model of `𝗜𝚺₁` — nonstandard
  indices included — and produces an internal `𝗭𝗙𝗖` proof.  Its proof runs
  `provable_numChainOmegaCode`, a model-internal `𝚺₁` successor induction,
  not an external recursion over `Nat`.
* **The vocabulary matches the kernel.**  The consequent is
  `SeparationKernel.isVonNeumannNatQ`, the very ω-predicate
  `SeparationKernel.zfcOmegaInductionOfShiftFixed` concludes with, and the
  antecedent is the typed view of `UniformStatement.numChainCode`, the code
  the source templates' numeral placeholder becomes after translation.  So
  this discharges item 2 of `ZFCinPA.LocalStepTransfer`'s residue in the
  form the rank lemmas need.
* **Nothing is assumed.**  The two source derivations are ordinary finite
  proofs over `SeparationKernel.omegaSourceTheory`, compiled by the typed
  template proof compiler; the `#print axioms` lines must show only Lean's
  three standard classical axioms.
-/

set_option autoImplicit false

namespace LeanProofs.ZFCinPA.NumeralOmegaAudit

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA
open LeanProofs.ZFCinPA.NumeralOmega

/-! ## The two standard leaves and their codes -/

#check @numZeroS
#check @succRelS
#check @emb_numZeroS
#check @emb_succRelS
#check @quote_numZeroS_val
#check @quote_succRelS_val

/-! ## The numeral chain, typed -/

#check @numChainQ
#check @numChainQ_shift
#check @numChainQ_zero
#check @numChainQ_succ

/-! ## The source sentences and their specializations -/

#check @srcNumChainZero
#check @srcNumChainStep
#check @translate_srcNumChainZero
#check @translate_srcNumChainStep
#check @srcNumChainZeroProof
#check @srcNumChainStepProof

/-! ## The internal statement, its halves, and the induction -/

#check @numChainOmegaStmt
#check @numChainOmegaBase
#check @numChainOmegaStep
#check @provable_numChainOmegaCode
#check @zfcInternal_numChain_omega
#check @zfcInternal_numChain_omega_provable

/-! ## The kernel's ω-predicate, for comparison -/

#check @SeparationKernel.isVonNeumannNatQ
#check @SeparationKernel.zfcOmegaInductionOfShiftFixed

/-! ## Assumption audit -/

#print axioms emb_numZeroS
#print axioms emb_succRelS
#print axioms quote_numZeroS_val
#print axioms quote_succRelS_val
#print axioms numChainQ_zero
#print axioms numChainQ_succ
#print axioms translate_srcNumChainZero
#print axioms translate_srcNumChainStep
#print axioms srcNumChainZeroProof
#print axioms srcNumChainStepProof
#print axioms numChainOmegaBase
#print axioms numChainOmegaStep
#print axioms provable_numChainOmegaCode
#print axioms zfcInternal_numChain_omega
#print axioms zfcInternal_numChain_omega_provable

end LeanProofs.ZFCinPA.NumeralOmegaAudit
