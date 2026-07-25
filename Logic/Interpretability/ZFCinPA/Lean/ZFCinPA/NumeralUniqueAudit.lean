import ZFCinPA.NumeralUnique

/-!
# Audit for the pinned numeral placeholder

Four things must stay visible.

* **The source formula says what it claims.**  `eval_srcNumUnique` reads
  `srcNumUnique`, in an *arbitrary* template structure with genuine
  equality, as `∀ k k', Num k → Num k' → k = k'` over
  `TemplateEvaluation.templateNum` — the very relation
  `TemplateEvaluation.templateStepLevel` existentially quantifies.  So the
  antecedent recorded here is exactly the one item 3 of
  `ZFCinPA.FieldEvaluation`'s residue asks for, not a weaker cousin.
* **The discharge is uniform and internal.**
  `zfcInternal_numChain_unique` takes an *arbitrary* `x : V` — nonstandard
  indices included — and produces an internal `𝗭𝗙𝗖` proof.  Its proof runs
  `provable_numChainUniqueCode`, an ambient `𝚺₁` successor induction, not
  an external recursion over `Nat`.
* **The vocabularies match.**  `numChainUniqueStmt x` is *definitionally*
  `translateFormula (levelLeaves x) srcNumUnique`, so the internal proof
  is literally a proof of the translated source antecedent and slots into
  a compiled source implication by `TProof.modusPonens`.  Nothing is
  restated "up to equivalence".
* **Nothing is assumed.**  The two source derivations are ordinary finite
  proofs over `templateZFC 2 levelArities` produced by completeness, and
  the congruence antecedent they carry is discharged by the already
  landed `LocalStepDerivation.translated_srcCongruence`.  The
  `#print axioms` lines must show only Lean's three standard classical
  axioms.
-/

set_option autoImplicit false

namespace LeanProofs.ZFCinPA.NumeralUniqueAudit

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA
open LeanProofs.ZFCinPA.NumeralUnique

/-! ## The source formulas -/

#check @srcNum₁
#check @srcNum₂
#check @srcEqSlots
#check @srcNumUnique
#check @srcNumUniqueSucc
#check @srcNumUniqueZero
#check @srcNumUniqueStep

/-! ## Free-variable-freeness and the closed forms -/

#check @fvFree_srcNumUnique
#check @fvFree_srcNumUniqueSucc
#check @fvFree_srcNumUniqueZero
#check @fvFree_srcNumUniqueStep
#check @srcNumUniqueSentence
#check @srcNumUniqueZeroSentence
#check @srcNumUniqueStepSentence
#check @emb_srcNumUniqueSentence
#check @emb_srcNumUniqueZeroSentence
#check @emb_srcNumUniqueStepSentence

/-! ## The translation identities -/

#check @numChainUniqueCode
#check @quote_numZeroLeaf
#check @translate_srcNum₁
#check @translate_srcNum₂
#check @translate_srcEqSlots
#check @translate_srcNumUnique_val
#check @translate_srcNumUniqueSucc_val
#check @translate_srcNumUniqueZero_val

/-! ## The evaluation bridge -/

#check @eval_srcNum₁
#check @eval_srcNum₂
#check @eval_srcEqSlots
#check @eval_srcNumUnique
#check @eval_srcNumUniqueSucc
#check @eval_srcNumUniqueZero

/-! ## The two source derivations -/

#check @srcNumUniqueZeroProof
#check @srcNumUniqueStepProof

/-! ## The internal discharge -/

#check @numChainUniqueStmt
#check @numChainUniqueStmt_val
#check @compileCongruent
#check @numChainUniqueBase
#check @numChainUniqueStep
#check @provable_numChainUniqueCode
#check @zfcInternal_numChain_unique
#check @zfcInternal_numChain_unique_provable
#check @zfcInternal_srcNumUnique

/-! ## The existentially quantified reading this pins, for comparison -/

#check @TemplateEvaluation.templateStepLevel
#check @TemplateEvaluation.templateNum

/-! ## Assumption audit -/

#print axioms srcNum₁
#print axioms srcNum₂
#print axioms srcEqSlots
#print axioms srcNumUnique
#print axioms srcNumUniqueSucc
#print axioms srcNumUniqueZero
#print axioms srcNumUniqueStep
#print axioms fvFree_srcNum₁
#print axioms fvFree_srcNum₂
#print axioms fvFree_srcEqSlots
#print axioms fvFree_srcNumUnique
#print axioms fvFree_srcNumUniqueSucc
#print axioms fvFree_srcNumUniqueZero
#print axioms fvFree_srcNumUniqueStep
#print axioms srcNumUniqueSentence
#print axioms srcNumUniqueZeroSentence
#print axioms srcNumUniqueStepSentence
#print axioms emb_srcNumUniqueSentence
#print axioms emb_srcNumUniqueZeroSentence
#print axioms emb_srcNumUniqueStepSentence
#print axioms numChainUniqueCode
#print axioms quote_numZeroLeaf
#print axioms translate_srcNum₁
#print axioms translate_srcNum₂
#print axioms translate_srcEqSlots
#print axioms translate_srcNumUnique_val
#print axioms translate_srcNumUniqueSucc_val
#print axioms translate_srcNumUniqueZero_val
#print axioms eval_srcNum₁
#print axioms eval_srcNum₂
#print axioms eval_srcEqSlots
#print axioms eval_srcNumUnique
#print axioms eval_srcNumUniqueSucc
#print axioms eval_srcNumUniqueZero
#print axioms srcNumUniqueZeroProof
#print axioms srcNumUniqueStepProof
#print axioms numChainUniqueStmt
#print axioms numChainUniqueStmt_val
#print axioms compileCongruent
#print axioms numChainUniqueBase
#print axioms numChainUniqueStep
#print axioms provable_numChainUniqueCode
#print axioms zfcInternal_numChain_unique
#print axioms zfcInternal_numChain_unique_provable
#print axioms zfcInternal_srcNumUnique

end LeanProofs.ZFCinPA.NumeralUniqueAudit
