import ZFCinPA.LocalStepDerivation

/-!
# Audit for the first field's source-derivation interface and boundary

Three things must stay visible here.

* **The design answer, machine-checked.**  `bot_notSigma_step` is the
  positive half: at an *arbitrary* previous-level relation `L` — which is
  the exact generality an abstract interpretation of the two placeholders
  provides — the falsity conjunct transfers one level up, by
  `levelJustified_of_tag_low` alone.  `exclusivity_not_step_transferable`
  is the negative half: there is a previous level whose Sigma side is
  empty, so that both conjuncts of `srcLocalStep` (and the source form of
  the `crossLevel` field) hold, and for which the next level's exclusivity
  nevertheless fails at the form code `⊥ 🡒 ⊥`.  Together they say that
  the first conjunct of the local-step successor is derivable from the
  previous certificate and the second is *not*.

* **The corrected interface.**  `localStepSuccessor_of_congruentSource`
  and `localStepSuccessor_of_congruentDerivation` accept the source
  derivation with the placeholder congruence laws as an antecedent, which
  is what `complete_underSetPlaceholderCongruence` actually produces.  The
  antecedent is discharged after translation by `translated_srcCongruence`
  — the set-theoretic counterpart of goal 1's
  `translatedTwoPredicateCongruenceContextProof`.  Its hypothesis is
  strictly weaker than `LocalStepSuccessor.localStepSuccessor_of_derivation`'s
  and its conclusion identical, so this is a strengthening of the residual
  obligation's interface, never a weakening of
  `ZFCSuccessorImplications`.

* **The honest boundary.**  Neither reduction is a claim that its source
  derivation exists.  Both take it as an explicit argument, and the module
  header records why — relative to `Con(𝗭𝗙𝗖)` — no such argument can be
  supplied for the present statement of `srcLocalStepStep`.

The `#print axioms` lines must show only Lean's three standard classical
axioms.
-/

namespace LeanProofs.ZFCinPA.LocalStepDerivationAudit

open LeanProofs.ZFCinPA.LocalStepDerivation

/-! ## The design answer -/

#check @bot_notSigma_step
#check @exclusivity_not_step_transferable

/-! ## The congruence antecedent and its discharge -/

#check @srcCongruence
#check @srcCongruentLocalStepStep
#check @congruenceProof_levelLeaves
#check @translated_srcCongruence

/-! ## The corrected reduction, with its explicit hypotheses -/

#check @localStepSuccessor_of_congruentSource
#check @localStepSuccessor_of_congruentDerivation

/-! ## Assumption audit -/

#print axioms bot_notSigma_step
#print axioms exclusivity_not_step_transferable
#print axioms congruenceProof_levelLeaves
#print axioms translated_srcCongruence
#print axioms localStepSuccessor_of_congruentSource
#print axioms localStepSuccessor_of_congruentDerivation

end LeanProofs.ZFCinPA.LocalStepDerivationAudit
