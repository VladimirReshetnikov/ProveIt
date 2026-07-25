import ZFCinPA.EnlargedFields

/-!
# Audit for the enlarged certificate field set

Three things must stay visible here.

* **The two refuting expansions die on the enlargement, not on the old
  fields.**  `expansionA_fails_tarskiIntro` and
  `expansionB_fails_tarskiElim` each name one *new* field.  That the old
  antecedent does not already exclude expansion (B) — the one that refutes
  the five-field successor obligation in
  `ZFCinPA.LocalStepDerivation.exclusivity_not_step_transferable` — is
  recorded by `expansionB_satisfies_excl` and
  `expansionB_satisfies_decided`.

* **The enlargement is step-transferable.**  `stepGood_of_levelLaws` is the
  positive counterpart of `exclusivity_not_step_transferable`: the same
  closure level, the same abstract vocabulary, with the two new fields in
  the antecedent, and now exclusivity *and* the adjacent-level collapse
  both come out.  `exclusivity_step` is the headline instance —
  exactly the statement shown false for five fields.

* **The two honest costs.**  `CodeInduction` is an explicit hypothesis, not
  a theorem: the induction property mentions the previous level, so in the
  source template the corresponding Separation instance is one for a
  placeholder formula.  `codeInduction_of_definable` records that every
  `Form`-presented property has it, which is how the instance will be
  discharged after translation, by `ZFCinPA.SeparationKernel`.  And the
  bounds are numerals of external naturals, because the two goal-2
  successor-peeling lemmas exist only in that shape.

Nothing here is a claim that the enlarged fields are provable in `𝗭𝗙𝗖` at
every level (that is `ZFCinPA.BaseCertificate`'s job) or that the coded
fields exist (that is `ZFCinPA.CertificateFields`'s).  The `#print axioms`
lines must show only Lean's three standard classical axioms.
-/

namespace LeanProofs.ZFCinPA.EnlargedFieldsAudit

open LeanProofs.ZFCinPA.EnlargedFields

/-! ## The two new fields -/

#check @TarskiElim
#check @TarskiIntro
#check @LevelLaws

/-! ## The two refuting expansions -/

#check @expansionA_fails_tarskiIntro
#check @expansionB_fails_tarskiElim
#check @expansionB_satisfies_excl
#check @expansionB_satisfies_decided

/-! ## The successor level and the field transfers -/

#check @Step
#check @step_of_level
#check @impSigmaElim_step
#check @impPiElim_step
#check @impSigmaIntro_step

/-! ## The induction hypothesis, carried explicitly -/

#check @CodeInduction
#check @codeInduction_of_definable

/-! ## The transfer -/

#check @StepGood
#check @stepGood_of_levelLaws
#check @exclusivity_step
#check @piFalse_collapse_step
#check @sigmaTrue_collapse_step

/-! ## Soundness of the enlargement

A field set that defeats the countermodels but is not itself true would be
worthless.  `levelLaws_levelSat` closes that gap unconditionally: goal 2's
hierarchy satisfies the whole enlarged bundle at every level, with the
level/bound pairing the certificate family uses.  `step_levelSat` records
that the abstract successor level of this module *is* `LevelSat` at the next
index, so the transfer above is about the real hierarchy and not an
approximation of it. -/

#check @step_levelSat
#check @sigmaTrue_all_elim_strong
#check @piFalse_ex_elim_strong
#check @tarskiElim_levelSat
#check @tarskiIntro_levelSat
#check @levelLaws_levelSat

/-! ## Assumption audit -/

#print axioms expansionA_fails_tarskiIntro
#print axioms expansionB_fails_tarskiElim
#print axioms expansionB_satisfies_excl
#print axioms expansionB_satisfies_decided
#print axioms step_of_level
#print axioms impSigmaElim_step
#print axioms impPiElim_step
#print axioms impSigmaIntro_step
#print axioms codeInduction_of_definable
#print axioms stepGood_of_levelLaws
#print axioms exclusivity_step
#print axioms piFalse_collapse_step
#print axioms sigmaTrue_collapse_step
#print axioms step_levelSat
#print axioms sigmaTrue_all_elim_strong
#print axioms piFalse_ex_elim_strong
#print axioms tarskiElim_levelSat
#print axioms tarskiIntro_levelSat
#print axioms levelLaws_levelSat

end LeanProofs.ZFCinPA.EnlargedFieldsAudit
