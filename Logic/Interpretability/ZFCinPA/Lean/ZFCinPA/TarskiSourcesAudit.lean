import ZFCinPA.TarskiSources

/-!
# Audit for the source readings of the two Tarski certificate fields

The audit keeps four things visible.

* **The slot- and arity-generalized level tower.**  `srcLevelSatAt`,
  `srcBitWitnessAt`, `srcCanonAtPair` and `srcPolarAt` (with their
  successor twins) are the shared generalization the previous analysis
  flagged as missing: the five original fields could only read the level
  tower at the canonical slot pair `(1, 0)` and ambient arity `4`, and the
  Tarski rows need six further pairs at two further arities.  Each carries
  its reconciliation lemma at an arbitrary model index.
* **The three coded skeletons.**  `srcConnSpine`, `srcQuantSpine` and
  `srcBotPiOf` are the source counterparts of
  `CertificateFields.connSpinePart`, `quantSpinePart` and `botPiPart`;
  their reconciliation lemmas are equations between specializations and the
  raw builders, holding for an arbitrary body.
* **The two fields, at both levels.**  `translate_srcTarskiElim` and
  `translate_srcTarskiIntro` say that at *every* model index, standard or
  not, the fixed source propositions specialize to `tarskiElimCode x` and
  `tarskiIntroCode x`; the `Succ` variants do the same one index up, and
  are the consequent halves a successor implication for these two fields
  needs.  Both levels come from the *same* definitions and the *same*
  translation proof, instantiated at `srcPolarAt` and `srcPolarAtSucc`.
* **No new kernel evaluation.**  Every free-slot bound is either an
  exported `freeMax` evaluation of `ZFCinPA.CertificateFields`
  (`freeMax_fTagPairF_imp`/`_and`/`_or`, `freeMax_fTagUnF_all`/`_ex`), the
  exported `LevelCodeTower.fm02`, or a consequence of one of the three
  skeleton closedness theorems.  Nothing here `decide`s a `freeMax`, and
  nothing evaluates a Gödel code: concrete constants are reached only
  through `coe_toNat_eq_quote`, `quote_leaf_move` and `quote_fEq_move`.

The `#print axioms` lines must show only Lean's three standard classical
axioms.
-/

namespace LeanProofs.ZFCinPA.TarskiSourcesAudit

open LeanProofs.ZFCinPA
open LeanProofs.ZFCinPA.SuccessorSources

/-! ## Free-slot bounds recovered from the skeleton closedness theorems -/

#check @free_isFormCode3D4
#check @free_isFormCode2D4
#check @free_univEnv1D4
#check @free_tagPairD4
#check @free_isFormCode4D5
#check @free_univEnv3D5
#check @free_tagUnD5
#check @free_econsQuantD5
#check @free_taggedEmpty0D2

/-! ## The generalized level tower -/

#check @srcLevelSatAt
#check @srcLevelSatSuccAt
#check @srcBitWitnessAt
#check @srcBitWitnessSuccAt
#check @srcCanonAtPair
#check @srcPolarAt
#check @srcPolarAtSucc
#check @translate_srcLevelSatAt
#check @translate_srcLevelSatSuccAt
#check @translate_srcBitWitnessAt
#check @translate_srcBitWitnessSuccAt
#check @translate_srcCanonAtPair
#check @translate_srcPolarAt
#check @translate_srcPolarAtSucc

/-! ## The three coded skeletons -/

#check @srcConnSpine
#check @srcQuantSpine
#check @srcBotPiOf
#check @translate_srcConnSpine
#check @translate_srcQuantSpine
#check @translate_srcBotPiOf

/-! ## The rows -/

#check @translate_srcConnElimOr
#check @translate_srcConnElimAnd
#check @translate_srcConnIntroOr
#check @translate_srcConnIntroAnd
#check @translate_srcQuantElim
#check @translate_srcQuantIntro

/-! ## The two fields at both levels -/

#check @srcTarskiElimOf
#check @srcTarskiIntroOf
#check @srcTarskiElim
#check @srcTarskiElimSucc
#check @srcTarskiIntro
#check @srcTarskiIntroSucc
#check @translate_srcTarskiElim
#check @translate_srcTarskiElimSucc
#check @translate_srcTarskiIntro
#check @translate_srcTarskiIntroSucc
#check @translate_srcTarskiElim_formula
#check @translate_srcTarskiElimSucc_formula
#check @translate_srcTarskiIntro_formula
#check @translate_srcTarskiIntroSucc_formula

/-! ## Free-variable-freeness -/

#check @fvFree_srcTarskiElim
#check @fvFree_srcTarskiElimSucc
#check @fvFree_srcTarskiIntro
#check @fvFree_srcTarskiIntroSucc

/-! ## Assumption audit -/

#print axioms translate_srcLevelSatAt
#print axioms translate_srcLevelSatSuccAt
#print axioms translate_srcBitWitnessAt
#print axioms translate_srcBitWitnessSuccAt
#print axioms translate_srcCanonAtPair
#print axioms translate_srcPolarAt
#print axioms translate_srcPolarAtSucc
#print axioms translate_srcConnSpine
#print axioms translate_srcQuantSpine
#print axioms translate_srcBotPiOf
#print axioms translate_srcTarskiElim
#print axioms translate_srcTarskiElimSucc
#print axioms translate_srcTarskiIntro
#print axioms translate_srcTarskiIntroSucc
#print axioms fvFree_srcTarskiElim
#print axioms fvFree_srcTarskiElimSucc
#print axioms fvFree_srcTarskiIntro
#print axioms fvFree_srcTarskiIntroSucc

end LeanProofs.ZFCinPA.TarskiSourcesAudit
