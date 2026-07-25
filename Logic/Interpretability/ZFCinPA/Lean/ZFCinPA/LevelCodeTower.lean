import ZFCinPA.UniformStatement

/-!
# PR-blueprint code towers for the level-indexed truth formulas

`BoundedZFCConsistency.UniverseTruthLevel` defines the level-`n` record
predicate `levelSatF : Nat → (Nat → Nat → Nat → Form)` by *external*
recursion on `n`: the successor formula wraps the predecessor in the fixed
step-closure pattern `fLevelClosedF (levelSatF n) 0 1`.  The staged
`𝗭𝗙𝗖`-certificate compiler needs the Gödel codes of the `toSet`-translations
of this family at *every* element of a PA model, nonstandard levels
included.  This module builds that internal code tower with Foundation's
`PR.Blueprint`/`PR.Construction` machinery, in the pattern of
`ZFCinPA.UniformStatement`'s `conNumCode`.

## The recursion shape and the canonical slot assignment

Unfolding one level of `levelSatF (n+1) c e b` gives

* two existentials over `fNumF 0 n` (the numeral of the previous level,
  handled by `UniformStatement.numChainCode`),
* the slot-independent **closure kernel** `closF n = fLevelClosedF
  (levelSatF n) 0 1`, and
* one slot-dependent membership atom `fTripleMemF (c+2) (e+2) (b+2) 1`.

All of the `n`-recursion is concentrated in the closure kernel: inside
`fLevelJustifiedF` the predecessor family occurs at exactly the three fixed
slot triples `(4,3,2)` (the delegation row), `(5,4,2)` (the universal
clause), and `(5,4,1)` (the existential clause), each itself of the
unfolded successor shape.  The internal recursion therefore carries the
*single* value `closF n` and re-wraps it three times per step.

The **canonical slot assignment** of the tower is

* `levelSatCode` codes `levelSatF n 2 1 0` at translation depth `3`
  (slot `2` = code, slot `1` = environment, slot `0` = bit);
* the derived `sigmaTrueCode`/`piFalseCode`/`piTrueCode` code
  `fSigmaTrueF n 1 0`/`fPiFalseF n 1 0`/`fPiTrueF n 1 0` at depth `2`
  (slot `1` = code, slot `0` = environment).

The choice makes the wrappers literal: `fSigmaTrueF n 1 0` is one
existential and one conjunct around exactly the canonical instance
`levelSatF n 2 1 0` at depth `3`.  Any other slot assignment the compiler
needs is a substitution instance of the canonical one.

## Free-variable accounting

Depth moves under quotation (`quote_toSet_congr`) need upper bounds on the
free slots of the moved formulas.  Instead of exact slot tables for the
large concrete macros (`fIsQFCodeF`, `fRanksF`, …), this module introduces
the *tight* free-slot bound `freeMax`, which — unlike `bound` — descends
through binders, so it is exact on the macros' concrete instances and can
be evaluated by the kernel.  The only `n`-dependent fact,
`Free i (closF n) → i < 2`, then follows by an induction that walks the
successor spine with `decide`-evaluated bounds at the fixed leaves.

## Codes are names, never numbers

Foundation's Gödel numbering is Cantor pairing at every constructor, so
the numeric codes of the deep fixed leaves are astronomical; the module
manipulates them strictly symbolically.  See the *parameter firewall* note
in the internal-builder section for the discipline that keeps every
`Defined` proof from ever evaluating one.
-/

set_option autoImplicit false

namespace LeanProofs
namespace ZFCinPA

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open BoundedZFCConsistency (fNumF fTripleMemF fUnivEnvF fTagUnF fPiBoundedF
  fSigmaBoundedF fShiftTripleMemF fLevelImpF fLevelAndF fLevelOrF
  fLevelClosedF fLevelJustifiedF fLevelAllF fLevelExF levelSatF
  fSigmaTrueF fPiFalseF fPiTrueF)

/-! ## Form-level analysis

The closure kernel, the unfolded successor shape, and the identification of
the three fixed predecessor instances.  Everything here is metatheoretic
syntax; no model appears. -/

section FormLevel

open SetTheory (Form Free)

/-- **The closure kernel**: the slot-independent part of the successor of
`levelSatF`.  Its free slots are `0` (the numeral of the previous level)
and `1` (the certificate), both bound by the successor's existentials. -/
def closF (n : ℕ) : SetTheory.Form := fLevelClosedF (levelSatF n) 0 1

/-- The unfolded successor shape of `levelSatF`, parametrized by the
*already shifted* slot triple: two existentials over the previous level's
numeral, the closure kernel, and the slot-carrying membership atom. -/
def lvlInstF (n : ℕ) (c e b : ℕ) : SetTheory.Form :=
  .fEx (.fEx (.fAnd (fNumF 0 n) (.fAnd (closF n) (fTripleMemF c e b 1))))

/-- The successor of the family is the instance shape at shifted slots. -/
theorem levelSatF_succ_eq (n c e b : ℕ) :
    levelSatF (n + 1) c e b = lvlInstF n (c + 2) (e + 2) (b + 2) := rfl

/-- **The successor of the closure kernel, fully unfolded.**  The spine is
fixed; the `n`-dependence is confined to the three `lvlInstF n` instances at
the slot triples `(6,5,4)`, `(7,6,4)`, `(7,6,3)` — the shifted images of
`(4,3,2)`, `(5,4,2)`, `(5,4,1)` — and to the numerals inside them.  Each
remaining leaf is a fixed concrete formula. -/
theorem closF_succ_form (n : ℕ) :
    closF (n + 1) =
      .fAll (.fAll (.fAll (.fImp (fTripleMemF 2 1 0 4)
        (.fAnd (fUnivEnvF 1)
          (.fEx (.fEx (.fAnd (.fAnd (fNumF 1 0) (fNumF 0 1))
            (.fOr (lvlInstF n 6 5 4)
            (.fOr (fLevelImpF 4 3 2 6 1 0)
            (.fOr (fLevelAndF 4 3 2 6 1 0)
            (.fOr (fLevelOrF 4 3 2 6 1 0)
            (.fOr (.fEx (.fAnd (fTagUnF 5 6 0)
                    (.fOr (.fAnd (.fEq 3 1) (.fAnd (fPiBoundedF 6 5)
                            (.fImp (lvlInstF n 7 6 4) .fBot)))
                          (.fAnd (.fEq 3 2)
                            (.fEx (fShiftTripleMemF 1 0 5 8 0))))))
                  (.fEx (.fAnd (fTagUnF 5 7 0)
                    (.fOr (.fAnd (.fEq 3 1)
                            (.fEx (fShiftTripleMemF 1 0 5 8 1)))
                          (.fAnd (.fEq 3 2) (.fAnd (fSigmaBoundedF 6 5)
                            (.fImp (lvlInstF n 7 6 3) .fBot)))))))))))))))))) :=
  rfl

/-- The canonical Sigma-truth wrapper: one existential and one conjunct
around exactly the canonical instance `levelSatF n 2 1 0`. -/
theorem fSigmaTrueF_canonical (n : ℕ) :
    fSigmaTrueF n 1 0 = .fEx (.fAnd (fNumF 0 1) (levelSatF n 2 1 0)) := rfl

/-- The canonical Pi-falsity wrapper. -/
theorem fPiFalseF_canonical (n : ℕ) :
    fPiFalseF n 1 0 = .fEx (.fAnd (fNumF 0 0) (levelSatF n 2 1 0)) := rfl

/-- The canonical Pi-truth wrapper. -/
theorem fPiTrueF_canonical (n : ℕ) :
    fPiTrueF n 1 0 = .fImp (fPiFalseF n 1 0) .fBot := rfl

end FormLevel

/-! ## The tight free-slot bound -/

section FreeMax

open SetTheory (Form Free)

/-- The **tight** strict upper bound on the free slots of a `Form`.  Unlike
`SetTheory.bound`, this descends through binders, so it computes the exact
supremum on concrete formulas and the kernel can evaluate it on the fixed
macros of the truth hierarchy. -/
def freeMax : SetTheory.Form → ℕ
  | .fMem i j => max i j + 1
  | .fEq i j  => max i j + 1
  | .fBot     => 0
  | .fImp a b => max (freeMax a) (freeMax b)
  | .fAnd a b => max (freeMax a) (freeMax b)
  | .fOr a b  => max (freeMax a) (freeMax b)
  | .fAll a   => freeMax a - 1
  | .fEx a    => freeMax a - 1

/-- Every free slot lies below `freeMax`. -/
theorem free_lt_freeMax (f : SetTheory.Form) : ∀ n, Free n f → n < freeMax f := by
  induction f with
  | fMem i j =>
      intro n hn
      rcases hn with rfl | rfl <;> simp [freeMax]
  | fEq i j =>
      intro n hn
      rcases hn with rfl | rfl <;> simp [freeMax]
  | fBot => intro n hn; cases hn
  | fImp a b iha ihb =>
      intro n hn
      rcases hn with hn | hn
      · have := iha n hn; simp only [freeMax]; omega
      · have := ihb n hn; simp only [freeMax]; omega
  | fAnd a b iha ihb =>
      intro n hn
      rcases hn with hn | hn
      · have := iha n hn; simp only [freeMax]; omega
      · have := ihb n hn; simp only [freeMax]; omega
  | fOr a b iha ihb =>
      intro n hn
      rcases hn with hn | hn
      · have := iha n hn; simp only [freeMax]; omega
      · have := ihb n hn; simp only [freeMax]; omega
  | fAll a ih =>
      intro n hn
      have := ih (n + 1) hn
      simp only [freeMax]
      omega
  | fEx a ih =>
      intro n hn
      have := ih (n + 1) hn
      simp only [freeMax]
      omega

/-! The fixed leaves of the successor spine, each evaluated by the kernel
in its own declaration so no single heartbeat budget is shared. -/

set_option maxHeartbeats 1000000 in
private theorem fm01 : freeMax (fTripleMemF 2 1 0 4) ≤ 5 := by decide
set_option maxHeartbeats 1000000 in
private theorem fm02 : freeMax (fUnivEnvF 1) ≤ 2 := by decide
set_option maxHeartbeats 1000000 in
private theorem fm03 : freeMax (fNumF 1 0) ≤ 2 := by decide
set_option maxHeartbeats 1000000 in
private theorem fm04 : freeMax (fNumF 0 1) ≤ 1 := by decide
set_option maxHeartbeats 1000000 in
private theorem fm05 : freeMax (fTripleMemF 6 5 4 1) ≤ 7 := by decide
set_option maxHeartbeats 1000000 in
private theorem fm06 : freeMax (fTripleMemF 7 6 4 1) ≤ 8 := by decide
set_option maxHeartbeats 1000000 in
private theorem fm07 : freeMax (fTripleMemF 7 6 3 1) ≤ 8 := by decide
set_option maxHeartbeats 1000000 in
private theorem fm08 : freeMax (fLevelImpF 4 3 2 6 1 0) ≤ 7 := by decide
set_option maxHeartbeats 1000000 in
private theorem fm09 : freeMax (fLevelAndF 4 3 2 6 1 0) ≤ 7 := by decide
set_option maxHeartbeats 1000000 in
private theorem fm10 : freeMax (fLevelOrF 4 3 2 6 1 0) ≤ 7 := by decide
set_option maxHeartbeats 1000000 in
private theorem fm11 : freeMax (fTagUnF 5 6 0) ≤ 7 := by decide
set_option maxHeartbeats 1000000 in
private theorem fm12 : freeMax (fTagUnF 5 7 0) ≤ 8 := by decide
set_option maxHeartbeats 1000000 in
private theorem fm13 : freeMax (fPiBoundedF 6 5) ≤ 8 := by decide
set_option maxHeartbeats 1000000 in
private theorem fm14 : freeMax (fSigmaBoundedF 6 5) ≤ 8 := by decide
set_option maxHeartbeats 1000000 in
private theorem fm15 : freeMax (fShiftTripleMemF 1 0 5 8 0) ≤ 9 := by decide
set_option maxHeartbeats 1000000 in
private theorem fm16 : freeMax (fShiftTripleMemF 1 0 5 8 1) ≤ 9 := by decide

set_option maxHeartbeats 2000000 in
private theorem freeMax_closF_zero : freeMax (closF 0) ≤ 2 := by decide

/-- **The closure kernel has free slots below `2`** — uniformly in the
level; this is the free-slot fact consumed by the depth moves under
quotation.  The base case is a kernel evaluation of `freeMax` on the
concrete level-zero kernel.  The successor case walks the disjunction that
`Free` assigns to the unfolded spine: the numeral leaves are `free_fNumF`,
the kernel leaves are the induction hypothesis, and every fixed leaf is one
of the kernel-evaluated bounds above — each case a two-atom linear problem,
never a nested-`max` computation. -/
theorem free_closF : ∀ (n : ℕ) {i : ℕ}, Free i (closF n) → i < 2 := by
  intro n
  induction n with
  | zero =>
      intro i h
      have h1 := free_lt_freeMax (closF 0) i h
      have h2 := freeMax_closF_zero
      omega
  | succ n ih =>
      intro i h
      rw [closF_succ_form] at h
      simp only [lvlInstF, SetTheory.Free, or_false] at h
      casesm* _ ∨ _
      all_goals
        first
        | omega
        | (have h2 := free_fNumF h; omega)
        | (have h2 := ih h; omega)
        | (have h2 := free_lt_freeMax _ _ h
           first
              | (have h3 := fm01; omega)
              | (have h3 := fm02; omega)
              | (have h3 := fm03; omega)
              | (have h3 := fm04; omega)
              | (have h3 := fm05; omega)
              | (have h3 := fm06; omega)
              | (have h3 := fm07; omega)
              | (have h3 := fm08; omega)
              | (have h3 := fm09; omega)
              | (have h3 := fm10; omega)
              | (have h3 := fm11; omega)
              | (have h3 := fm12; omega)
              | (have h3 := fm13; omega)
              | (have h3 := fm14; omega)
              | (have h3 := fm15; omega)
              | (have h3 := fm16; omega))

end FreeMax

/-! ## The fixed codes

The `n`-independent leaves of the successor spine, as standard
natural-number codes at the exact translation depths where they occur:
depth `2` is the canonical kernel depth, three universal quantifiers put
the implication at depth `5`, the two justification existentials put the
clause row at depth `7`, one clause existential puts its body at depth `8`,
and the two existentials of an unfolded instance put its leaves at depths
`9` (delegation row) and `10` (quantifier clauses). -/

section FixedCodes

/-- Code of the head membership atom `fTripleMemF 2 1 0 4` at depth `5`. -/
def tripleMemHeadCode : ℕ := (toSet 5 (fTripleMemF 2 1 0 4)).toNat

/-- Code of the environment condition `fUnivEnvF 1` at depth `5`. -/
def univEnvLeafCode : ℕ := (toSet 5 (fUnivEnvF 1)).toNat

/-- Code of the two bound numerals of the justification row at depth `7`. -/
def numPairLeafCode : ℕ :=
  (toSet 7 (SetTheory.Form.fAnd (fNumF 1 0) (fNumF 0 1))).toNat

/-- Code of the implication clause at depth `7`. -/
def impClauseLeafCode : ℕ := (toSet 7 (fLevelImpF 4 3 2 6 1 0)).toNat

/-- Code of the conjunction clause at depth `7`. -/
def andClauseLeafCode : ℕ := (toSet 7 (fLevelAndF 4 3 2 6 1 0)).toNat

/-- Code of the disjunction clause at depth `7`. -/
def orClauseLeafCode : ℕ := (toSet 7 (fLevelOrF 4 3 2 6 1 0)).toNat

/-- Code of the universal clause's tag equation at depth `8`. -/
def tagAllLeafCode : ℕ := (toSet 8 (fTagUnF 5 6 0)).toNat

/-- Code of the existential clause's tag equation at depth `8`. -/
def tagExLeafCode : ℕ := (toSet 8 (fTagUnF 5 7 0)).toNat

/-- Code of the bit-is-one equation `fEq 3 1` at depth `8`. -/
def eqBitOneLeafCode : ℕ := (toSet 8 (SetTheory.Form.fEq 3 1)).toNat

/-- Code of the bit-is-zero equation `fEq 3 2` at depth `8`. -/
def eqBitZeroLeafCode : ℕ := (toSet 8 (SetTheory.Form.fEq 3 2)).toNat

/-- Code of the Pi-rank bound `fPiBoundedF 6 5` at depth `8`. -/
def piBoundedLeafCode : ℕ := (toSet 8 (fPiBoundedF 6 5)).toNat

/-- Code of the Sigma-rank bound `fSigmaBoundedF 6 5` at depth `8`. -/
def sigmaBoundedLeafCode : ℕ := (toSet 8 (fSigmaBoundedF 6 5)).toNat

/-- Code of the universal clause's counterexample record at depth `8`. -/
def allWitnessLeafCode : ℕ :=
  (toSet 8 (SetTheory.Form.fAnd (.fEq 3 2)
    (.fEx (fShiftTripleMemF 1 0 5 8 0)))).toNat

/-- Code of the existential clause's witness record at depth `8`. -/
def exWitnessLeafCode : ℕ :=
  (toSet 8 (SetTheory.Form.fAnd (.fEq 3 1)
    (.fEx (fShiftTripleMemF 1 0 5 8 1)))).toNat

/-- Code of falsum at depth `8` (the consequent of the delegated-truth
implications). -/
def botLeafCode : ℕ := (toSet 8 SetTheory.Form.fBot).toNat

/-- Code of the delegation row's membership atom at depth `9`. -/
def tripleMemInstACode : ℕ := (toSet 9 (fTripleMemF 6 5 4 1)).toNat

/-- Code of the universal clause's membership atom at depth `10`. -/
def tripleMemInstBCode : ℕ := (toSet 10 (fTripleMemF 7 6 4 1)).toNat

/-- Code of the existential clause's membership atom at depth `10`. -/
def tripleMemInstCCode : ℕ := (toSet 10 (fTripleMemF 7 6 3 1)).toNat

/-- Code of the canonical instance's membership atom at depth `5`:
`levelSatF n 2 1 0` puts its two existentials over depth `3`, so the atom
`fTripleMemF 4 3 2 1` sits at depth `5`. -/
def tripleMemCanonCode : ℕ := (toSet 5 (fTripleMemF 4 3 2 1)).toNat

/-- Code of the concrete level-zero canonical instance at depth `3`. -/
def levelSatZeroCode : ℕ := (toSet 3 (levelSatF 0 2 1 0)).toNat

/-- Code of the concrete level-zero closure kernel at depth `2`. -/
def closZeroCode : ℕ := (toSet 2 (closF 0)).toNat

/-- Code of the Sigma-truth bit witness `fNumF 0 1` at depth `3`. -/
def numOneWitnessCode : ℕ := (toSet 3 (fNumF 0 1)).toNat

/-- Code of the Pi-falsity bit witness `fNumF 0 0` at depth `3`. -/
def numZeroWitnessCode : ℕ := (toSet 3 (fNumF 0 0)).toNat

/-- Code of falsum at the canonical wrapper depth `2`. -/
def botCanonCode : ℕ := (toSet 2 SetTheory.Form.fBot).toNat

end FixedCodes

/-! ## The internal builder

Two primitive recursions on the model (Foundation's `PR` machinery over
`𝗜𝚺₁`):

* `closCode x` — the code of the closure kernel (`closF ·` at depth `2`);
  its successor step re-wraps the previous kernel three times in the fixed
  spine, consuming `numChainCode` of the *index* for the level numerals;
* `levelSatCode x` — the code of the canonical instance (`levelSatF · 2 1 0`
  at depth `3`), whose successor consumes both `numChainCode` and
  `closCode` at the index and never its own previous value.

The derived Sigma/Pi readings are plain (non-recursive) wrappers around
`levelSatCode`.  Totality at every (possibly nonstandard) `x : V` is what
the `PR` constructions' `𝚺₁` induction provides. -/

section InternalBuilder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The coded unfolded-instance shape: two coded existentials over the
level numeral, the closure kernel, and a fixed membership atom. -/
noncomputable def lvlInstPart (t : ℕ) (num cls : V) : V :=
  ^∃ (^∃ (num ^⋏ (cls ^⋏ ↑t)))

/-- Graph of `lvlInstPart t`, argument order `(value, numeral, kernel)`. -/
noncomputable def lvlInstGraph (t : ℕ) : 𝚺₁.Semisentence 3 := .mkSigma
  “y num cls. ∃ a, !qqAndDef a cls ↑t ∧ ∃ b, !qqAndDef b num a ∧
    ∃ e, !qqExsDef e b ∧ !qqExsDef y e”

instance lvlInstPart.defined (t : ℕ) :
    𝚺₁-Function₂ (lvlInstPart t : V → V → V) via lvlInstGraph t := .mk fun v ↦ by
  simp [lvlInstGraph, lvlInstPart, numeral_eq_natCast]


/-! ### The parameter firewall

Foundation's Gödel numbering is Cantor pairing at every constructor, so the
codes of the deep fixed leaves are astronomically large naturals: they may
be *named* but must never be *evaluated*.  A `simp`-driven `Defined` proof
whose goal mentions such a constant can trigger literal evaluation through
arithmetic simprocs.  Every evaluation proof below is therefore stated with
the leaf codes as *variables* — where the machinery is symbolic by
construction — and the concrete constants enter only by instantiating the
proved instance, never through another `simp`. -/

/-- The coded universal clause of the justification row, with the leaf
codes abstracted: the tag equation, then either the delegated Pi-truth of
the code (via the unfolded instance at slots `(7,6,4)`) or the recorded
counterexample. -/
noncomputable def allClausePart (bot pb e1 aw tg : ℕ) (num cls : V) : V :=
  ^∃ (↑tg ^⋏ ((↑e1 ^⋏ (↑pb ^⋏
    Bootstrapping.imp ℒₛₑₜ
      (lvlInstPart tripleMemInstBCode num cls) ↑bot)) ^⋎ ↑aw))

/-- Graph of `allClausePart`, argument order `(value, numeral, kernel)`. -/
noncomputable def allClauseGraphPart (bot pb e1 aw tg : ℕ) : 𝚺₁.Semisentence 3 := .mkSigma
  “y num cls.
    ∃ iB, !(lvlInstGraph tripleMemInstBCode) iB num cls ∧
    ∃ f5, !(Bootstrapping.impGraph ℒₛₑₜ) f5 iB ↑bot ∧
    ∃ f4, !qqAndDef f4 ↑pb f5 ∧
    ∃ f3, !qqAndDef f3 ↑e1 f4 ∧
    ∃ f2, !qqOrDef f2 f3 ↑aw ∧
    ∃ f1, !qqAndDef f1 ↑tg f2 ∧
    !qqExsDef y f1”

instance allClausePart.defined (bot pb e1 aw tg : ℕ) :
    𝚺₁-Function₂ (allClausePart bot pb e1 aw tg : V → V → V)
      via allClauseGraphPart bot pb e1 aw tg := .mk fun v ↦ by
  simp [allClauseGraphPart, allClausePart, numeral_eq_natCast]

/-- The coded universal clause at the concrete leaf codes. -/
noncomputable def allClauseCode : V → V → V :=
  allClausePart botLeafCode piBoundedLeafCode eqBitOneLeafCode
    allWitnessLeafCode tagAllLeafCode

/-- Graph of `allClauseCode`. -/
noncomputable def allClauseGraph : 𝚺₁.Semisentence 3 :=
  allClauseGraphPart botLeafCode piBoundedLeafCode eqBitOneLeafCode
    allWitnessLeafCode tagAllLeafCode

instance allClauseCode.defined :
    𝚺₁-Function₂ (allClauseCode : V → V → V) via allClauseGraph :=
  allClausePart.defined botLeafCode piBoundedLeafCode eqBitOneLeafCode
    allWitnessLeafCode tagAllLeafCode

/-- The coded existential clause of the justification row, with the leaf
codes abstracted: the tag equation, then either the recorded witness or the
delegated Sigma-falsity of the code (via the unfolded instance at slots
`(7,6,3)`). -/
noncomputable def exClausePart (bot sb e0 ew tg : ℕ) (num cls : V) : V :=
  ^∃ (↑tg ^⋏ (↑ew ^⋎ (↑e0 ^⋏ (↑sb ^⋏
    Bootstrapping.imp ℒₛₑₜ
      (lvlInstPart tripleMemInstCCode num cls) ↑bot))))

/-- Graph of `exClausePart`, argument order `(value, numeral, kernel)`. -/
noncomputable def exClauseGraphPart (bot sb e0 ew tg : ℕ) : 𝚺₁.Semisentence 3 := .mkSigma
  “y num cls.
    ∃ iC, !(lvlInstGraph tripleMemInstCCode) iC num cls ∧
    ∃ g5, !(Bootstrapping.impGraph ℒₛₑₜ) g5 iC ↑bot ∧
    ∃ g4, !qqAndDef g4 ↑sb g5 ∧
    ∃ g3, !qqAndDef g3 ↑e0 g4 ∧
    ∃ g2, !qqOrDef g2 ↑ew g3 ∧
    ∃ g1, !qqAndDef g1 ↑tg g2 ∧
    !qqExsDef y g1”

instance exClausePart.defined (bot sb e0 ew tg : ℕ) :
    𝚺₁-Function₂ (exClausePart bot sb e0 ew tg : V → V → V)
      via exClauseGraphPart bot sb e0 ew tg := .mk fun v ↦ by
  simp [exClauseGraphPart, exClausePart, numeral_eq_natCast]

/-- The coded existential clause at the concrete leaf codes. -/
noncomputable def exClauseCode : V → V → V :=
  exClausePart botLeafCode sigmaBoundedLeafCode eqBitZeroLeafCode
    exWitnessLeafCode tagExLeafCode

/-- Graph of `exClauseCode`. -/
noncomputable def exClauseGraph : 𝚺₁.Semisentence 3 :=
  exClauseGraphPart botLeafCode sigmaBoundedLeafCode eqBitZeroLeafCode
    exWitnessLeafCode tagExLeafCode

instance exClauseCode.defined :
    𝚺₁-Function₂ (exClauseCode : V → V → V) via exClauseGraph :=
  exClausePart.defined botLeafCode sigmaBoundedLeafCode eqBitZeroLeafCode
    exWitnessLeafCode tagExLeafCode

/-- The coded justification row, with its direct leaf codes abstracted:
the delegation instance at slots `(6,5,4)`, the three fixed Boolean
clauses, and the two quantifier clauses, under the two bound numerals. -/
noncomputable def justRowPart (np impC andC orC : ℕ) (num cls : V) : V :=
  ^∃ (^∃ (↑np ^⋏
    (lvlInstPart tripleMemInstACode num cls ^⋎
    (↑impC ^⋎
    (↑andC ^⋎
    (↑orC ^⋎
    (allClauseCode num cls ^⋎ exClauseCode num cls)))))))

/-- Graph of `justRowPart`, argument order `(value, numeral, kernel)`. -/
noncomputable def justRowGraphPart (np impC andC orC : ℕ) : 𝚺₁.Semisentence 3 := .mkSigma
  “y num cls.
    ∃ iA, !(lvlInstGraph tripleMemInstACode) iA num cls ∧
    ∃ l5, !allClauseGraph l5 num cls ∧
    ∃ l6, !exClauseGraph l6 num cls ∧
    ∃ d5, !qqOrDef d5 l5 l6 ∧
    ∃ d4, !qqOrDef d4 ↑orC d5 ∧
    ∃ d3, !qqOrDef d3 ↑andC d4 ∧
    ∃ d2, !qqOrDef d2 ↑impC d3 ∧
    ∃ d1, !qqOrDef d1 iA d2 ∧
    ∃ e2, !qqAndDef e2 ↑np d1 ∧
    ∃ e1, !qqExsDef e1 e2 ∧
    !qqExsDef y e1”

instance justRowPart.defined (np impC andC orC : ℕ) :
    𝚺₁-Function₂ (justRowPart np impC andC orC : V → V → V)
      via justRowGraphPart np impC andC orC := .mk fun v ↦ by
  simp [justRowGraphPart, justRowPart, numeral_eq_natCast]

/-- The coded justification row at the concrete leaf codes. -/
noncomputable def justRowCode : V → V → V :=
  justRowPart numPairLeafCode impClauseLeafCode andClauseLeafCode
    orClauseLeafCode

/-- Graph of `justRowCode`. -/
noncomputable def justRowGraph : 𝚺₁.Semisentence 3 :=
  justRowGraphPart numPairLeafCode impClauseLeafCode andClauseLeafCode
    orClauseLeafCode

instance justRowCode.defined :
    𝚺₁-Function₂ (justRowCode : V → V → V) via justRowGraph :=
  justRowPart.defined numPairLeafCode impClauseLeafCode andClauseLeafCode
    orClauseLeafCode

/-- **The coded successor of the closure kernel**, with its two direct
leaf codes abstracted: three coded universal quantifiers over the
implication from the head membership atom to the environment condition and
the justification row. -/
noncomputable def closStepPart (tm ue : ℕ) (num cls : V) : V :=
  ^∀ (^∀ (^∀ (Bootstrapping.imp ℒₛₑₜ ↑tm (↑ue ^⋏ justRowCode num cls))))

/-- Graph of `closStepPart`, argument order `(value, numeral, kernel)`. -/
noncomputable def closStepGraphPart (tm ue : ℕ) : 𝚺₁.Semisentence 3 := .mkSigma
  “y num cls.
    ∃ j, !justRowGraph j num cls ∧
    ∃ b1, !qqAndDef b1 ↑ue j ∧
    ∃ a3, !(Bootstrapping.impGraph ℒₛₑₜ) a3 ↑tm b1 ∧
    ∃ a2, !qqAllDef a2 a3 ∧
    ∃ a1, !qqAllDef a1 a2 ∧
    !qqAllDef y a1”

instance closStepPart.defined (tm ue : ℕ) :
    𝚺₁-Function₂ (closStepPart tm ue : V → V → V)
      via closStepGraphPart tm ue := .mk fun v ↦ by
  simp [closStepGraphPart, closStepPart, numeral_eq_natCast]

/-- The coded successor of the closure kernel at the concrete leaf codes. -/
noncomputable def closStepCode : V → V → V :=
  closStepPart tripleMemHeadCode univEnvLeafCode

/-- Graph of `closStepCode`. -/
noncomputable def closStepGraph : 𝚺₁.Semisentence 3 :=
  closStepGraphPart tripleMemHeadCode univEnvLeafCode

instance closStepCode.defined :
    𝚺₁-Function₂ (closStepCode : V → V → V) via closStepGraph :=
  closStepPart.defined tripleMemHeadCode univEnvLeafCode

/-! ### The closure-kernel tower -/

namespace ClosKernel

/-- Blueprint, with the base code abstracted behind the firewall. -/
noncomputable def blueprint (z : ℕ) : PR.Blueprint 0 where
  zero := .mkSigma “y. y = ↑z”
  succ := .mkSigma “y ih k. ∃ num, !numChainGraph num k ∧ !closStepGraph y num ih”

noncomputable def construction (z : ℕ) : PR.Construction V (blueprint z) where
  zero _ := ↑z
  succ _ k ih := closStepCode (numChainCode k) ih
  zero_defined := .mk fun v ↦ by simp [blueprint, numeral_eq_natCast]
  succ_defined := .mk fun v ↦ by simp [blueprint]

end ClosKernel

/-- The code of `toSet 2 (closF x)`, extended to every model element by
primitive recursion. -/
noncomputable def closCode (x : V) : V :=
  (ClosKernel.construction closZeroCode).result ![] x

/-- Graph of `closCode`. -/
noncomputable def closGraph : 𝚺₁.Semisentence 2 :=
  (ClosKernel.blueprint closZeroCode).resultDef

private lemma closCodeAux_zero (z : ℕ) :
    (ClosKernel.construction z).result ![] (0 : V) = ↑z := by
  simp [ClosKernel.construction]

private lemma closCodeAux_succ (z : ℕ) (x : V) :
    (ClosKernel.construction z).result ![] (x + 1) =
      closStepCode (numChainCode x)
        ((ClosKernel.construction z).result ![] x) := by
  simp [ClosKernel.construction]

@[simp] lemma closCode_zero : closCode (0 : V) = ↑closZeroCode :=
  closCodeAux_zero closZeroCode

@[simp] lemma closCode_succ (x : V) :
    closCode (x + 1) = closStepCode (numChainCode x) (closCode x) :=
  closCodeAux_succ closZeroCode x

instance closCode.defined :
    𝚺₁-Function₁ (closCode : V → V) via closGraph := .mk fun v ↦ by
  simpa [closGraph, closCode, Matrix.empty_eq] using
    (ClosKernel.construction closZeroCode).result_defined_iff v

/-! ### The canonical level tower -/

namespace LevelSatTower

/-- Blueprint, with the base code abstracted behind the firewall. -/
noncomputable def blueprint (z : ℕ) : PR.Blueprint 0 where
  zero := .mkSigma “y. y = ↑z”
  succ := .mkSigma
    “y ih k. ∃ num, !numChainGraph num k ∧ ∃ cls, !closGraph cls k ∧
      !(lvlInstGraph tripleMemCanonCode) y num cls”

noncomputable def construction (z : ℕ) : PR.Construction V (blueprint z) where
  zero _ := ↑z
  succ _ k _ := lvlInstPart tripleMemCanonCode (numChainCode k) (closCode k)
  zero_defined := .mk fun v ↦ by simp [blueprint, numeral_eq_natCast]
  succ_defined := .mk fun v ↦ by simp [blueprint]

end LevelSatTower

/-- The code of `toSet 3 (levelSatF x 2 1 0)`, extended to every model
element.  Its successor reads the numeral chain and the closure kernel at
the *index*, mirroring `levelSatF_succ_eq`, and never its own previous
value. -/
noncomputable def levelSatCode (x : V) : V :=
  (LevelSatTower.construction levelSatZeroCode).result ![] x

/-- Graph of `levelSatCode`. -/
noncomputable def levelSatGraph : 𝚺₁.Semisentence 2 :=
  (LevelSatTower.blueprint levelSatZeroCode).resultDef

private lemma levelSatCodeAux_zero (z : ℕ) :
    (LevelSatTower.construction z).result ![] (0 : V) = ↑z := by
  simp [LevelSatTower.construction]

private lemma levelSatCodeAux_succ (z : ℕ) (x : V) :
    (LevelSatTower.construction z).result ![] (x + 1) =
      lvlInstPart tripleMemCanonCode (numChainCode x) (closCode x) := by
  simp [LevelSatTower.construction]

@[simp] lemma levelSatCode_zero : levelSatCode (0 : V) = ↑levelSatZeroCode :=
  levelSatCodeAux_zero levelSatZeroCode

@[simp] lemma levelSatCode_succ (x : V) :
    levelSatCode (x + 1) =
      lvlInstPart tripleMemCanonCode (numChainCode x) (closCode x) :=
  levelSatCodeAux_succ levelSatZeroCode x

instance levelSatCode.defined :
    𝚺₁-Function₁ (levelSatCode : V → V) via levelSatGraph := .mk fun v ↦ by
  simpa [levelSatGraph, levelSatCode, Matrix.empty_eq] using
    (LevelSatTower.construction levelSatZeroCode).result_defined_iff v

/-! ### The derived Sigma/Pi readings -/

/-- The coded bit-witness wrapper, with the witness code abstracted: one
coded existential and one conjunct around the canonical instance. -/
noncomputable def bitWitnessPart (w : ℕ) (x : V) : V :=
  ^∃ (↑w ^⋏ levelSatCode x)

/-- Graph of `bitWitnessPart`, argument order `(value, index)`. -/
noncomputable def bitWitnessGraphPart (w : ℕ) : 𝚺₁.Semisentence 2 := .mkSigma
  “y x. ∃ ls, !levelSatGraph ls x ∧ ∃ a, !qqAndDef a ↑w ls ∧ !qqExsDef y a”

instance bitWitnessPart.defined (w : ℕ) :
    𝚺₁-Function₁ (bitWitnessPart w : V → V) via bitWitnessGraphPart w := .mk fun v ↦ by
  simp [bitWitnessGraphPart, bitWitnessPart, numeral_eq_natCast]

/-- The code of `toSet 2 (fSigmaTrueF x 1 0)`: the bit-one witness around
the canonical instance. -/
noncomputable def sigmaTrueCode : V → V := bitWitnessPart numOneWitnessCode

/-- Graph of `sigmaTrueCode`. -/
noncomputable def sigmaTrueGraph : 𝚺₁.Semisentence 2 :=
  bitWitnessGraphPart numOneWitnessCode

instance sigmaTrueCode.defined :
    𝚺₁-Function₁ (sigmaTrueCode : V → V) via sigmaTrueGraph :=
  bitWitnessPart.defined numOneWitnessCode

/-- The code of `toSet 2 (fPiFalseF x 1 0)`: the bit-zero witness around
the canonical instance. -/
noncomputable def piFalseCode : V → V := bitWitnessPart numZeroWitnessCode

/-- Graph of `piFalseCode`. -/
noncomputable def piFalseGraph : 𝚺₁.Semisentence 2 :=
  bitWitnessGraphPart numZeroWitnessCode

instance piFalseCode.defined :
    𝚺₁-Function₁ (piFalseCode : V → V) via piFalseGraph :=
  bitWitnessPart.defined numZeroWitnessCode

/-- The coded Pi-truth wrapper, with the falsum code abstracted: the coded
implication from Pi-falsity to falsum. -/
noncomputable def piTruePart (b : ℕ) (x : V) : V :=
  Bootstrapping.imp ℒₛₑₜ (piFalseCode x) ↑b

/-- Graph of `piTruePart`, argument order `(value, index)`. -/
noncomputable def piTrueGraphPart (b : ℕ) : 𝚺₁.Semisentence 2 := .mkSigma
  “y x. ∃ pf, !piFalseGraph pf x ∧ !(Bootstrapping.impGraph ℒₛₑₜ) y pf ↑b”

instance piTruePart.defined (b : ℕ) :
    𝚺₁-Function₁ (piTruePart b : V → V) via piTrueGraphPart b := .mk fun v ↦ by
  simp [piTrueGraphPart, piTruePart, numeral_eq_natCast]

/-- The code of `toSet 2 (fPiTrueF x 1 0)`. -/
noncomputable def piTrueCode : V → V := piTruePart botCanonCode

/-- Graph of `piTrueCode`. -/
noncomputable def piTrueGraph : 𝚺₁.Semisentence 2 := piTrueGraphPart botCanonCode

instance piTrueCode.defined :
    𝚺₁-Function₁ (piTrueCode : V → V) via piTrueGraph :=
  piTruePart.defined botCanonCode

end InternalBuilder

/-! ## Standard points of the tower

At a standard element `↑m` each layer computes exactly the quotation of the
corresponding syntactic object.  All proofs are external inductions driven
by the layers' defining equations, the quotation equations of the
translation, and depth-independence; the fixed leaves are matched against
their named codes by `coe_toNat_eq_quote` alone, never by evaluation. -/

section StandardPoints

open SetTheory (Form Free)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The quotation of an unfolded instance is the coded instance shape on
the canonical numeral and kernel quotes.  The inner depth is passed
explicitly so that the membership atom's code appears at the literal depth
of its named constant. -/
theorem quote_lvlInstF (m c e b k d : ℕ) (hd : k + 1 + 1 = d) :
    (⌜toSet k (lvlInstF m c e b)⌝ : V) =
      lvlInstPart ((toSet d (fTripleMemF c e b 1)).toNat)
        (⌜toSet 1 (fNumF 0 m)⌝ : V) (⌜toSet 2 (closF m)⌝ : V) := by
  subst hd
  have hq : (⌜toSet k (lvlInstF m c e b)⌝ : V) =
      ^∃ (^∃ ((⌜toSet (k + 1 + 1) (fNumF 0 m)⌝ : V) ^⋏
        ((⌜toSet (k + 1 + 1) (closF m)⌝ : V) ^⋏
         (⌜toSet (k + 1 + 1) (fTripleMemF c e b 1)⌝ : V)))) := by
    simp [lvlInstF, toSet]
  have hnum : (⌜toSet (k + 1 + 1) (fNumF 0 m)⌝ : V) = ⌜toSet 1 (fNumF 0 m)⌝ :=
    quote_toSet_congr (fun i hi => by have := free_fNumF hi; omega)
      (fun i hi => by have := free_fNumF hi; omega)
  have hcls : (⌜toSet (k + 1 + 1) (closF m)⌝ : V) = ⌜toSet 2 (closF m)⌝ :=
    quote_toSet_congr (fun i hi => by have := free_closF m hi; omega)
      (fun i hi => free_closF m hi)
  rw [hq, hnum, hcls,
    ← coe_toNat_eq_quote (V := V) (toSet (k + 1 + 1) (fTripleMemF c e b 1))]
  rfl

/-! ### The fixed pieces of the successor spine, named at the Form level -/

private def headTMF : Form := fTripleMemF 2 1 0 4
private def envF : Form := fUnivEnvF 1
private def numPairF : Form := .fAnd (fNumF 1 0) (fNumF 0 1)
private def impClauseF : Form := fLevelImpF 4 3 2 6 1 0
private def andClauseF : Form := fLevelAndF 4 3 2 6 1 0
private def orClauseF : Form := fLevelOrF 4 3 2 6 1 0
private def tagAllF : Form := fTagUnF 5 6 0
private def tagExF : Form := fTagUnF 5 7 0
private def eqOneF : Form := .fEq 3 1
private def eqZeroF : Form := .fEq 3 2
private def piBddF : Form := fPiBoundedF 6 5
private def sigBddF : Form := fSigmaBoundedF 6 5
private def allWitF : Form := .fAnd (.fEq 3 2) (.fEx (fShiftTripleMemF 1 0 5 8 0))
private def exWitF : Form := .fAnd (.fEq 3 1) (.fEx (fShiftTripleMemF 1 0 5 8 1))

private def allClauseF (m : ℕ) : Form :=
  .fEx (.fAnd tagAllF (.fOr (.fAnd eqOneF (.fAnd piBddF
    (.fImp (lvlInstF m 7 6 4) .fBot))) allWitF))

private def exClauseF (m : ℕ) : Form :=
  .fEx (.fAnd tagExF (.fOr exWitF (.fAnd eqZeroF (.fAnd sigBddF
    (.fImp (lvlInstF m 7 6 3) .fBot)))))

private def justF (m : ℕ) : Form :=
  .fEx (.fEx (.fAnd numPairF (.fOr (lvlInstF m 6 5 4) (.fOr impClauseF
    (.fOr andClauseF (.fOr orClauseF (.fOr (allClauseF m) (exClauseF m))))))))

private def restF (m : ℕ) : Form := .fAnd envF (justF m)

/-- `closF_succ_form`, restated through the named pieces. -/
private theorem closF_succ_form' (m : ℕ) :
    closF (m + 1) = .fAll (.fAll (.fAll (.fImp headTMF (restF m)))) := rfl

/-- **Quotation of the successor kernel**: the quote of `closF (m+1)` is
the coded successor step applied to the canonical numeral and kernel
quotes.  This is the equation that ties the internal recursion to the
external one. -/
theorem quote_closF_succ (m : ℕ) :
    (⌜toSet 2 (closF (m + 1))⌝ : V) =
      closStepCode (⌜toSet 1 (fNumF 0 m)⌝ : V) (⌜toSet 2 (closF m)⌝ : V) := by
  have hA : (⌜toSet 2 (closF (m + 1))⌝ : V) =
      ^∀ (^∀ (^∀ (⌜toSet 5 (Form.fImp headTMF (restF m))⌝ : V))) := by
    rw [closF_succ_form']
    simp [toSet]
  have hImp := quote_toSet_fImp (V := V) 5 headTMF (restF m)
  have hRest : (⌜toSet 5 (restF m)⌝ : V) =
      (⌜toSet 5 envF⌝ : V) ^⋏
        (^∃ (^∃ ((⌜toSet 7 numPairF⌝ : V) ^⋏
          ((⌜toSet 7 (lvlInstF m 6 5 4)⌝ : V) ^⋎
          ((⌜toSet 7 impClauseF⌝ : V) ^⋎
          ((⌜toSet 7 andClauseF⌝ : V) ^⋎
          ((⌜toSet 7 orClauseF⌝ : V) ^⋎
          ((^∃ ((⌜toSet 8 tagAllF⌝ : V) ^⋏
              (((⌜toSet 8 eqOneF⌝ : V) ^⋏ ((⌜toSet 8 piBddF⌝ : V) ^⋏
                  (⌜toSet 8 (Form.fImp (lvlInstF m 7 6 4) Form.fBot)⌝ : V))) ^⋎
               (⌜toSet 8 allWitF⌝ : V)))) ^⋎
           (^∃ ((⌜toSet 8 tagExF⌝ : V) ^⋏
              ((⌜toSet 8 exWitF⌝ : V) ^⋎
               ((⌜toSet 8 eqZeroF⌝ : V) ^⋏ ((⌜toSet 8 sigBddF⌝ : V) ^⋏
                  (⌜toSet 8 (Form.fImp (lvlInstF m 7 6 3) Form.fBot)⌝ : V)))))))))))))) := by
    simp [restF, justF, allClauseF, exClauseF, toSet]
  have hImpB := quote_toSet_fImp (V := V) 8 (lvlInstF m 7 6 4) Form.fBot
  have hImpC := quote_toSet_fImp (V := V) 8 (lvlInstF m 7 6 3) Form.fBot
  have hLA := quote_lvlInstF (V := V) m 6 5 4 7 9 rfl
  have hLB := quote_lvlInstF (V := V) m 7 6 4 8 10 rfl
  have hLC := quote_lvlInstF (V := V) m 7 6 3 8 10 rfl
  rw [hA, hImp, hRest, hImpB, hImpC, hLA, hLB, hLC,
    ← coe_toNat_eq_quote (V := V) (toSet 5 headTMF),
    ← coe_toNat_eq_quote (V := V) (toSet 5 envF),
    ← coe_toNat_eq_quote (V := V) (toSet 7 numPairF),
    ← coe_toNat_eq_quote (V := V) (toSet 7 impClauseF),
    ← coe_toNat_eq_quote (V := V) (toSet 7 andClauseF),
    ← coe_toNat_eq_quote (V := V) (toSet 7 orClauseF),
    ← coe_toNat_eq_quote (V := V) (toSet 8 tagAllF),
    ← coe_toNat_eq_quote (V := V) (toSet 8 eqOneF),
    ← coe_toNat_eq_quote (V := V) (toSet 8 piBddF),
    ← coe_toNat_eq_quote (V := V) (toSet 8 allWitF),
    ← coe_toNat_eq_quote (V := V) (toSet 8 tagExF),
    ← coe_toNat_eq_quote (V := V) (toSet 8 exWitF),
    ← coe_toNat_eq_quote (V := V) (toSet 8 eqZeroF),
    ← coe_toNat_eq_quote (V := V) (toSet 8 sigBddF),
    ← coe_toNat_eq_quote (V := V) (toSet 8 Form.fBot)]
  rfl

/-- The kernel tower agrees with the quotation of the closure kernel at
depth `2`. -/
theorem closCode_natCast (m : ℕ) :
    closCode ((m : ℕ) : V) = ⌜toSet 2 (closF m)⌝ := by
  induction m with
  | zero =>
      rw [Nat.cast_zero, closCode_zero]
      exact coe_toNat_eq_quote _
  | succ m ih =>
      rw [Nat.cast_succ, closCode_succ, numChainCode_natCast, ih,
        quote_closF_succ]

/-- The successor of the canonical instance is the instance shape at the
canonical shifted slots. -/
theorem levelSatF_succ_canonical (m : ℕ) :
    levelSatF (m + 1) 2 1 0 = lvlInstF m 4 3 2 := rfl

/-- **The canonical tower agrees with the quotation of the level-indexed
family** at slots `(2,1,0)` and depth `3`. -/
theorem levelSatCode_natCast (m : ℕ) :
    levelSatCode ((m : ℕ) : V) = ⌜toSet 3 (levelSatF m 2 1 0)⌝ := by
  cases m with
  | zero =>
      rw [Nat.cast_zero, levelSatCode_zero]
      exact coe_toNat_eq_quote _
  | succ m =>
      rw [Nat.cast_succ, levelSatCode_succ, numChainCode_natCast,
        closCode_natCast, levelSatF_succ_canonical,
        quote_lvlInstF (V := V) m 4 3 2 3 5 rfl]
      rfl

/-- The Sigma-truth wrapper agrees with the quotation of `fSigmaTrueF` at
slots `(1,0)` and depth `2`. -/
theorem sigmaTrueCode_natCast (m : ℕ) :
    sigmaTrueCode ((m : ℕ) : V) = ⌜toSet 2 (fSigmaTrueF m 1 0)⌝ := by
  have hq : (⌜toSet 2 (fSigmaTrueF m 1 0)⌝ : V) =
      ^∃ ((⌜toSet 3 (fNumF 0 1)⌝ : V) ^⋏ (⌜toSet 3 (levelSatF m 2 1 0)⌝ : V)) := by
    rw [fSigmaTrueF_canonical]
    simp [toSet]
  rw [hq, ← levelSatCode_natCast,
    ← coe_toNat_eq_quote (V := V) (toSet 3 (fNumF 0 1))]
  rfl

/-- The Pi-falsity wrapper agrees with the quotation of `fPiFalseF` at
slots `(1,0)` and depth `2`. -/
theorem piFalseCode_natCast (m : ℕ) :
    piFalseCode ((m : ℕ) : V) = ⌜toSet 2 (fPiFalseF m 1 0)⌝ := by
  have hq : (⌜toSet 2 (fPiFalseF m 1 0)⌝ : V) =
      ^∃ ((⌜toSet 3 (fNumF 0 0)⌝ : V) ^⋏ (⌜toSet 3 (levelSatF m 2 1 0)⌝ : V)) := by
    rw [fPiFalseF_canonical]
    simp [toSet]
  rw [hq, ← levelSatCode_natCast,
    ← coe_toNat_eq_quote (V := V) (toSet 3 (fNumF 0 0))]
  rfl

/-- The Pi-truth wrapper agrees with the quotation of `fPiTrueF` at slots
`(1,0)` and depth `2`. -/
theorem piTrueCode_natCast (m : ℕ) :
    piTrueCode ((m : ℕ) : V) = ⌜toSet 2 (fPiTrueF m 1 0)⌝ := by
  rw [show toSet 2 (fPiTrueF m 1 0) =
        toSet 2 (Form.fImp (fPiFalseF m 1 0) Form.fBot) from rfl,
    quote_toSet_fImp (V := V) 2 (fPiFalseF m 1 0) Form.fBot,
    ← piFalseCode_natCast,
    ← coe_toNat_eq_quote (V := V) (toSet 2 Form.fBot)]
  rfl

end StandardPoints

/-! ## The functional relation `LevelSatCode` -/

section CodeRelation

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **The internal code relation of the tower**: `c` is the code the tower
assigns to the (possibly nonstandard) level `x`.  Being the graph of a
function, it is total and single-valued by construction; the substantive
facts are its `𝚺₁` definedness (`levelSatCode.defined`) and its standard
points (`levelSatCode_quote_numeral`). -/
def LevelSatCode (c x : V) : Prop := c = levelSatCode x

/-- The `𝚺₁` graph means the relation, in every model. -/
theorem eval_levelSatGraph_iff {c x : V} :
    levelSatGraph.val.Evalb ![c, x] ↔ LevelSatCode c x := by
  simp [LevelSatCode]

/-- Totality of the tower at every model element, including nonstandard
ones — this is where the `𝚺₁` induction inside `V` (packaged in
Foundation's `PR` constructions) is consumed. -/
theorem levelSatCode_total (x : V) : ∃ c : V, LevelSatCode c x :=
  ⟨levelSatCode x, rfl⟩

/-- Single-valuedness of the tower. -/
theorem levelSatCode_functional {c₁ c₂ x : V}
    (h₁ : LevelSatCode c₁ x) (h₂ : LevelSatCode c₂ x) : c₁ = c₂ :=
  h₁.trans h₂.symm

/-- Totality and single-valuedness, packaged. -/
theorem levelSatCode_existsUnique (x : V) : ∃! c : V, LevelSatCode c x :=
  ⟨levelSatCode x, rfl, fun _ h => h⟩

/-- **Quotation agreement at standard points**, phrased on the numeral. -/
theorem levelSatCode_quote_numeral (n : ℕ) :
    LevelSatCode (⌜toSet 3 (levelSatF n 2 1 0)⌝ : V) (ORingStructure.numeral n) := by
  show (⌜toSet 3 (levelSatF n 2 1 0)⌝ : V) = levelSatCode (ORingStructure.numeral n)
  rw [numeral_eq_natCast, levelSatCode_natCast]

/-- The Sigma-truth wrapper on the numeral. -/
theorem sigmaTrueCode_quote_numeral (n : ℕ) :
    sigmaTrueCode (ORingStructure.numeral n : V) = ⌜toSet 2 (fSigmaTrueF n 1 0)⌝ := by
  rw [numeral_eq_natCast, sigmaTrueCode_natCast]

/-- The Pi-falsity wrapper on the numeral. -/
theorem piFalseCode_quote_numeral (n : ℕ) :
    piFalseCode (ORingStructure.numeral n : V) = ⌜toSet 2 (fPiFalseF n 1 0)⌝ := by
  rw [numeral_eq_natCast, piFalseCode_natCast]

/-- The Pi-truth wrapper on the numeral. -/
theorem piTrueCode_quote_numeral (n : ℕ) :
    piTrueCode (ORingStructure.numeral n : V) = ⌜toSet 2 (fPiTrueF n 1 0)⌝ := by
  rw [numeral_eq_natCast, piTrueCode_natCast]

end CodeRelation

end ZFCinPA
end LeanProofs
