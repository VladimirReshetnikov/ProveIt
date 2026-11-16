import Mathlib

/-!
# Object-theory compilation outline for hypergeometric identities

This file is an **interface sketch**, not a completed formalization.  It keeps
the intended ProveIt theorem shapes explicit while remaining independent of
unstable repository import paths.  The implementation should replace the
abstract fields below with:

* `LeanProofs.ConciseIPRA.PTm`, `Fm`, `PRAAx`, and `Prf`;
* arithmetic symbols and derived lemmas from
  `IPRADerivations.Core.Definitions`, `Core.BoundedSums`, `Core.Pairing`,
  `Core.Division`, `Core.Gcd`, and `Core.Tactic`;
* the transfer theorem `pra_iff_native` after each ordinary iPRA derivation is
  complete.

No declaration below is evidence that the corresponding object-theory
sequent has been derived.
-/

set_option autoImplicit false

namespace HypergeometricIPRA

/-- Minimal abstract surface needed from the embedded iPRA calculus. -/
class PRAKit where
  Term : Type
  Formula : Type
  Derivation : Formula → Type
  zero : Term
  succ : Term → Term
  add mul : Term → Term → Term
  eq : Term → Term → Formula
  imp conj : Formula → Formula → Formula
  all : Formula → Formula
  natLit : ℕ → Term

/-- Codes used by the concrete implementation.  Every field is primitive
recursive in the metatheory and will be represented by a numerical term. -/
structure RationalCode where
  numSign : ℕ
  numMag : ℕ
  denPred : ℕ

structure ComplexCode where
  re : RationalCode
  im : RationalCode

/-- Input contract for one fixed hypergeometric parameter tuple. -/
structure HypergeometricProgram where
  a b c z : ComplexCode
  coeffProgram : ℕ
  partialSumProgram : ℕ
  denomMarginProgram : ℕ
  ratioCutoffProgram : ℕ
  tailModulusProgram : ℕ

/-- The implementation target corresponding to a closed derivation
`([] : List (Fm PTm 0)) ⊢[PRAAx] φ`. -/
structure ClosedTarget (K : PRAKit) where
  sentence : K.Formula
  derivation : Option (K.Derivation sentence)

/-- Names of the planned object-theory milestones. -/
inductive Milestone
  | risingRecurrence
  | risingZeroCriterion
  | coefficientRatio
  | derivativeIdentity
  | gaussODE
  | terminatingVandermonde
  | jacobiSpecialization
  | contiguousRelations
  | finiteContinuedFraction
  | cubicRadical
  | diskTail
  | eulerIntegral
  | gaussSummation
  deriving Repr, DecidableEq

/-- Audit record used while migrating a metatheoretic Lean theorem into an
object-theory derivation. -/
structure AuditRow where
  milestone : Milestone
  targetModule : String
  formulaName : String
  inductionVariable : Option String
  invariant : String
  denominatorGuards : List String
  usesClassicalInObjectTheory : Bool
  compiled : Bool
  kernelChecked : Bool
  noSorryAx : Bool
  deriving Repr

/-- Recommended initial audit table. -/
def initialAudit : List AuditRow := [
  { milestone := .risingRecurrence,
    targetModule := "SpecialFunctions/Hypergeometric/Pochhammer",
    formulaName := "rising_succ",
    inductionVariable := none,
    invariant := "defining equation",
    denominatorGuards := [],
    usesClassicalInObjectTheory := false,
    compiled := false, kernelChecked := false, noSorryAx := false },
  { milestone := .coefficientRatio,
    targetModule := "SpecialFunctions/Hypergeometric/Coefficients",
    formulaName := "hg_coeff_ratio",
    inductionVariable := none,
    invariant := "cleared-denominator polynomial identity",
    denominatorGuards := ["(c)_n != 0", "c+n != 0"],
    usesClassicalInObjectTheory := false,
    compiled := false, kernelChecked := false, noSorryAx := false },
  { milestone := .gaussODE,
    targetModule := "SpecialFunctions/Hypergeometric/ODE",
    formulaName := "gauss_residual",
    inductionVariable := some "n",
    invariant := "coefficient recurrence through index n",
    denominatorGuards := ["(c)_(n+1) != 0"],
    usesClassicalInObjectTheory := false,
    compiled := false, kernelChecked := false, noSorryAx := false },
  { milestone := .terminatingVandermonde,
    targetModule := "SpecialFunctions/Hypergeometric/Vandermonde",
    formulaName := "chu_vandermonde",
    inductionVariable := some "m",
    invariant := "finite sum after multiplication by (c)_m",
    denominatorGuards := ["(c)_j != 0 for j <= m"],
    usesClassicalInObjectTheory := false,
    compiled := false, kernelChecked := false, noSorryAx := false },
  { milestone := .diskTail,
    targetModule := "SpecialFunctions/Hypergeometric/Tail",
    formulaName := "hg_cauchy_modulus",
    inductionVariable := some "N",
    invariant := "term bound A*r^(N-N0)",
    denominatorGuards := ["apartness margin for c+n"],
    usesClassicalInObjectTheory := false,
    compiled := false, kernelChecked := false, noSorryAx := false }
]

/-- A completed row must carry all three implementation flags. -/
def AuditRow.complete (r : AuditRow) : Bool :=
  r.compiled && r.kernelChecked && r.noSorryAx

end HypergeometricIPRA
