import ConciseIPRA.NativeBiInterpretation

/-!
# Object-theory interfaces for constructive zeta zero distribution

STATUS: UNCOMPILED INTERFACE, NOT A FORMALIZATION OF THE ANALYTIC THEOREMS.

Inspected API: VladimirReshetnikov/ProveIt at
b5a3ad037723c44d69a3d5b28a950c554327a989, Lean/mathlib v4.32.0.
The declarations below define finite data and the required proof types.
No analytic theorem is added as an axiom. No value of `Completed` is
constructed. Arbitrary PR definitions do not satisfy the intended contracts:
the fixed definitions must first be compiled and their meanings established.
-/

namespace ZetaZerosIPRA.Blueprint

open LeanProofs.ConciseIPRA

/-- A rational code; the mathematical denominator is `denMinusOne + 1`.
An eventual PR compiler encodes the signed numerator by naturals. -/
structure RationalData where
  numerator : Int
  denMinusOne : Nat

structure ComplexRationalData where
  re : RationalData
  im : RationalData

/-- Data only. The certificate checker must recompute every sample using
the fixed zeta/xi approximant and verify its rational inequalities. -/
structure ContourData where
  domainVertices : List ComplexRationalData
  imageVertices : List ComplexRationalData
  samplePrecision : Nat
  analyticBoxBound : Nat
  derivativeBound : Nat
  positiveMargin : RationalData
  signedWinding : Int

/-- Equality to the Boolean value one for one FIXED PR definition.
The variables are natural codes, not arbitrary PR program codes. -/
def eqOne {n : Nat} (check : PR n) : Fm PTm n :=
  Fm.eq (PTm.app check Syn.var) (PTm.succ PTm.zero)

/-- Close an explicitly finite list of numerical variables. -/
def allClose : {n : Nat} → Fm PTm n → Fm PTm 0
  | 0, phi => phi
  | n + 1, phi => @allClose n (Fm.all phi)

def correctnessSentence {n : Nat} (check : PR n) : Fm PTm 0 :=
  allClose (eqOne check)

theorem eqOne_qf {n : Nat} (check : PR n) : (eqOne check).QF := by
  trivial

/-- A supplied internal derivation transfers to the native scalar core.
This theorem does not provide the supplied derivation. -/
theorem transfer {phi : Fm PTm 0} (h : Prf PRAAx [] phi) :
    NPrf [] (NFm.ofPRA phi) := by
  simpa using (pra_iff_native (Γ := []) (φ := phi)).mp h

/-- Object-language formula expressing validity of a generated contour.
`generate` and `valid` are separately fixed PR syntax trees. -/
def generatedValidMatrix (generate valid : PR 1) : Fm PTm 1 :=
  Fm.eq
    (PTm.app valid (fun _ => PTm.app generate Syn.var))
    (PTm.succ PTm.zero)

def generatedValidSentence (generate valid : PR 1) : Fm PTm 0 :=
  Fm.all (generatedValidMatrix generate valid)

/-!
`ProgramContracts` is an implementation boundary. The accompanying report
specifies each fixed Boolean check, including what invalid input means.
Correctness of a conditional count checker is separate from correctness of
the contour generator; omitting the latter would weaken the distribution
theorems and would not establish unbounded zero counts.
-/

structure ProgramContracts where
  generateContour : PR 1
  validGeneratedContour : PR 1
  nonvanishingCheck : PR 4
  trivialZeroCheck : PR 3
  symmetryCheck : PR 4
  contourCountCheck : PR 4
  reciprocalTailCheck : PR 3

/-- The final completion obligations. This type is intentionally not
inhabited here. The analytic content is in the missing INTERNAL proofs. -/
structure Completed (p : ProgramContracts) : Prop where
  generatedContour :
    Prf PRAAx [] (generatedValidSentence p.generateContour p.validGeneratedContour)
  nonvanishing : Prf PRAAx [] (correctnessSentence p.nonvanishingCheck)
  trivialZeros : Prf PRAAx [] (correctnessSentence p.trivialZeroCheck)
  symmetry : Prf PRAAx [] (correctnessSentence p.symmetryCheck)
  contourCount : Prf PRAAx [] (correctnessSentence p.contourCountCheck)
  reciprocalTail : Prf PRAAx [] (correctnessSentence p.reciprocalTailCheck)

theorem completed_count_transfers (p : ProgramContracts) (h : Completed p) :
    NPrf [] (NFm.ofPRA (correctnessSentence p.contourCountCheck)) :=
  transfer h.contourCount

theorem completed_generator_transfers (p : ProgramContracts) (h : Completed p) :
    NPrf [] (NFm.ofPRA
      (generatedValidSentence p.generateContour p.validGeneratedContour)) :=
  transfer h.generatedContour

end ZetaZerosIPRA.Blueprint
