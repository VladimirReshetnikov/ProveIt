import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.GaussianGammaGaussReflectionSine
import IPRADerivations.Analysis.Trigonometry.SineProducts.GaussianSineProductT7Actual

/-!
# Cleared reflection for every original Gauss reference row

The two Gamma operands are exactly the reference names at `r/m` and
`(m-r)/m`. The sine operand is exactly the original cyclic sine name
used in the finite normalization of M1.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaGaussReflectionRow

open_ipra
open GaussianCyclicExponentialRoots (angleF)
open GaussianCyclicFullHalfAngle (sineData)
open GaussianGammaReciprocalInverse (gammaF gammaData gamma_regular)
open GaussianGammaGaussReflectionDomain
  (source argument complement referenceData pairData modulus_positive reflection_source reference_at pair_regular gamma_pair_cross)
open GaussianGammaGaussReflectionSine (reflection_input sine_cross)
open GaussianGammaReflectionProduct (gammaPairF complementaryData)
open GaussianGammaReflectionSineTransfer
  (argumentF argumentData argumentRadius sineAtPiF sineAtPiData)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNamedSmallPerturbationTransport (product_at productClock)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianRationalHorner (qmul)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "S" => GaussianNamedSineFromExponential.sineF angleF
local notation "P" => GaussianGammaHalfPiName.nameF
local notation "gneg" => ComplexLogarithmRemainder.neg

def rowF : PR 2 := multiplyF S gammaPairF
def rowData (r m x : PTm n) : PTm n := multiplyData S gammaPairF (sineData r m x) (pairData r m)

ipra_subst rowData

theorem cyclic_source (r m : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] GaussianCyclicExponentialRoots.source r m :=
  .andI (modulus_positive r m h) (le_of_lt h.andE₂)

theorem row_regular (r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] pointCN rowF (rowData r m x) :=
  multiply_fast _ _ _ _ (GaussianCyclicFullHalfAngle.sine_regular r m x (cyclic_source r m h)) (pair_regular r m h)

theorem gamma_pair_at (p r m : PTm n) :
    Γ ⊢[PRAAx] ap2 gammaPairF p (pairData r m) ≐
      qmul (ap2 gammaF (productClock gammaF gammaF (referenceData r m) (referenceData (complement r m) m) p)
        (referenceData r m)) (ap2 gammaF
        (productClock gammaF gammaF (referenceData r m) (referenceData (complement r m) m) p)
        (referenceData (complement r m) m)) :=
  product_at gammaF gammaF _ _ p

theorem row_at (p r m x : PTm n) :
    Γ ⊢[PRAAx] ap2 rowF p (rowData r m x) ≐
      qmul (GaussianCyclicFullHalfAngle.sineSample (productClock S gammaPairF (sineData r m x) (pairData r m) p) r m x)
        (ap2 gammaPairF (productClock S gammaPairF (sineData r m x) (pairData r m) p) (pairData r m)) :=
  product_at S gammaPairF _ _ p

theorem reflection_row (r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] crossEquivalent rowF P (rowData r m x) x := by
  let z := argument r
  let s := sineData r m x
  let t := sineAtPiData z m x
  let g := pairData r m
  let k := complementaryData z one m m m
  have hs := reflection_source r m h
  have hc := cyclic_source r m h
  have ht : Γ ⊢[PRAAx] pointCN sineAtPiF t :=
    GaussianNamedSineFromExponential.sine_regular (GaussianNamedSineTaylor.imaginaryF argumentF)
      (argumentRadius z m x) (argumentData z m x) (reflection_input r m x)
  have hk : Γ ⊢[PRAAx] pointCN gammaPairF k :=
    multiply_fast gammaF gammaF (referenceData r m) (gammaData (shifted (gneg z) m) (one+one) m m)
      (gamma_regular _ _ _ _ _ (reference_at r m h))
      (gamma_regular _ _ _ _ _ (GaussianGammaShift.shifted_source _ _ _ _ _ _ _ hs.andE₂))
  have align := multiply_cross S sineAtPiF gammaPairF gammaPairF s t g k
    (GaussianCyclicFullHalfAngle.sine_regular r m x hc) ht (pair_regular r m h) hk
    (sine_cross r m x hc) (cross_symm _ _ _ _ (gamma_pair_cross r m h))
  exact cross_trans _ _ _ _ _ _ align
    (GaussianSineProductT7Actual.original_cleared_reflection z one m one m one m x hs)

theorem actual_Gauss_cleared_reflection_row_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source (var 2) (var 1) ⟶ crossEquivalent rowF P (rowData (var 2) (var 1) (var 0)) (var 0)) :=
  closeUniv 3 (.impI (reflection_row _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaGaussReflectionRow
