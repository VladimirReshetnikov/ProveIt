import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.GaussianGammaGaussPositiveReferenceRows
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.GaussianGammaGaussReferenceSquare

/-!
# Positive square-root certificate for the original Gauss reference product

The real name uses the original Gamma observations at the explicit
positivity clocks, with the same arguments as the reference product.
Every sample is real and has a modulus of at least (36^{-N}).
Its square is equivalent to the independent ((2pi)^N/(N+1)) name.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianGammaGaussPositiveReference

open_ipra
open GaussianGammaGaussPositiveReferenceRows (lowerDen denominator_positive)
open GaussianGammaGaussReflectionDomain (referenceData)
open GaussianGammaGaussReflectionFamily (rightBody right_ascending_at right_rows)
open GaussianGammaGaussReflectionReferenceProducts (right_reference_product)
open GaussianCyclicSineProductSquare (data)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianGammaGaussReferenceSquare (normalizationF normalizationData actual_square_normalization)
open GaussianGammaGaussReferenceSquareAlgebra (referenceSquareF referenceSquareData)
open GaussianNamedFiniteProductFamily (regularRows productData rowF radius family_product_regular)
open GaussianNamedFiniteProductFamilyCongruence (equalRows equal_at family_product_cross)
open GaussianNamedFiniteProductName (clock)
open GaussianNamedFiniteProductApartness (denominator rowLower rowLowerAt)
open GaussianRationalNonnegativeProducts (nonnegative nonnegativeRows)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameReciprocal (lower lower_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => GaussianGammaGaussPositiveReferenceRows.nameF
local notation "R" => GaussianGammaGaussReferenceProduct.nameF
local notation "FProd" => GaussianNamedFiniteProductName.nameF

def body : PTm 2 := GaussianNamedPositiveLateLogSource.retimedData rightBody (num 18)
def nameF : PR 2 := FProd (rowF G body)
def nameData (N x : PTm n) : PTm n := productData G body N (data N x)
def lowerDenominator (N : PTm n) : PTm n := denominator lowerDen N

ipra_subst nameData [productData]
ipra_subst lowerDenominator

theorem body_at (N x i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] inst2 body i (data N x) ≐ GaussianGammaGaussPositiveReferenceRows.nameData (succ i) (succ N) := by
  let a := inst2 rightBody i (data N x)
  let b := referenceData (succ i) (succ N)
  have eq := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (GaussianNamedPositiveLateLogSource.retimedData (var 0) (num 18) : PTm 1)
    (σ := ![a]) (σ' := ![b]) (fun j => by fin_cases j; exact right_ascending_at N x i hi)
  simpa [body,GaussianGammaGaussPositiveReferenceRows.nameData,inst2,a,b] using eq

theorem rows_cross (N x : PTm n) :
    Γ ⊢[PRAAx] equalRows gammaF G rightBody body N (data N x) (data N x) := by
  refine .allI (.impI ?_)
  let K := Syn.shift N
  let y := Syn.shift x
  let i : PTm (n+1) := var 0
  let Δ := lt i K :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt i K := Prf.hyp0
  have h := GaussianGammaGaussPositiveReferenceRows.original_cross (succ i) (succ K)
    (zero_lt_succ i) (le_trans hi (le_succ_self K))
  have d := GaussianGammaRealValues.cross_right_data (body_at K y i hi).eqSymm h
  have e := GaussianGammaRealValues.cross_right_data (right_ascending_at K y i hi).eqSymm
    (cross_symm _ _ _ _ d)
  simpa [equalRows,Syn.shift,Δ,K,y,i] using cross_symm _ _ _ _ e

theorem regular_rows (N x : PTm n) : Γ ⊢[PRAAx] regularRows G body N (data N x) := by
  refine .allI (.impI ?_)
  let K := Syn.shift N
  let y := Syn.shift x
  let i : PTm (n+1) := var 0
  let Δ := lt i K :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt i K := Prf.hyp0
  have c := equal_at gammaF G rightBody body K (data K y) (data K y) i (rows_cross K y) hi
  have reg : Δ ⊢[PRAAx] pointCN G (inst2 body i (data K y)) :=
    cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ c) c
  simpa [regularRows,Syn.shift,Δ,K,y,i] using reg

theorem name_regular (N x : PTm n) : Γ ⊢[PRAAx] pointCN nameF (nameData N x) :=
  family_product_regular G body N (data N x) (regular_rows N x)

theorem original_cross (N x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent R nameF (GaussianGammaGaussReferenceProduct.data (succ N)) (nameData N x) :=
  cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (right_reference_product N x))
    (family_product_cross gammaF G rightBody body N (data N x) (data N x)
      (right_rows N x) (regular_rows N x) (rows_cross N x))

private theorem row_at (p N x i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] ap3 (rowF G body) p i (data N x) ≐
      ap2 G p (GaussianGammaGaussPositiveReferenceRows.nameData (succ i) (succ N)) :=
  (GaussianNamedFiniteProductFamily.row_at G body p i (data N x)).eqTrans
    (congrAp2 G (.eqRefl _) (body_at N x i hi))

private theorem nonnegative_rows (p N x : PTm n) : Γ ⊢[PRAAx] nonnegativeRows (rowF G body) p N (data N x) := by
  refine .allI (.impI ?_)
  let K := Syn.shift N
  let y := Syn.shift x
  let i : PTm (n+1) := var 0
  let Δ := lt i K :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt i K := Prf.hyp0
  simpa [nonnegativeRows,Syn.shift,Δ,K,y,i] using
    GaussianRationalNonnegativeProducts.congr (row_at (Syn.shift p) K y i hi).eqSymm
      (GaussianGammaGaussPositiveReferenceRows.sample_nonnegative (Syn.shift p) (succ i) (succ K)
        (zero_lt_succ i) (le_trans hi (le_succ_self K)))

theorem nonnegative_at (p N x : PTm n) : Γ ⊢[PRAAx] nonnegative (ap2 nameF p (nameData N x)) := by
  let t := clock N (radius G body N (data N x)) one p
  exact GaussianRationalNonnegativeProducts.congr
    (GaussianNamedFiniteProductName.name_at (rowF G body) p N (radius G body N (data N x)) one (data N x)).eqSymm
    (GaussianRationalNonnegativeProducts.sample_nonnegative (rowF G body) t N (data N x) (nonnegative_rows t N x))

private theorem lower_rows (N x : PTm n) : Γ ⊢[PRAAx] rowLower (rowF G body) N lowerDen (data N x) := by
  refine .allI (.allI (.impI ?_))
  let sh := fun t : PTm n => Syn.shift (Syn.shift t)
  let K := sh N
  let y := sh x
  let p : PTm (n+2) := var 1
  let i : PTm (n+2) := var 0
  let Δ := lt i K :: (Γ.map Fm.shift).map Fm.shift
  have hi : Δ ⊢[PRAAx] lt i K := Prf.hyp0
  simpa [rowLower,rowLowerAt,Syn.shift,sh,Δ,K,y,i,p,lowerDen,two] using
    lower_congr (row_at p K y i hi).eqSymm (.eqRefl _)
      (GaussianGammaGaussPositiveReferenceRows.sample_lower p (succ i) (succ K) (zero_lt_succ i)
        (le_trans hi (le_succ_self K)))

theorem lower_at (p N x : PTm n) :
    Γ ⊢[PRAAx] lower (ap2 nameF p (nameData N x)) (lowerDenominator N) :=
  GaussianNamedFiniteProductApartness.name_lower (rowF G body) p N (radius G body N (data N x)) one lowerDen (data N x)
    denominator_positive (lower_rows N x)

def positiveObservations (N x : PTm n) : Fm PTm n := .all
  (nonnegative (ap2 nameF (var 0) (Syn.shift (nameData N x))) ⋏
    lower (ap2 nameF (var 0) (Syn.shift (nameData N x))) (Syn.shift (lowerDenominator N)))

theorem positive_observations (N x : PTm n) : Γ ⊢[PRAAx] positiveObservations N x := by
  refine .allI ?_
  simpa [positiveObservations,Fm.shift,Syn.shift] using
    Prf.andI (nonnegative_at (Γ := Γ.map Fm.shift) (var 0) (Syn.shift N) (Syn.shift x))
      (lower_at (Γ := Γ.map Fm.shift) (var 0) (Syn.shift N) (Syn.shift x))

def squareF : PR 2 := multiplyF nameF nameF
def squareData (N x : PTm n) : PTm n := multiplyData nameF nameF (nameData N x) (nameData N x)

theorem square_normalization (N x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent squareF normalizationF (squareData N x) (normalizationData N x) := by
  let X := nameData N x
  let Y := GaussianGammaGaussReferenceProduct.data (succ N)
  have h := cross_symm _ _ _ _ (original_cross (Γ := Γ) N x)
  have hp := name_regular (Γ := Γ) N x
  have hr := GaussianGammaGaussReferenceProduct.name_regular (Γ := Γ) (succ N)
  have hs : Γ ⊢[PRAAx] crossEquivalent squareF referenceSquareF (squareData N x) (referenceSquareData N) :=
    GaussianGammaAdjacentCutoff.multiply_cross nameF R nameF R X Y X Y hp hr hp hr h h
  exact cross_trans _ _ _ _ _ _ hs (actual_square_normalization N x)

def rootCertificate (N x : PTm n) : Fm PTm n :=
  pointCN nameF (nameData N x) ⋏
    (positiveObservations N x ⋏
      (crossEquivalent R nameF (GaussianGammaGaussReferenceProduct.data (succ N)) (nameData N x) ⋏
        crossEquivalent squareF normalizationF (squareData N x) (normalizationData N x)))

theorem positive_root (N x : PTm n) : Γ ⊢[PRAAx] rootCertificate N x :=
  .andI (name_regular N x) (.andI (positive_observations N x)
    (.andI (original_cross N x) (square_normalization N x)))

theorem actual_Gauss_reference_positive_root_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (rootCertificate (var 1) (var 0)) :=
  closeUniv 2 (positive_root _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaGaussPositiveReference
