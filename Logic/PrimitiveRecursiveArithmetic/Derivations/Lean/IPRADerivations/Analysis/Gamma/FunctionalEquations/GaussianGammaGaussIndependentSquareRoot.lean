import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaGaussPositiveReference
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianNamedBoundedSquareRoot

/-!
# Independent computation of the Gauss reference square root

The sampler reads the actual doubled π family power and the literal
reciprocal of the modulus. Its program does not read Gamma. The certified
positive real Gamma product supplies the accuracy proof.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianGammaGaussIndependentSquareRoot

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaGaussReferenceSquare (doubledPiBody doubledPiPowerF doubledPiPowerData normalizationF normalizationData)
open GaussianGammaGaussReflectionFamily (piBody)
open GaussianGammaGaussReflectionPowerConstant (twoBody reciprocalModulus)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianCyclicSineProductSquare (data)
open GaussianRationalNonnegativeFractions (fraction_nonnegative multiply_nonnegative_at)
open GaussianRationalNonnegativeProducts (nonnegative nonnegativeRows)
open GaussianNamedFiniteProductFamily (rowF radius)
open GaussianNamedFiniteProductName (clock)
open GaussianNamedBoundedSquareRoot (observations sqrtF square_root_cross)
open GaussianRationalHorner (canonical canonical_congr ofGaussian_canonical ofGaussian_represents)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianNameArithmetic (multiplyF multiplyModulus multiply_canonical)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalNaturalScale (naturalPoint)
open ComplexLogarithmRemainder (scale oneCode)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianGammaHalfPiName.nameF
local notation "C" => constantF
local notation "F" => multiplyF P C

private theorem pi_nonnegative (p x : PTm n) : Γ ⊢[PRAAx] nonnegative (ap2 P p x) :=
  GaussianRationalNonnegativeProducts.congr (GaussianGammaHalfPiName.sample_at p x).eqSymm
    (fraction_nonnegative _ _ (GaussianGammaHalfRisingFactorial.factorial_positive _))

private theorem doubled_row (p i N x : PTm n) :
    Γ ⊢[PRAAx] nonnegative (ap3 (rowF F doubledPiBody) p i (data N x)) := by
  let a := inst2 piBody i (data N x)
  let b := inst2 twoBody i (data N x)
  let s := GaussianFastValueCut.exponent (multiplyModulus P C a b) p
  have hb : b = naturalPoint two := by simp [b,twoBody,inst2,two,one]
  have c : Γ ⊢[PRAAx] nonnegative (ap2 C s b) :=
    GaussianRationalNonnegativeProducts.congr (constant_at s b).eqSymm
      (by rw [hb]; exact fraction_nonnegative two one (le_refl one))
  have bind := GaussianNamedFiniteProductFamily.row_at (Γ := Γ) F doubledPiBody p i (data N x)
  rw [doubledPiBody, GaussianNamedFiniteProductFamilyAlgebra.body_at] at bind
  exact GaussianRationalNonnegativeProducts.congr bind.eqSymm
    (multiply_nonnegative_at P C a b p (pi_nonnegative s a) c)

private theorem doubled_rows (p N x : PTm n) :
    Γ ⊢[PRAAx] nonnegativeRows (rowF F doubledPiBody) p N (data N x) := by
  refine .allI (.impI ?_)
  let K := Syn.shift N
  let i : PTm (n+1) := var 0
  let Δ := lt i K :: Γ.map Fm.shift
  simpa [nonnegativeRows,Syn.shift,K,i,Δ] using doubled_row (Γ := Δ) (Syn.shift p) i K (Syn.shift x)

theorem doubled_power_nonnegative (p N x : PTm n) :
    Γ ⊢[PRAAx] nonnegative (ap2 doubledPiPowerF p (doubledPiPowerData N x)) := by
  let f := rowF F doubledPiBody
  let R := radius F doubledPiBody N (data N x)
  let t := clock N R one p
  exact GaussianRationalNonnegativeProducts.congr
    (GaussianNamedFiniteProductName.name_at f p N R one (data N x)).eqSymm
    (GaussianRationalNonnegativeProducts.sample_nonnegative f t N (data N x) (doubled_rows t N x))

theorem reciprocal_fraction (N : PTm n) : Γ ⊢[PRAAx] fraction one (succ N) ≐ reciprocalModulus N := by
  let m := succ N
  have hm := zero_lt_succ (Γ := Γ) N
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (scale one oneCode) oneCode := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,ZT.toZ_ofNat]
  exact GaussianRationalHorner.canonical_unique _ _ _ m (ofGaussian_canonical _ _ hm) (ofGaussian_canonical _ _ hm) hm
    (GaussianRationalHorner.represents_congr (.eqRefl _) e (.eqRefl _) (ofGaussian_represents _ _ hm))
    (ofGaussian_represents _ _ hm)

private theorem reciprocal_nonnegative (N : PTm n) : Γ ⊢[PRAAx] nonnegative (reciprocalModulus N) :=
  GaussianRationalNonnegativeProducts.congr (reciprocal_fraction N) (fraction_nonnegative one (succ N) (zero_lt_succ N))

theorem normalization_observation (p N x : PTm n) : Γ ⊢[PRAAx]
    canonical (ap2 normalizationF p (normalizationData N x)) ⋏
      nonnegative (ap2 normalizationF p (normalizationData N x)) := by
  let a := doubledPiPowerData N x
  let b := reciprocalModulus N
  let s := GaussianFastValueCut.exponent (multiplyModulus doubledPiPowerF C a b) p
  exact .andI (multiply_canonical doubledPiPowerF C a b p) (multiply_nonnegative_at doubledPiPowerF C a b p
    (doubled_power_nonnegative s N x)
    (GaussianRationalNonnegativeProducts.congr (constant_at s b).eqSymm (reciprocal_nonnegative N)))

private theorem shift_normalizationData (N x : PTm n) :
    Syn.shift (normalizationData N x) = normalizationData (Syn.shift N) (Syn.shift x) := by
  simp [normalizationData,doubledPiPowerData,GaussianNamedFiniteProductFamily.productData,reciprocalModulus,
    ComplexLogarithmRemainder.oneCode,ComplexLogarithmRemainder.code,ZT.ofNat,one,Syn.shift]

theorem normalization_observations (N x : PTm n) : Γ ⊢[PRAAx] observations normalizationF (normalizationData N x) := by
  refine .allI ?_
  rw [shift_normalizationData]
  exact normalization_observation (var 0) (Syn.shift N) (Syn.shift x)

private theorem positive_canonical (p N x : PTm n) : Γ ⊢[PRAAx]
    canonical (ap2 GaussianGammaGaussPositiveReference.nameF p (GaussianGammaGaussPositiveReference.nameData N x)) := by
  let f := GaussianGammaGaussPositiveReferenceRows.nameF
  let t := GaussianGammaGaussPositiveReference.body
  let g := rowF f t
  let R := radius f t N (data N x)
  exact canonical_congr (GaussianNamedFiniteProductName.name_at g p N R one (data N x))
    (GaussianNamedFiniteProduct.sample_canonical g (clock N R one p) N (data N x))

theorem positive_reference_observations (N x : PTm n) : Γ ⊢[PRAAx]
    observations GaussianGammaGaussPositiveReference.nameF (GaussianGammaGaussPositiveReference.nameData N x) := by
  refine .allI ?_
  simpa [Syn.shift] using
    Prf.andI (positive_canonical (Γ := Γ.map Fm.shift) (var 0) (Syn.shift N) (Syn.shift x))
      (GaussianGammaGaussPositiveReference.nonnegative_at (Γ := Γ.map Fm.shift) (var 0) (Syn.shift N) (Syn.shift x))

def nameF : PR 2 := sqrtF normalizationF
def nameData (N x : PTm n) : PTm n := normalizationData N x

theorem positive_reference_cross (N x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent GaussianGammaGaussPositiveReference.nameF nameF
      (GaussianGammaGaussPositiveReference.nameData N x) (nameData N x) :=
  square_root_cross _ _ _ _ (GaussianGammaGaussPositiveReference.name_regular N x)
    (positive_reference_observations N x) (normalization_observations N x)
    (GaussianGammaGaussPositiveReference.square_normalization N x)

theorem original_reference_cross (N x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent GaussianGammaGaussReferenceProduct.nameF nameF
      (GaussianGammaGaussReferenceProduct.data (succ N)) (nameData N x) :=
  cross_trans _ _ _ _ _ _ (GaussianGammaGaussPositiveReference.original_cross N x) (positive_reference_cross N x)

theorem actual_Gauss_independent_square_root_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (crossEquivalent GaussianGammaGaussReferenceProduct.nameF nameF
        (GaussianGammaGaussReferenceProduct.data (succ (var 1))) (nameData (var 1) (var 0))) :=
  closeUniv 2 (original_reference_cross _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaGaussIndependentSquareRoot
