import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGaussEulerFiniteIdentity
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianGaussPiPowerSquareRoot

/-!
# Gauss multiplication with the two separate half powers

The positive square root of the named integer power of twice pi
provides the first factor independently of the Gamma names. The
second factor is the exponential of (1/2−mz) times the real log of m.
The original cleared Gauss limit agrees with their product times
the original Gamma at mz.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationHalfPowers

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaGaussShiftedProduct (source)
open GaussianGammaReciprocalInverse (gammaF named_product_exchange)
open GaussianGaussEulerFiniteIdentity (cleared_Gauss_multiplication)
open GaussianGaussMultiplicationCofinalProducts (leftF leftData innerF innerData rightF rightData referenceF referenceData)
open GaussianGaussMultiplicationCofinalRows (limit_power_regular scaled_regular scaledData)
open GaussianGaussMultiplicationHalfPower (halfData half_regular ratioPowerF ratio_power_regular regroupedCoefficient
  regroupedData regroup)
open GaussianGaussMultiplicationPowerRate (powerF)
open GaussianGaussMultiplicationPowerPerturbation (limitData)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_symm)
open GaussianNameRingLaws (multiply_associative multiply_commutative)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "PiHalf" => GaussianGaussPiPowerSquareRoot.nameF
local notation "Half" => GaussianGaussMultiplicationHalfPower.halfF

abbrev coefficientF : PR 2 := multiplyF PiHalf ratioPowerF
abbrev normalizedF : PR 2 := multiplyF coefficientF gammaF
def coefficientData (z B N x : PTm n) : PTm n :=
  multiplyData PiHalf ratioPowerF (GaussianGaussPiPowerSquareRoot.nameData N x) (regroupedData z B (succ N))
def normalizedData (z R B N d x : PTm n) : PTm n :=
  multiplyData coefficientF gammaF (coefficientData z B N x) (scaledData z R B (succ N) d)

theorem normalized_right (z R B N a d x : PTm n) (hs : Γ ⊢[PRAAx] source z R B (succ N) a d) :
    Γ ⊢[PRAAx] crossEquivalent rightF normalizedF (rightData z R B (succ N) d) (normalizedData z R B N d x) := by
  let m := succ N
  let P := limitData z R B m
  let G := scaledData z R B m d
  let C := referenceData m
  let Y := GaussianGaussPiPowerSquareRoot.nameData N x
  let H := halfData m
  let Q := regroupedData z B m
  have hm := hs.andE₁.andE₁
  have hB := hs.andE₂.andE₁.andE₂.andE₁
  have hP := limit_power_regular z R B m a d hs
  have hG := scaled_regular z R B m a d hs
  have hC := GaussianGammaGaussReferenceProduct.name_regular (Γ := Γ) m
  have hY := GaussianGaussPiPowerSquareRoot.name_regular (Γ := Γ) N x
  have hH := half_regular m hm
  have hQ := ratio_power_regular (regroupedCoefficient z B m) m hm
  have hI := multiply_fast powerF gammaF P G hP hG
  have ref := cross_trans _ _ _ _ _ _
    (cross_symm _ _ _ _ (GaussianGaussPiPowerSquareRoot.reference_cross (Γ := Γ) N x))
    (multiply_commutative PiHalf Half Y H hY hH)
  have expanded := multiply_cross innerF innerF referenceF (multiplyF Half PiHalf)
    (innerData z R B m d) (innerData z R B m d) C (multiplyData Half PiHalf H Y)
    hI hI hC (multiply_fast _ _ _ _ hH hY) (cross_refl _ _ hI) ref
  have grouped := named_product_exchange powerF gammaF Half PiHalf P G H Y hP hG hH hY
  have exponents := regroup z R B m hm hB hs.andE₁.andE₂
  have factors := multiply_cross (multiplyF powerF Half) ratioPowerF (multiplyF gammaF PiHalf) (multiplyF PiHalf gammaF)
    (multiplyData powerF Half P H) Q (multiplyData gammaF PiHalf G Y) (multiplyData PiHalf gammaF Y G)
    (multiply_fast _ _ _ _ hP hH) hQ (multiply_fast _ _ _ _ hG hY) (multiply_fast _ _ _ _ hY hG) exponents
    (multiply_commutative gammaF PiHalf G Y hG hY)
  have assoc := cross_symm _ _ _ _ (multiply_associative ratioPowerF PiHalf gammaF Q Y G hQ hY hG)
  have ordered := multiply_cross (multiplyF ratioPowerF PiHalf) coefficientF gammaF gammaF
    (multiplyData ratioPowerF PiHalf Q Y) (coefficientData z B N x) G G
    (multiply_fast _ _ _ _ hQ hY) (multiply_fast _ _ _ _ hY hQ) hG hG
    (multiply_commutative ratioPowerF PiHalf Q Y hQ hY) (cross_refl _ _ hG)
  exact cross_trans _ _ _ _ _ _ expanded (cross_trans _ _ _ _ _ _ grouped
    (cross_trans _ _ _ _ _ _ factors (cross_trans _ _ _ _ _ _ assoc ordered)))

theorem normalized_multiplication (z R B N a d x : PTm n) (hs : Γ ⊢[PRAAx] source z R B (succ N) a d) :
    Γ ⊢[PRAAx] crossEquivalent leftF normalizedF (leftData z R B (succ N) d) (normalizedData z R B N d x) :=
  cross_trans _ _ _ _ _ _ (cleared_Gauss_multiplication z R B (succ N) a d hs) (normalized_right z R B N a d x hs)

theorem actual_Gauss_multiplication_separate_half_powers_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 0) (var 1) (var 2) (succ (var 3)) (var 4) (var 5) ⟶ crossEquivalent leftF normalizedF
      (leftData (var 0) (var 1) (var 2) (succ (var 3)) (var 5))
      (normalizedData (var 0) (var 1) (var 2) (var 3) (var 5) (var 6))) :=
  closeUniv 7 (.impI (normalized_multiplication _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationHalfPowers
