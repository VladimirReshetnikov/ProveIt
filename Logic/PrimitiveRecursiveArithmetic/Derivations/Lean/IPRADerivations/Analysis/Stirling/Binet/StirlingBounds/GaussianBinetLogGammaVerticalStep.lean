import IPRADerivations.Analysis.Stirling.Binet.StirlingBounds.GaussianBinetStirlingVerticalAlgebra
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Derivatives.GaussianLogGammaEulerTaylorCofinal

/-!
# Vertical log-Gamma increment with the literal C27 linear term

Specialize the cofinal Taylor bound to the exact signed vertical
displacement. The linear term reads the original C27 digamma at the
same observation clock. A separate dyadic allowance pays for replacing
the normalized weighted slope and its cofinal Euler representation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetLogGammaVerticalStep

open_ipra
open ComplexLogarithmRemainder (normSq)
open GaussianBinetLogVerticalStep (step native_step_bound)
open GaussianBinetStirlingVerticalAlgebra (displacement)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianLogGammaEulerCofinal (canonicalData)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianLogGammaEulerResidualRadius (native_norm)
open GaussianLogGammaEulerTaylorRows (coefficient errorDenominator)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus)
open GaussianNameEquivalence (cross_at)
open GaussianNameRingLaws (multiply_sample_error)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (ofGaussian_represents positive_product qmul)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded qsub)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRightHalfPlaneLogarithm (source)
open GaussianRightHalfPlaneLogarithmIncrementMargin (admitted smallStep)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => GaussianLogGammaEulerCofinal.nameF
local notation "S" => GaussianLogGammaEulerReciprocalSlopeCofinal.nameF
local notation "sd" => GaussianLogGammaEulerReciprocalSlopeCofinal.canonicalData
local notation "P" => GaussianLogGammaEulerDigammaFractionsCofinal.nameF
local notation "pd" => GaussianLogGammaEulerDigammaFractionsCofinal.data

theorem step_bound (D sign H : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hs : Γ ⊢[PRAAx] (sign ≐ zero) ⋎ (sign ≐ one)) : Γ ⊢[PRAAx] bounded (step H D sign) H D := by
  let z := native zero H sign
  have e : Γ ⊢[PRAAx] normSq z ≐ H*H :=
    (native_norm zero H sign hs).eqTrans (by ipra_ring)
  exact bounded_of_cleared _ z D H D hD hD (ofGaussian_represents z D hD)
    (le_congr (congrMul (.eqRefl _) e.eqSymm) (.eqRefl _) (by ipra_le 0))

theorem scaled_distance (w a b W C A B : PTm n)
    (hC : Γ ⊢[PRAAx] le one C) (hB : Γ ⊢[PRAAx] le one B)
    (hw : Γ ⊢[PRAAx] bounded w W C) (hr : Γ ⊢[PRAAx] distanceBounded a b A B) :
    Γ ⊢[PRAAx] distanceBounded (qmul w a) (qmul w b) (W*A) (C*B) :=
  bound_congr (GaussianPolynomialCoefficientDifferences.scalar_scaled_difference w a b).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_product w (qsub a b) W C A B hC hB hw hr)

def dyadicCost (A B D sign H : PTm n) : PTm n :=
  (H+num 37)+(multiplyModulus constantF S (step H D sign) (sd A B D sign)+one)+two*H

theorem sample_error (p A B D sign H K C : PTm n)
    (h : Γ ⊢[PRAAx] source A D sign) (hK : Γ ⊢[PRAAx] le one K) (hm : Γ ⊢[PRAAx] le D (K*A))
    (hsize : Γ ⊢[PRAAx] le (A+B+A+(B+H)) (C*D)) (hs : Γ ⊢[PRAAx] smallStep H K C D) :
    Γ ⊢[PRAAx] distanceBounded (qsub (ap2 G p (canonicalData A (B+H) D sign)) (ap2 G p (canonicalData A B D sign)))
      (qmul (step H D sign) (ap2 P p (pd A B D sign)))
      (coefficient H K*unit p+dyadicCost A B D sign H*(D*D)) (D*D*unit p) := by
  let e := step H D sign
  let old := GaussianLogGammaEulerArgumentIncrement.step A B sign A (B+H) sign D
  let x := sd A B D sign
  let y := pd A B D sign
  let t := ap2 (multiplyF constantF S) p (multiplyData constantF S old x)
  let v := qmul e (ap2 S p x)
  let w := qmul e (ap2 P p y)
  let U := unit p
  let E := D*D
  let Q := E*U
  let M := multiplyModulus constantF S e x+one
  have hu := unit_positive (Γ := Γ) p
  have hD := h.andE₂
  have hE := positive_product D D hD hD
  have hQ := positive_product E U hE hu
  have ha := admitted A B sign A (B+H) sign D H K C h h (native_step_bound A B sign H h.andE₁.andE₂)
    hK hm hm hsize hs
  have raw := GaussianLogGammaEulerTaylorCofinal.raw_cofinal_at p A B sign A (B+H) sign D H _ _ K ha hm
  have eold := displacement A B D sign H h
  have hx := GaussianLogGammaEulerReciprocalSlopeCofinal.canonical_regular A B D sign h
  have mp := multiply_sample_error constantF S old x p (constant_regular old) hx
  have em : Γ ⊢[PRAAx] multiplyModulus constantF S old x+one ≐ M := by
    have u : Γ ⊢[PRAAx] GaussianNameBounds.U constantF old ≐ GaussianNameBounds.U constantF e := by
      simpa only [GaussianNameBounds.subst_U, Syn.subst_var, Matrix.cons_val_zero] using
        Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (GaussianNameBounds.U constantF (var 0) : PTm 1) (σ := ![old]) (σ' := ![e])
          (fun i => by fin_cases i; exact eold)
    exact congrAdd (congrAdd u (.eqRefl _)) (.eqRefl one)
  have nerr : Γ ⊢[PRAAx] distanceBounded t v M U :=
    distance_congr (.eqRefl _) (qmul_congr ((constant_at p old).eqTrans eold) (.eqRefl _)) em (.eqRefl _) mp
  have second : Γ ⊢[PRAAx] distanceBounded t v (M*E) Q :=
    distance_radius_mono _ _ _ _ _ _ hu hQ (by dsimp only [Q]; ipra_le 0) nerr
  have close := cross_at S P x y p p (GaussianLogGammaEulerDigammaFractionsCofinal.cofinal_equivalent A B D sign h)
  have base : Γ ⊢[PRAAx] distanceBounded (ap2 S p x) (ap2 P p y) two U :=
    distance_radius_mono _ _ _ _ _ _ (positive_product U U hu hu) hu (by ipra_le 0) close
  have scaled := scaled_distance e _ _ H D two U hD hu (step_bound D sign H hD h.andE₁.andE₂) base
  have third : Γ ⊢[PRAAx] distanceBounded v w (two*H*E) Q :=
    distance_radius_mono _ _ _ _ _ _ (positive_product D U hD hu) hQ
      (by dsimp only [E,Q]; ipra_le Groth.ι (IPRA.Q.mk Γ (H*two*D*D*U))*sl hD) scaled
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [dyadicCost,M,E]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ v w _ _ Q hQ (distance_triangle_same _ t v _ _ Q hQ raw second) third)

end LeanProofs.IPRA.Analysis.GaussianBinetLogGammaVerticalStep
