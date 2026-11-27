import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceIntegrand
import IPRADerivations.Analysis.Euler.Integration.Decay.Quadrature.GaussianEulerDecayQuadraturePrecision
import IPRADerivations.Analysis.Euler.VerticalBounds.GaussianEulerVerticalIntegrandSquare

/-!
# Real decay of the actual Binet Laplace exponential

At encoded time `A/B`, the signed complex exponent has the same real
coordinate as the original decay exponent at `(X*A)/(D*B)`. The original
squared modulus identity then compares the actual complex and real decay
observations at independently requested precisions.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceDecay

open_ipra
open ComplexLogarithmRemainder (scale oneCode eval_re_code)
open GaussianBinetLaplaceExponential (exponent exponent_bound)
open GaussianCoefficientNameBounds (unit)
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianExponentialRealPart (squareF squareData)
open GaussianExponentialRealPartMajorant (doubleScalar expData squared_exponential_real)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner
  (positive_product ofGaussian_represents qmul_represents qmul_canonical scalar_congr scalar_same_value)
open GaussianRationalMetric (qnegative_represents qnegative_canonical bounded)
open GaussianRealExponentialPositiveRepresentative (originalData)
open RationalNormalForm (well_formed_unique)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianBinetLaplaceExponential.nameF
local notation "input" => GaussianBinetLaplaceIntegrand.input
local notation "laplaceData" => GaussianBinetLaplaceExponential.data

theorem exponent_real_coordinate (X Y D sign A B : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    fstT (exponent X Y D sign A B) ≐ fstT (decayPoint (X*A) (D*B)) := by
  let z := argument X Y D sign
  let x := native X Y sign
  let w := fraction A B
  let t := scale A oneCode
  let nx := ComplexLogarithmRemainder.neg x
  let q := exponent X Y D sign A B
  let r := decayPoint (X*A) (D*B)
  let u := -ZT.ofNat (X*A)
  have hv := positive_product _ _ hD hB
  have qrep := qmul_represents _ w nx t D B hD hB
    (qnegative_represents z x D (ofGaussian_represents x D hD)) (ofGaussian_represents t B hB)
  have realq : Γ ⊢[PRAAx] ZT.eq (ComplexLogarithmRemainder.re (ComplexLogarithmRemainder.mul nx t)) u := by
    apply ZT.derive
    simp only [nx,x,t,native,u,GaussianRootAlgebra.re_mul,GaussianRootAlgebra.re_neg,
      GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,
      GaussianRootAlgebra.im_one,eval_re_code,ZT.toZ_ofNat,ZT.toZ_neg]
    ipra_simps
    ring
  have rr := qnegative_represents (fraction (X*A) (D*B)) (scale (X*A) oneCode) (D*B)
    (ofGaussian_represents _ _ hv)
  have realr : Γ ⊢[PRAAx] ZT.eq (ComplexLogarithmRemainder.re (ComplexLogarithmRemainder.neg (scale (X*A) oneCode))) u := by
    apply ZT.derive
    simp only [u, GaussianRootAlgebra.re_neg, GaussianRootAlgebra.re_scale, GaussianRootAlgebra.re_one]
    ipra_simps
    ring
  have sq := scalar_congr (.eqRefl (fstT q)) realq (.eqRefl _) qrep.andE₁
  have sr := scalar_congr (.eqRefl (fstT r)) realr (.eqRefl _) rr.andE₁
  exact well_formed_unique _ _ (qmul_canonical _ _).andE₂.andE₁ (qnegative_canonical _).andE₂.andE₁
    (scalar_same_value _ _ u (D*B) hv sq sr)

private theorem original_data_congr {a b : PTm n} (e : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] originalData a ≐ originalData b := by
  simpa only [originalData,exponentialInputData,GaussianRadiusExponentialName.subst_data,
    GaussianNameBounds.subst_U,RationalGaussianEmbedding.subst_embed,Syn.subst_var,Matrix.cons_val_zero] using
    (Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (originalData (var 0) : PTm 1)
      (σ := ![a]) (σ' := ![b]) (fun i => by fin_cases i; exact e))

theorem square_matches_real_decay (X Y D sign R T A B : PTm n) (h : Γ ⊢[PRAAx] input X Y D sign R T A B) :
    Γ ⊢[PRAAx] crossEquivalent (squareF F) (squareF decayF)
      (squareData F (laplaceData X Y D sign R T A B)) (squareData decayF (decayData (X*A) (D*B))) := by
  let q := exponent X Y D sign A B
  let r := decayPoint (X*A) (D*B)
  let u := laplaceData X Y D sign R T A B
  let v := expData q
  let S := R*T
  let K := GaussianNameBounds.U constantF q
  let w := originalData (doubleScalar q)
  let w' := originalData (doubleScalar r)
  have hb := h.andE₂.andE₁
  have hd := h.andE₁.andE₁.andE₂
  have reg := GaussianBinetLaplaceExponential.regular X Y D sign R T A B h.andE₁ hb h.andE₂.andE₂
  have actual := GaussianSignedNameExponentialOrder.constant_input _ _
    (exponent_bound X Y D sign R T A B h.andE₁ hb h.andE₂.andE₂)
  have canonical := exponential_input (Γ := Γ) constantF q (constant_regular _)
  have equal := GaussianExponentialRadiusIndependence.same_input_cross constantF S K q actual canonical
  have squares := GaussianEulerVerticalIntegrandSquare.square_equivalent F F u v reg
    (GaussianRadiusExponentialName.name_regular _ _ _ canonical) equal
  have coord := exponent_real_coordinate X Y D sign A B hd hb
  have names := original_data_congr (RationalAlgebra.add_congr coord coord)
  have projected := GaussianGammaCompactCutoffAlignment.cross_data_congr (squareF F) decayF (squareData F v) (squareData F v) w w'
    (.eqRefl _) names (squared_exponential_real q)
  exact cross_trans _ _ _ _ _ _ squares
    (cross_trans _ _ _ _ _ _ projected (cross_symm _ _ _ _ (squared_exponential_real r)))

/-- Retain an arbitrary checked radius of the original real decay sample.
The sole extra error for the actual complex sample is `2/2^p`. -/
theorem observation_bound (p X Y D sign R T A B U V : PTm n)
    (h : Γ ⊢[PRAAx] input X Y D sign R T A B) (hV : Γ ⊢[PRAAx] le one V)
    (hr : Γ ⊢[PRAAx] bounded (ap2 decayF p (decayData (X*A) (D*B))) U V) :
    Γ ⊢[PRAAx] bounded (ap2 F p (laplaceData X Y D sign R T A B)) (U*unit p+two*V) (V*unit p) :=
  GaussianEulerVerticalNormTransfer.original_norm_transfer F decayF _ _ p U V hV
    (GaussianBinetLaplaceExponential.regular X Y D sign R T A B h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂)
    (GaussianEulerDecayQuadraturePrecision.observation_regular (X*A) (D*B))
    (square_matches_real_decay X Y D sign R T A B h) hr

theorem actual_Binet_Laplace_exponential_decay_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (input (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      le one (var 10) ⟶ bounded (ap2 decayF (var 0) (decayData (var 1*var 7) (var 3*var 8))) (var 9) (var 10) ⟶
      bounded (ap2 F (var 0) (laplaceData (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
        (var 9*unit (var 0)+two*var 10) (var 10*unit (var 0))) :=
  closeUniv 11 (.impI (.impI (.impI (observation_bound _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceDecay
