import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianLogGammaEulerCommonDenominator
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianLogGammaEulerRationalContinuity
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianLogGammaEulerRescale

/-!
# Independence of the signed-rational log-Gamma chart

Equal input codes give equal native Gaussian values after clearing the two
denominators. The existing rescaling theorem and the zero-displacement
case of the local log-Gamma continuity theorem identify their cofinal names.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerChartAgreement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale normSq_zero zeroCode)
open GaussianLogGammaEulerCofinal (canonicalData)
open GaussianLogGammaEulerCommonDenominator (native_scaled)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner
  (canonical_unique ofGaussian_canonical ofGaussian_represents positive_product represents_congr represents_rescale)
open GaussianRootAlgebra (equal equal_of_values equal_symm equal_trans normSq_equal sub re_sub im_sub re_zero im_zero)
open GaussianRightHalfPlaneLogarithm (source)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianLogGammaEulerCofinal.nameF

theorem scaled_argument (A B D neg k E : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hk : Γ ⊢[PRAAx] le one k) (he : Γ ⊢[PRAAx] k*D ≐ E) :
    Γ ⊢[PRAAx] argument (k*A) (k*B) E neg ≐ argument A B D neg := by
  let z := native A B neg
  let v := native (k*A) (k*B) neg
  let x := argument A B D neg
  let y := argument (k*A) (k*B) E neg
  have hd : Γ ⊢[PRAAx] le one E := le_congr (.eqRefl _) he (positive_product k D hk h.andE₂)
  have ev : Γ ⊢[PRAAx] equal v (scale k z) := native_scaled k A B neg h.andE₁.andE₂
  have rep := represents_congr (.eqRefl x) (equal_symm ev) ((by ipra_ring : Γ ⊢[PRAAx] D*k ≐ k*D).eqTrans he)
    (represents_rescale x z D k (ofGaussian_represents z D h.andE₂))
  exact canonical_unique y x v E (ofGaussian_canonical v E hd) (ofGaussian_canonical z D h.andE₂) hd
    (ofGaussian_represents v E hd) rep

private theorem zero_rate_agreement (f g : PR 2) (x y C D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] independentRate f g x y (C*zero) D) : Γ ⊢[PRAAx] crossEquivalent f g x y := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let s (v : PTm n) := Syn.shift (Syn.shift v)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have hs : Δ ⊢[PRAAx] independentRate f g (s x) (s y) (s C*zero) (s D) := by
    simpa [Δ,s,Fm.shift,Syn.shift] using h.shift.shift
  have hd : Δ ⊢[PRAAx] le one (s D) := by simpa [Δ,s,Fm.shift,Syn.shift] using hD.shift.shift
  have hpq := positive_product _ _ (GaussianCoefficientNameBounds.unit_positive (Γ := Δ) p)
    (GaussianCoefficientNameBounds.unit_positive (Γ := Δ) q)
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive (s D) p q hd) hpq
    (le_of_eq_add (d := zero) (by unfold rateNumerator rateDenominator; ipra_ring))
    (rate_at f g (s x) (s y) (s C*zero) (s D) p q hs)

private theorem le_mul_of_positive (x D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] le x (D*x) :=
  le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right x hD)

theorem common_denominator_agreement (A B neg a b sign D : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (h' : Γ ⊢[PRAAx] source a D sign)
    (e : Γ ⊢[PRAAx] equal (native A B neg) (native a b sign)) :
    Γ ⊢[PRAAx] crossEquivalent F F (canonicalData A B D neg) (canonicalData a b D sign) := by
  let C := A+B+a+b
  have delta : Γ ⊢[PRAAx] equal (sub (native a b sign) (native A B neg)) zeroCode := by
    apply equal_of_values
    · simp only [re_sub, re_zero, ZT.toZ_eq e.andE₁, sub_self]
    · simp only [im_sub, im_zero, ZT.toZ_eq e.andE₂, sub_self]
  have bounded : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (sub (native a b sign) (native A B neg)) zero :=
    le_congr ((normSq_equal delta).eqTrans normSq_zero).eqSymm (by ipra_ring) (le_refl zero)
  have left : Γ ⊢[PRAAx] le D (D*A) :=
    le_congr (.eqRefl _) (by ipra_ring) (le_mul_of_positive D A h.andE₁.andE₁)
  have right : Γ ⊢[PRAAx] le D (D*a) :=
    le_congr (.eqRefl _) (by ipra_ring) (le_mul_of_positive D a h'.andE₁.andE₁)
  have size : Γ ⊢[PRAAx] le (A+B+a+b) (C*D) :=
    le_congr (.eqRefl _) (by dsimp only [C]; ipra_ring) (le_mul_of_positive (A+B+a+b) D h.andE₂)
  have small : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithmIncrementMargin.smallStep zero D C D :=
    le_congr (by ipra_ring) (.eqRefl _) (zero_le D)
  have src : Γ ⊢[PRAAx] GaussianLogGammaEulerTaylorUniform.source A B neg a b sign D zero D C :=
    .andI h (.andI h' (.andI bounded (.andI h.andE₂ (.andI left (.andI right (.andI size small))))))
  have rate := GaussianLogGammaEulerRationalContinuity.independent_rate A B neg a b sign D zero D C src
  exact cross_symm F F _ _ (zero_rate_agreement F F _ _ (GaussianLogGammaEulerRationalContinuity.response D C) D h.andE₂ rate)

theorem canonical_agreement (A B D neg a b d sign : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (h' : Γ ⊢[PRAAx] source a d sign)
    (e : Γ ⊢[PRAAx] argument A B D neg ≐ argument a b d sign) :
    Γ ⊢[PRAAx] crossEquivalent F F (canonicalData A B D neg) (canonicalData a b d sign) := by
  let E := d*D
  let z := native A B neg
  let w := native a b sign
  let x := canonicalData A B D neg
  let y := canonicalData a b d sign
  let u := canonicalData (d*A) (d*B) E neg
  let v := canonicalData (D*a) (D*b) E sign
  have hE := positive_product d D h'.andE₂ h.andE₂
  have he : Γ ⊢[PRAAx] D*d ≐ E := by dsimp only [E]; ipra_ring
  have left := GaussianLogGammaEulerRescale.canonical_rescale A B D neg d E h h'.andE₂ (.eqRefl E)
    (scaled_argument A B D neg d E h h'.andE₂ (.eqRefl E))
  have right := GaussianLogGammaEulerRescale.canonical_rescale a b d sign D E h' h.andE₂ he
    (scaled_argument a b d sign D E h' h.andE₂ he)
  have repLeft := ofGaussian_represents z D h.andE₂
  have repRight := represents_congr e.eqSymm (GaussianRootAlgebra.equal_refl w) (.eqRefl d) (ofGaussian_represents w d h'.andE₂)
  have scaled := GaussianDominantPairAlgebra.represents_cross (argument A B D neg) z w D d repLeft repRight
  have ev := equal_trans (native_scaled d A B neg h.andE₁.andE₂)
    (equal_trans scaled (equal_symm (native_scaled D a b sign h'.andE₁.andE₂)))
  have su : Γ ⊢[PRAAx] source (d*A) E neg :=
    .andI (.andI (positive_product d A h'.andE₂ h.andE₁.andE₁) h.andE₁.andE₂) hE
  have sv : Γ ⊢[PRAAx] source (D*a) E sign :=
    .andI (.andI (positive_product D a h.andE₂ h'.andE₁.andE₁) h'.andE₁.andE₂) hE
  have middle := common_denominator_agreement (d*A) (d*B) neg (D*a) (D*b) sign E su sv ev
  exact cross_trans F F F x v y (cross_trans F F F x u v (cross_symm F F u x left) middle) right

theorem actual_canonical_log_Gamma_chart_agreement_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (source (var 0) (var 2) (var 3) ⟶ source (var 4) (var 6) (var 7) ⟶
        argument (var 0) (var 1) (var 2) (var 3) ≐ argument (var 4) (var 5) (var 6) (var 7) ⟶
        crossEquivalent F F (canonicalData (var 0) (var 1) (var 2) (var 3))
          (canonicalData (var 4) (var 5) (var 6) (var 7))) :=
  closeUniv 8 (.impI (.impI (.impI (canonical_agreement _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerChartAgreement
