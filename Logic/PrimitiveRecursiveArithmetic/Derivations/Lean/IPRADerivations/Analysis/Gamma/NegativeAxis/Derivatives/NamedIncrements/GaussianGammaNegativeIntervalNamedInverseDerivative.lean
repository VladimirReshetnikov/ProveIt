import IPRADerivations.Analysis.Gamma.NegativeAxis.Values.GaussianGammaNegativeIntervalNamedCorrectionFactor
import IPRADerivations.Analysis.Gamma.NegativeAxis.Values.GaussianGammaNegativeIntervalNamedInverseFactor
import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.NamedIncrements.GaussianGammaNegativeIntervalNamedInverseIncrementInput
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianNamedIncrementFrozenCoefficient
import IPRADerivations.Analysis.Names.Rates.Moduli.GaussianNamedLipschitzRate

/-!
# The finite inverse shift derivative for arbitrary named increments

The exact frozen coefficient is read from the quotient at an
independent observation clock. Its error relative to the derivative
coefficient is linear in the certified upper bound for the increment.
The apartness certificate is used only in the observation error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedInverseDerivative

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialSmallPerturbation (smallSamples)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianGammaNegativeIntervalCorrectionVariation (correctionCap factor_bound)
open GaussianGammaNegativeIntervalInverseRationalEnvelope (finiteCoefficient exact_difference window_envelope)
open GaussianGammaNegativeIntervalInverseRecurrence (inverse correctionFactor)
open GaussianGammaNegativeIntervalNamedInput (sampleNumerator sampleDenominator frozen_guard)
open GaussianGammaNegativeIntervalNamedInverseIncrementInput (approx_increment frozen_step_small increment)
open GaussianGammaNegativeProductDerivativeInverseRate (inverseRateCost)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedEulerUnitTime (source encoded_source)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "IF" => GaussianGammaNegativeIntervalNamedInverseFactor.nameF
local notation "id" => GaussianGammaNegativeIntervalNamedInverseFactor.data
local notation "CF" => GaussianGammaNegativeIntervalNamedCorrectionFactor.nameF
local notation "cd" => GaussianGammaNegativeIntervalNamedCorrectionFactor.data
local notation "QF" => GaussianNamedIncrementDifferenceQuotient.nameF
local notation "qd" => GaussianNamedIncrementDifferenceQuotient.data
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def input (f g K : PR 2) (p x y z E a : PTm n) : Fm PTm n :=
  source f x E ⋏ (source g y E ⋏ (GaussianNameReciprocal.input K a z ⋏
    (crossEquivalent (GaussianNamedDifference.nameF g f) K (GaussianNamedDifference.data y x) z ⋏
      smallSamples K z one (unit p))))

ipra_subst input

def gain (E N : PTm n) : PTm n := two*inverseRateCost (succ N) (E*E)

def coefficientBound (E N : PTm n) : PTm n := gain E N+(E*E)*correctionCap E N

def clock (p q E N : PTm n) : PTm n := p+num 3+q+
  GaussianGammaNegativeIntervalNamedInverseFactor.clock q E N+
  GaussianGammaNegativeIntervalNamedCorrectionFactor.clock q E N

def cost (f g K : PR 2) (x y z E N a : PTm n) : PTm n :=
  GaussianNamedIncrementFrozenCoefficient.cost (IF g) (IF f) K (id y E N) (id x E N) z a
    (coefficientBound E N)+num 3

private theorem read_constant (F : PR 2) (q x c : PTm n) (h : Γ ⊢[PRAAx] independentRate F constantF x c one (unit q)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F q x) c (num 3) (unit q) := by
  have hp := unit_positive (Γ := Γ) q
  have h0 := diagonal_rate F constantF x c one (unit q) q hp h
  have h1 := distance_radius_mono _ _ _ _ (num 3) (unit q) (positive_product _ _ hp hp) hp
    (le_of_eq_add (d := zero) (by ipra_ring)) h0
  exact distance_congr (.eqRefl _) (constant_at q c) (.eqRefl _) (.eqRefl _) h1

private theorem clock_growth (p q E N : PTm n) : Γ ⊢[PRAAx] le (num 8*unit p) (unit (clock p q E N)) := by
  have pow : Γ ⊢[PRAAx] pw two (num 3) ≐ num 8 :=
    (pw_succ two (num 2)).eqTrans
      ((congrMul ((pw_succ two one).eqTrans (congrMul (pw_one two) (.eqRefl _))) (.eqRefl _)).eqTrans (by ipra_ring))
  have idx : Γ ⊢[PRAAx] le (p+num 3) (clock p q E N) :=
    le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (le_add_right _ _))
  have size : Γ ⊢[PRAAx] unit (p+num 3) ≐ num 8*unit p :=
    (pw_add two p (num 3)).eqTrans ((congrMul (.eqRefl _) pow).eqTrans (mul_comm _ _))
  exact le_congr size (.eqRefl _) (GaussianExponentialReference.unit_monotone idx)

theorem original_diagonal (f g K : PR 2) (p q x y z E N a : PTm n)
    (h : Γ ⊢[PRAAx] input f g K p x y z E a) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 (QF (IF g) (IF f) K) q (qd (IF g) (IF f) K (id y E N) (id x E N) z a))
      (ap2 (CF f) q (cd x E N)) (diagonalNumerator (gain E N) (unit p) (cost f g K x y z E N a) q)
      (diagonalDenominator (unit p) q) := by
  let r := clock p q E N
  let A := sampleNumerator f r x
  let B := sampleDenominator f r x
  let C := sampleNumerator g r y
  let D := sampleDenominator g r y
  let T := finiteCoefficient A B C D N
  let W := correctionFactor A B N
  let H := coefficientBound E N
  let P := unit p
  let Q := unit q
  let rawCost := GaussianNamedIncrementFrozenCoefficient.cost (IF g) (IF f) K (id y E N) (id x E N) z a H
  have hf := h.andE₁
  have hg := h.andE₂.andE₁
  have hk := h.andE₂.andE₂.andE₁
  have he := h.andE₂.andE₂.andE₂.andE₁
  have hs := h.andE₂.andE₂.andE₂.andE₂
  have ip := unit_positive (Γ := Γ) p
  have iq := unit_positive (Γ := Γ) q
  have wide := positive_product _ _ ip iq
  have lateI : Γ ⊢[PRAAx] le (GaussianGammaNegativeIntervalNamedInverseFactor.clock q E N) r := by
    exact le_trans (le_add_left _ _) (le_add_right _ _)
  have lateC : Γ ⊢[PRAAx] le (GaussianGammaNegativeIntervalNamedCorrectionFactor.clock q E N) r := le_add_left _ _
  have qr : Γ ⊢[PRAAx] le q r := by
    exact le_trans (le_add_left _ _) (le_trans (le_add_right _ _) (le_add_right _ _))
  have fx := encoded_source f r x E hf
  have gy := encoded_source g r y E hg
  have dh := frozen_step_small f g K p r x y z E hf hg he hs (clock_growth p q E N)
  have error0 := (window_envelope A B C D E N two P fx gy ip dh).andE₂
  have error : Γ ⊢[PRAAx] distanceBounded T W (gain E N) P :=
    distance_congr (.eqRefl _) (.eqRefl _) (by unfold gain; ipra_ring) (.eqRefl _) error0
  have coarse := distance_radius_mono _ _ _ _ (gain E N) one ip (le_refl one)
    (by ipra_le 𝔞(gain E N)*sl ip) error
  have tbound := GaussianReconstructionRoots.norm_from_distance T W (gain E N) one ((E*E)*correctionCap E N) one
    (le_refl one) (le_refl one) coarse (factor_bound A B E N fx)
  have bound : Γ ⊢[PRAAx] bounded T H one :=
    GaussianRationalReciprocal.bound_congr (.eqRefl _) (by unfold H coefficientBound; ipra_ring) (by ipra_ring) tbound
  have hc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical T := GaussianRationalHorner.qmul_canonical _ _
  have inv_at (F : PR 2) (v : PTm n) (hv : Γ ⊢[PRAAx] source F v E) :
      Γ ⊢[PRAAx] distanceBounded (ap2 (IF F) q (id v E N))
        (inverse (sampleNumerator F r v) (sampleDenominator F r v) N) (num 3) Q :=
    read_constant (IF F) q (id v E N) _ (GaussianGammaNegativeIntervalNamedInverseFactor.original_frozen_rate F q r v E N hv lateI)
  have coeff_at := read_constant (CF f) q (cd x E N) W
    (GaussianGammaNegativeIntervalNamedCorrectionFactor.original_frozen_rate f q r x E N hf lateC)
  have as_three (u v : PTm n) (h3 : Γ ⊢[PRAAx] distanceBounded u v (num 3) Q) :
      Γ ⊢[PRAAx] distanceBounded u v GaussianNameRingLaws.three Q :=
    distance_congr (.eqRefl _) (.eqRefl _) (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _) h3
  have near := GaussianNamedIncrementFrozenCoefficient.coefficient_at (IF g) (IF f) K q (id y E N) (id x E N) z a
    (inverse C D N) (inverse A B N) (increment f g r x y) T H
    (.andI (GaussianGammaNegativeIntervalNamedInverseFactor.name_regular g y E N hg)
      (.andI (GaussianGammaNegativeIntervalNamedInverseFactor.name_regular f x E N hf) hk))
    hc bound (exact_difference A B C D N fx.andE₁ gy.andE₁) (as_three _ _ (inv_at g y hg)) (as_three _ _ (inv_at f x hf))
    (approx_increment f g K q r x y z E hf hg he qr)
  have liftQ (u v M : PTm n) (hM : Γ ⊢[PRAAx] distanceBounded u v M Q) :
      Γ ⊢[PRAAx] distanceBounded u v (M*P) (P*Q) :=
    distance_radius_mono _ _ _ _ _ _ iq wide (le_of_eq_add (d := zero) (by ipra_ring)) hM
  have mid := distance_radius_mono _ _ _ _ (gain E N*Q) (P*Q) ip wide
    (le_of_eq_add (d := zero) (by ipra_ring)) error
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [diagonalNumerator,cost,rawCost,P,Q,H]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ wide (liftQ _ _ rawCost near)
      (distance_triangle_same _ _ _ _ _ _ wide mid (liftQ _ _ (num 3) (distance_symmetric _ _ _ _ iq coeff_at))))

theorem original_rate (f g K : PR 2) (p x y z E N a : PTm n)
    (h : Γ ⊢[PRAAx] input f g K p x y z E a) :
    Γ ⊢[PRAAx] independentRate (QF (IF g) (IF f) K) (CF f)
      (qd (IF g) (IF f) K (id y E N) (id x E N) z a) (cd x E N) (gain E N) (unit p) := by
  have hi := GaussianGammaNegativeIntervalNamedInverseFactor.name_regular g y E N h.andE₂.andE₁
  have hj := GaussianGammaNegativeIntervalNamedInverseFactor.name_regular f x E N h.andE₁
  have hQ := GaussianNamedIncrementDifferenceQuotient.name_regular (IF g) (IF f) K (id y E N) (id x E N) z a
    (.andI hi (.andI hj h.andE₂.andE₂.andE₁))
  have hc := GaussianGammaNegativeIntervalNamedCorrectionFactor.name_regular f x E N h.andE₁
  apply GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ (cost f g K x y z E N a) (unit_positive p) hQ hc
  refine .allI ?_
  let sh (t : PTm n) := Syn.shift t
  have hh : Γ.map Fm.shift ⊢[PRAAx] input f g K (sh p) (sh x) (sh y) (sh z) (sh E) (sh a) :=
    by simpa only [Fm.shift, subst_input, sh, Syn.shift] using h.shift
  simpa only [diagonalEnvelope,Syn.shift,sh,GaussianNamedIncrementDifferenceQuotient.subst_data,
    GaussianNamedUnitIntervalRationalLift.subst_data,GaussianNamedIncrementFrozenCoefficient.subst_cost,
    GaussianGammaNegativeProductDerivativeInverseRate.subst_inverseRateCost,
    GaussianGammaNegativeIntervalCorrectionVariation.subst_correctionCap,
    GaussianCoefficientNameBounds.subst_unit,cost,coefficientBound,gain,two,one,
    PTm.subst_mul,PTm.subst_add,PTm.subst_num,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    original_diagonal f g K (sh p) (var 0) (sh x) (sh y) (sh z) (sh E) (sh N) (sh a) hh

theorem actual_negative_interval_named_inverse_factor_derivative_closed (f g K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (input f g K (var 0) (var 1) (var 2) (var 3) (var 4) (var 6) ⟶
        independentRate (QF (IF g) (IF f) K) (CF f)
          (qd (IF g) (IF f) K (id (var 2) (var 4) (var 5)) (id (var 1) (var 4) (var 5)) (var 3) (var 6))
          (cd (var 1) (var 4) (var 5)) (gain (var 4) (var 5)) (unit (var 0))) :=
  closeUniv 7 (.impI (original_rate f g K _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedInverseDerivative
