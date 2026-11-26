import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.GaussianGammaMinimumRationalBase
import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.GaussianGammaMinimumLogProperness
import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.GaussianGammaMinimumChordStationary
import IPRADerivations.Analysis.Gamma.Ratios.GaussianGammaRationalWendelBoundary
import IPRADerivations.Analysis.Inequalities.NonnegativeArithmetic.GaussianRationalNonnegativeFractions

/-!
# The strong rational comparison at the selected dyadic base

At every selected dyadic fraction, compare the original log-Gamma
samples to an arbitrary positive rational input. The stationary
residual contributes an explicit uniform error tending to zero as
the grid refines. The comparison retains the squared separation
margin and both independent observation allowances.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaMinimumRational

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaDigammaDyadicLocation (lower)
open GaussianGammaDigammaDyadicMesh (grid)
open GaussianGammaDigammaLocationInput (rational_source)
open GaussianGammaMinimumCenterRate (original_center_log_rate)
open GaussianGammaMinimumChord (margin absDelta)
open GaussianGammaMinimumLogProperness (log_gamma_cross)
open GaussianGammaMinimumRationalBase
  (baseNumerator targetNumerator denominator minimumCost residualCost chord_domain
    rescaled_fraction target_fraction rescaled_derivative_residual)
open GaussianGammaMinimumSignedStep (weight weight_lower)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianNamedRealOrderTransport (upperSlack precision remove_upper_slack)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (qadd qzero positive_product canonical canonical_congr)
open GaussianRationalSyntheticDivision (qadd_congr qzero_add)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData gammaRetimedF gammaRetimedData gammaLogMargin)
open GaussianStirlingGammaFractionalIncrementObservations (scalar_upper)
open RationalValueBounds (upper upper_congr upper_mono upper_triangle upper_order_left)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "F" => logGammaF
local notation "lg" => logGammaData

def rootMargin (k c d M : PTm n) : PTm n := margin (baseNumerator k d) (targetNumerator k c) (denominator k d) M

ipra_subst rootMargin

private theorem margin_denominator_positive (b M : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hM : Γ ⊢[PRAAx] le two M) : Γ ⊢[PRAAx] le one (num 4*(M*b)*(M*b)) := by
  have h := positive_product _ _ (le_trans (le_succ_self one) hM) hb
  exact positive_product _ _ (positive_product _ _ (by ipra_le 3) h) h

private theorem log_canonical (p a b : PTm n) : Γ ⊢[PRAAx] canonical (ap2 F p (lg a b)) := by
  apply canonical_congr (GaussianNamedPositiveLogarithm.sample_at gammaRetimedF p (gammaRetimedData a b) gammaLogMargin)
  exact GaussianPositiveRationalLogarithm.sample_canonical _ _ _

private theorem rational_cases (a c : PTm n) : Γ ⊢[PRAAx] (lt a c ⋎ lt c a) ⋎ a ≐ c := by
  refine .orE (lt_or_le a c) (.orI₁ (.orI₁ Prf.hyp0)) ?_
  exact .orE (lt_or_eq_of_le Prf.hyp0) (.orI₁ (.orI₂ Prf.hyp0)) (.orI₂ Prf.hyp0.eqSymm)

private theorem equal_comparison (p q a c b M K N : PTm n)
    (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c b)
    (hM : Γ ⊢[PRAAx] le two M) (eq : Γ ⊢[PRAAx] a ≐ c) :
    Γ ⊢[PRAAx] upper (fstT (qadd (margin a c b M) (ap2 F p (lg a b))))
      (fstT (ap2 F q (lg c b))) (rateNumerator K N p q) (rateDenominator N p q) := by
  let x := ap2 F p (lg a b)
  have e0 : Γ ⊢[PRAAx] absDelta a c ≐ zero :=
    (congrAdd (congrMonus eq.eqSymm (.eqRefl _)) (congrMonus (.eqRefl _) eq.eqSymm)).eqTrans
      ((congrAdd (monus_self a) (monus_self a)).eqTrans (by ipra_ring))
  have ez : Γ ⊢[PRAAx] margin a c b M ≐ qzero :=
    (GaussianCompactRiemannName.fraction_congr _ _ _ _
      ((congrMul e0 e0).eqTrans (by ipra_ring)) (.eqRefl _)).eqTrans
      (GaussianGammaRationalWendelBoundary.fraction_zero _ (margin_denominator_positive b M ha.andE₂ hM))
  have erase := (qadd_congr ez (.eqRefl x)).eqTrans (qzero_add x (log_canonical p a b))
  have fractions := GaussianCompactRiemannName.fraction_congr a c b b eq (.eqRefl _)
  have agree := log_gamma_cross a b c b ha hc fractions
  have hpq := positive_product _ _ (unit_positive (Γ := Γ) p) (unit_positive q)
  have atom := scalar_upper _ _ _ _ hpq (cross_at _ _ _ _ p q agree)
  exact upper_congr (congrFst erase).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (upper_mono _ _ _ _ _ _ hpq atom (by unfold rateNumerator rateDenominator; ipra_le 𝔞(K)*𝔞(unit p)^2*𝔞(unit q)^2))

private theorem common_comparison (p q k c d M : PTm n) (hc : Γ ⊢[PRAAx] le one c)
    (hd : Γ ⊢[PRAAx] le one d) (hM : Γ ⊢[PRAAx] le two M) (cap : Γ ⊢[PRAAx] le c (M*d)) :
    Γ ⊢[PRAAx] upper (fstT (qadd (rootMargin k c d M) (ap2 F p (lg (baseNumerator k d) (denominator k d)))))
      (fstT (ap2 F q (lg (targetNumerator k c) (denominator k d))))
      (rateNumerator (minimumCost M) (unit k) p q) (rateDenominator (unit k) p q) := by
  let a := baseNumerator k d
  let v := targetNumerator k c
  let b := denominator k d
  let W := weight k a b M
  have root := chord_domain k c d M hc hd hM cap
  refine .orE (rational_cases a v) ?_ ?_
  · have h : (lt a v ⋎ lt v a) :: Γ ⊢[PRAAx] GaussianGammaMinimumSignedStep.domain a v b M := root.wk
    have rate := original_center_log_rate k a v b M residualCost zero h Prf.hyp0
      (rescaled_derivative_residual k d hd).wk
    exact GaussianGammaMinimumChordStationary.stationary_at p q a v b M W (minimumCost M) (unit k)
      h.andE₁.andE₁ h.andE₂.andE₁ h.andE₁.andE₂ h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂
      (weight_lower k a b M) (unit_positive k) rate
  · exact equal_comparison p q a v b M (minimumCost M) (unit k) root.wk.andE₁
      (.andI root.wk.andE₂.andE₁ root.wk.andE₁.andE₂) hM.wk Prf.hyp0

private theorem transfer_comparison (p q k c d M t : PTm n) (hc : Γ ⊢[PRAAx] le one c)
    (hd : Γ ⊢[PRAAx] le one d) (hM : Γ ⊢[PRAAx] le two M) (cap : Γ ⊢[PRAAx] le c (M*d)) :
    Γ ⊢[PRAAx] upperSlack (fstT (qadd (rootMargin k c d M) (ap2 F p (lg (lower k) (grid k)))))
      (fstT (ap2 F q (lg c d))) (rateNumerator (minimumCost M) (unit k) p q) (rateDenominator (unit k) p q)
      (num 4) t := by
  let A := baseNumerator k d
  let B := denominator k d
  let V := targetNumerator k c
  let m := rootMargin k c d M
  let x := lg (lower k) (grid k)
  let y := lg c d
  let x' := lg A B
  let y' := lg V B
  have domain := chord_domain k c d M hc hd hM cap
  have xx := cross_symm _ _ _ _ (log_gamma_cross A B (lower k) (grid k) domain.andE₁
    (rational_source k) (rescaled_fraction k d hd))
  have yy := log_gamma_cross V B c d (.andI domain.andE₂.andE₁ domain.andE₁.andE₂)
    (.andI hc hd) (target_fraction k c d hd)
  have hP := unit_positive (Γ := Γ) p
  have hQ := unit_positive (Γ := Γ) q
  have hU := unit_positive (Γ := Γ) t
  have hPU := positive_product _ _ hP hU
  have hUQ := positive_product _ _ hU hQ
  have hInside := positive_product _ _ (positive_product _ _ (unit_positive k) hU) hU
  have left := GaussianNameArithmetic.sum_distance m m (ap2 F p x) (ap2 F t x') _
    (unit p+unit t) (unit p*unit t) hPU
    (GaussianRationalPowerDifference.distance_refl_zero m _ hPU) (cross_at _ _ _ _ p t xx)
  have l := scalar_upper _ _ (unit p+unit t) _ hPU
    (distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) left)
  have middle := common_comparison t t k c d M hc hd hM cap
  have r := scalar_upper _ _ _ _ hUQ (cross_at _ _ _ _ t q yy)
  have joined := upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ l middle) r
  apply upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hPU hInside) hUQ) joined
  unfold rateNumerator rateDenominator
  ipra_le 0

theorem root_margin_independent_at (p q k c d M : PTm n) (hc : Γ ⊢[PRAAx] le one c)
    (hd : Γ ⊢[PRAAx] le one d) (hM : Γ ⊢[PRAAx] le two M) (cap : Γ ⊢[PRAAx] le c (M*d)) :
    Γ ⊢[PRAAx] upper (fstT (qadd (rootMargin k c d M) (ap2 F p (lg (lower k) (grid k)))))
      (fstT (ap2 F q (lg c d))) (rateNumerator (minimumCost M) (unit k) p q) (rateDenominator (unit k) p q) :=
  remove_upper_slack _ _ _ _ (num 4)
    (transfer_comparison p q k c d M (precision _ _ _ (num 4)) hc hd hM cap)

theorem root_margin_at (p k c d M : PTm n) (hc : Γ ⊢[PRAAx] le one c)
    (hd : Γ ⊢[PRAAx] le one d) (hM : Γ ⊢[PRAAx] le two M) (cap : Γ ⊢[PRAAx] le c (M*d)) :
    Γ ⊢[PRAAx] upper (fstT (qadd (rootMargin k c d M) (ap2 F p (lg (lower k) (grid k)))))
      (fstT (ap2 F p (lg c d))) (minimumCost M*unit p+two*unit k) (unit k*unit p) := by
  have h := root_margin_independent_at p p k c d M hc hd hM cap
  have den := GaussianNamedInverseRate.denominator_positive (Γ := Γ) (unit k) p p (unit_positive k)
  exact upper_mono _ _ _ _ _ _ den h (by unfold rateNumerator rateDenominator; ipra_le 0)

theorem root_order_at (p k c d M : PTm n) (hc : Γ ⊢[PRAAx] le one c)
    (hd : Γ ⊢[PRAAx] le one d) (hM : Γ ⊢[PRAAx] le two M) (cap : Γ ⊢[PRAAx] le c (M*d)) :
    Γ ⊢[PRAAx] upper (fstT (ap2 F p (lg (lower k) (grid k)))) (fstT (ap2 F p (lg c d)))
      (minimumCost M*unit p+two*unit k) (unit k*unit p) := by
  let x := ap2 F p (lg (lower k) (grid k))
  let m := rootMargin k c d M
  have den := (chord_domain k c d M hc hd hM cap).andE₁.andE₂
  have hm : Γ ⊢[PRAAx] RationalArgmin.rationalLE RationalGaussianEmbedding.scalarZero (fstT m) :=
    (GaussianRationalNonnegativeFractions.fraction_nonnegative _ _
    (margin_denominator_positive (denominator k d) M den hM)).andE₁
  have order := RationalArgmin.rationalLE_congr (RationalGaussianRealPart.real_zero (Γ := Γ)).eqSymm (.eqRefl _) hm
  have sum := GaussianStirlingTailComparison.point_add_order qzero m x x order (RationalArgmin.reflexive _)
  have first := RationalArgmin.rationalLE_congr (congrFst (qzero_add x (log_canonical p (lower k) (grid k))))
    (.eqRefl _) sum
  exact upper_order_left _ _ _ _ _ first (root_margin_at p k c d M hc hd hM cap)

theorem actual_dyadic_base_rational_log_Gamma_margin_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((le one (var 3) ⋏ (le one (var 4) ⋏ (le two (var 5) ⋏ le (var 3) (var 5*var 4)))) ⟶
        upper (fstT (qadd (rootMargin (var 2) (var 3) (var 4) (var 5))
            (ap2 F (var 0) (lg (lower (var 2)) (grid (var 2))))))
          (fstT (ap2 F (var 1) (lg (var 3) (var 4))))
          (rateNumerator (minimumCost (var 5)) (unit (var 2)) (var 0) (var 1))
          (rateDenominator (unit (var 2)) (var 0) (var 1))) :=
  closeUniv 6 (.impI (root_margin_independent_at _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaMinimumRational
