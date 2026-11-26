import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteCutoffRate

/-!
# Cofinal Cauchy bounds for the actual incomplete Euler pieces

The cutoff is the original rational-interior clock at p and the compact
read precision is p+4. The actual two-piece cutoff estimate gives both
Cauchy bounds. Equal numerical precisions use object equality transport;
strict order uses the genuine additive FastValueCut clock, and arbitrary
order follows by symmetry. No regularity of a new name is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteCofinalRate

open_ipra
open GaussianEulerIncompleteCutoff (clock)
open GaussianEulerIncompleteCutoffParts (lowerData upperData)
open GaussianEulerCompactAdditivity (nameF)
open GaussianEulerCutoffCauchyComparison (combined)
open GaussianGammaIntegralCutoffs (height)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def lowerSample (p z R B A a b : PTm n) : PTm n :=
  ap2 nameF (GaussianEulerCutoffCauchyComparison.clock p) (lowerData z R B (clock p a b) A a b)
def upperSample (p z R B A a b : PTm n) : PTm n :=
  ap2 nameF (GaussianEulerCutoffCauchyComparison.clock p) (upperData z R B (clock p a b) A a b)
def source (z R B A a b : PTm n) : Fm PTm n :=
  GaussianEulerIntegralGammaIdentification.source z R B A ⋏ (le one a ⋏ le one b)

@[simp] theorem subst_cutoffClock {m : ℕ} (σ : Fin n → PTm m) (p a b : PTm n) :
    Syn.subst σ (clock p a b) = clock (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b) := by simp [clock]
ipra_subst lowerData [GaussianEulerIncompleteCutoff.lowerWidth, GaussianEulerIncompleteCutoff.splitPoint, GaussianEulerIncompleteCutoff.denominator, GaussianGammaIntegralCutoffs.etaDen, GaussianGammaIntegralCutoffs.top, height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst upperData [GaussianEulerIncompleteCutoff.upperWidth, GaussianEulerIncompleteCutoff.splitPoint, GaussianEulerIncompleteCutoff.denominator, GaussianGammaIntegralCutoffs.etaDen, GaussianGammaIntegralCutoffs.top, height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst lowerSample
ipra_subst upperSample
ipra_subst source

theorem cutoff_strict (p q a b : PTm n) (h : Γ ⊢[PRAAx] lt p q) : Γ ⊢[PRAAx] lt (clock p a b) (clock q a b) :=
  le_congr (by unfold clock GaussianFastValueCut.exponent; ipra_ring)
    (by unfold clock GaussianFastValueCut.exponent; ipra_ring)
    (add_le_add_right (GaussianFastValueCut.normalizer (succ b)+succ a) h)

theorem lower_sample_congr (p q z R B A a b : PTm n) (h : Γ ⊢[PRAAx] p ≐ q) : Γ ⊢[PRAAx]
    lowerSample p z R B A a b ≐ lowerSample q z R B A a b := by
  simpa using Prf.eqCongr1 (Γ := Γ) (lowerSample (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift a) (Syn.shift b)) h
theorem upper_sample_congr (p q z R B A a b : PTm n) (h : Γ ⊢[PRAAx] p ≐ q) : Γ ⊢[PRAAx]
    upperSample p z R B A a b ≐ upperSample q z R B A a b := by
  simpa using Prf.eqCongr1 (Γ := Γ) (upperSample (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift a) (Syn.shift b)) h

theorem cutoff_budget (p k A R : PTm n) (hpk : Γ ⊢[PRAAx] le p k) : Γ ⊢[PRAAx]
    le (combined A R*unit (GaussianEulerCutoffCauchyComparison.clock p)) (unit (height k A R)) := by
  have heights : Γ ⊢[PRAAx] le (height p A R) (height k A R) :=
    le_congr (by unfold height; ipra_ring) (by unfold height; ipra_ring)
      (add_le_add_right (A+GaussianGammaIntegralCutoffs.tailCoefficient R+num 10) hpk)
  exact le_trans (GaussianEulerCutoffCauchyComparison.cutoff_clock_budget p A R)
    (GaussianExponentialReference.unit_monotone heights)

/-- The original tail costs one extra late dyadic; together with the
five observation dyadics this fits inside the exact p+4 read clock. -/
theorem clocked_radius (p q k A R : PTm n) (hpk : Γ ⊢[PRAAx] le p k) : Γ ⊢[PRAAx]
    le (GaussianEulerIncompleteCutoffRate.numerator (GaussianEulerCutoffCauchyComparison.clock q)
          (GaussianEulerCutoffCauchyComparison.clock p) (combined A R) (unit (height k A R))*(unit p*unit q))
      ((unit p+unit q)*GaussianEulerIncompleteCutoffRate.denominator (GaussianEulerCutoffCauchyComparison.clock q)
        (GaussianEulerCutoffCauchyComparison.clock p) (unit (height k A R))) := by
  let H := unit (height k A R)
  let P := unit (GaussianEulerCutoffCauchyComparison.clock p)
  let Q := unit (GaussianEulerCutoffCauchyComparison.clock q)
  have bound : Γ ⊢[PRAAx]
      le (GaussianEulerIncompleteCutoffRate.numerator (GaussianEulerCutoffCauchyComparison.clock q)
        (GaussianEulerCutoffCauchyComparison.clock p) (combined A R) H) (H*(P+num 6*Q)) := by
    have budget := cutoff_budget p k A R hpk
    have scaled := mul_le_mul_right Q budget
    have joined := add_le_add_right (H*(P+num 5*Q)) scaled
    exact le_congr (by unfold GaussianEulerIncompleteCutoffRate.numerator; dsimp only [P,Q]; ipra_ring)
      (by ipra_ring) joined
  apply le_trans (mul_le_mul_right (unit p*unit q) bound)
  have ep := natEq (GaussianEulerCutoffCauchyComparison.clock_unit (Γ := Γ) p)
  have eq := natEq (GaussianEulerCutoffCauchyComparison.clock_unit (Γ := Γ) q)
  refine le_of_eq_add (d := num 240*H*unit p*unit p*unit q+num 160*H*unit p*unit q*unit q) ?_
  apply deriveNat
  dsimp only [P,Q,GaussianEulerIncompleteCutoffRate.denominator]
  ipra_simps
  rw [ep,eq]
  ring

theorem reduce_clocked (u v p q k A R : PTm n) (hpk : Γ ⊢[PRAAx] le p k)
    (h : Γ ⊢[PRAAx] distanceBounded u v
      (GaussianEulerIncompleteCutoffRate.numerator (GaussianEulerCutoffCauchyComparison.clock q)
        (GaussianEulerCutoffCauchyComparison.clock p) (combined A R) (unit (height k A R)))
      (GaussianEulerIncompleteCutoffRate.denominator (GaussianEulerCutoffCauchyComparison.clock q)
        (GaussianEulerCutoffCauchyComparison.clock p) (unit (height k A R)))) : Γ ⊢[PRAAx]
    distanceBounded u v (unit p+unit q) (unit p*unit q) :=
  distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ (unit_positive _) (unit_positive _)) (unit_positive _))
    (positive_product _ _ (unit_positive p) (unit_positive q)) (clocked_radius p q k A R hpk) h

theorem strict_observations (p q z R B A a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerIntegralGammaIdentification.source z R B A)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) (hpq : Γ ⊢[PRAAx] lt p q) : Γ ⊢[PRAAx]
    distanceBounded (lowerSample p z R B A a b) (lowerSample q z R B A a b) (unit p+unit q) (unit p*unit q) ⋏
    distanceBounded (upperSample p z R B A a b) (upperSample q z R B A a b) (unit p+unit q) (unit p*unit q) := by
  have old := GaussianEulerIncompleteCutoffRate.original_cutoff_piece_observations
    (GaussianEulerCutoffCauchyComparison.clock q) (GaussianEulerCutoffCauchyComparison.clock p) p
    (clock p a b) (clock q a b) z R B A a b h ha hb (le_refl _) (cutoff_strict p q a b hpq)
  have hpk := GaussianEulerIncompleteCutoff.clock_later (Γ := Γ) p a b
  have dp := positive_product (Γ := Γ) _ _ (unit_positive p) (unit_positive q)
  exact .andI (distance_symmetric _ _ _ _ dp (reduce_clocked _ _ p q _ A R hpk old.andE₁))
    (distance_symmetric _ _ _ _ dp (reduce_clocked _ _ p q _ A R hpk old.andE₂))

theorem equal_observations (p q z R B A a b : PTm n) (hpq : Γ ⊢[PRAAx] p ≐ q) : Γ ⊢[PRAAx]
    distanceBounded (lowerSample p z R B A a b) (lowerSample q z R B A a b) (unit p+unit q) (unit p*unit q) ⋏
    distanceBounded (upperSample p z R B A a b) (upperSample q z R B A a b) (unit p+unit q) (unit p*unit q) := by
  have dp := positive_product (Γ := Γ) _ _ (unit_positive p) (unit_positive q)
  have widen (u : PTm n) : Γ ⊢[PRAAx] distanceBounded u u (unit p+unit q) (unit p*unit q) :=
    distance_radius_mono _ _ zero _ _ _ dp dp (le_of_eq_add (d := (unit p+unit q)*(unit p*unit q)) (by ipra_ring))
      (GaussianRationalPowerDifference.distance_refl_zero u _ dp)
  exact .andI (distance_congr (.eqRefl _) (lower_sample_congr p q z R B A a b hpq) (.eqRefl _) (.eqRefl _) (widen _))
    (distance_congr (.eqRefl _) (upper_sample_congr p q z R B A a b hpq) (.eqRefl _) (.eqRefl _) (widen _))

theorem ordered_observations (p q z R B A a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerIntegralGammaIdentification.source z R B A)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    distanceBounded (lowerSample p z R B A a b) (lowerSample q z R B A a b) (unit p+unit q) (unit p*unit q) ⋏
    distanceBounded (upperSample p z R B A a b) (upperSample q z R B A a b) (unit p+unit q) (unit p*unit q) := by
  refine .orE (lt_or_eq_of_le hpq) ?_ ?_
  · exact strict_observations p q z R B A a b h.wk ha.wk hb.wk Prf.hyp0
  · exact equal_observations p q z R B A a b Prf.hyp0

theorem original_piece_observations (p q z R B A a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerIntegralGammaIdentification.source z R B A)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    distanceBounded (lowerSample p z R B A a b) (lowerSample q z R B A a b) (unit p+unit q) (unit p*unit q) ⋏
    distanceBounded (upperSample p z R B A a b) (upperSample q z R B A a b) (unit p+unit q) (unit p*unit q) := by
  refine .orE (le_total p q) ?_ ?_
  · exact ordered_observations p q z R B A a b h.wk ha.wk hb.wk Prf.hyp0
  · have old := ordered_observations q p z R B A a b h.wk ha.wk hb.wk Prf.hyp0
    have dp := positive_product (Γ := (le q p)::Γ) _ _ (unit_positive q) (unit_positive p)
    exact .andI
      (distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring) (distance_symmetric _ _ _ _ dp old.andE₁))
      (distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring) (distance_symmetric _ _ _ _ dp old.andE₂))

theorem sample_regularity (p q z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    distanceBounded (lowerSample p z R B A a b) (lowerSample q z R B A a b) (unit p+unit q) (unit p*unit q) ⋏
    distanceBounded (upperSample p z R B A a b) (upperSample q z R B A a b) (unit p+unit q) (unit p*unit q) :=
  original_piece_observations p q z R B A a b h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂

theorem actual_original_lower_incomplete_Euler_cofinal_cauchy_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((GaussianEulerIntegralGammaIdentification.source (var 2) (var 3) (var 4) (var 5) ⋏ (le one (var 6) ⋏ le one (var 7))) ⟶
      distanceBounded (lowerSample (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
        (lowerSample (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 8 (.impI ((original_piece_observations _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂).andE₁))

theorem actual_original_upper_incomplete_Euler_cofinal_cauchy_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((GaussianEulerIntegralGammaIdentification.source (var 2) (var 3) (var 4) (var 5) ⋏ (le one (var 6) ⋏ le one (var 7))) ⟶
      distanceBounded (upperSample (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
        (upperSample (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 8 (.impI ((original_piece_observations _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂).andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteCofinalRate
