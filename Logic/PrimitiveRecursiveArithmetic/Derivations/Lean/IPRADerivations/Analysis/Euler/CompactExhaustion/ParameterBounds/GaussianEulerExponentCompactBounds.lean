import IPRADerivations.Analysis.Logarithm.PositiveAxis.Bounds.GaussianCompactLogarithmBounds
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIntegrandName
import IPRADerivations.Analysis.Polynomials.RootFinding.Characteristic.GaussianCharacteristicEntryNorm

/-!
# Original Euler exponent: compact disks and local sampled variation

The actual exponent program retains the original coefficient, logarithm
and both operation clocks. Original compact-time and input-disk guards
derive one encoding-independent radius and a local input-relative rate.
This is a conservative supplier; no integrand/output law is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerExponentCompactBounds

open_ipra
open GaussianRationalHorner (positive_product qadd qmul)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactLogarithmBounds (domain)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianEulerIntegrandName (coefficient decayPoint exponentF exponentData exponent_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def source (z R B E : PTm n) : Fm PTm n := le one B ⋏ (le one E ⋏ ComplexLogarithmRemainder.bounded z (R*B))
def radius (R E T : PTm n) : PTm n := (R+one)*GaussianCompactLogarithmBounds.radius E T+T
def factor (R E : PTm n) : PTm n := (R+one)*E+one
def clock (p z B a b : PTm n) : PTm n := GaussianEulerIntegrandName.powerClock (GaussianFastValueCut.exponent two p) z B a b
ipra_subst source [ComplexLogarithmRemainder.bounded]
ipra_subst radius
ipra_subst factor
ipra_subst clock

theorem fraction_bound (a b T : PTm n) (hb : Γ ⊢[PRAAx] le one b) (h : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    bounded (fraction a b) T one := by
  have norm : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq (ComplexLogarithmRemainder.scale a ComplexLogarithmRemainder.oneCode) ≐ a*a :=
    (ComplexLogarithmRemainder.normSq_scale _ _).eqTrans
      ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring))
  exact GaussianRationalMetric.bounded_of_cleared _ _ b T one hb (le_refl one)
    (GaussianRationalHorner.ofGaussian_represents _ _ hb)
    (le_congr ((congrMul (.eqRefl (one*one)) norm).eqTrans (by ipra_ring)).eqSymm (by ipra_ring) (sq_le_sq h))

theorem exponent_bound (p z R B E T a b : PTm n) (hz : Γ ⊢[PRAAx] source z R B E) (ht : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx]
    bounded (ap2 exponentF p (exponentData z B a b)) (radius R E T) one := by
  have prod := GaussianRationalReciprocal.bounded_product_one
    (GaussianEulerIntegrandName.coefficient_bound z R B hz.andE₁ hz.andE₂.andE₂)
    (GaussianCompactLogarithmBounds.sample_bound (clock p z B a b) a b E T hz.andE₂.andE₁ ht)
  have neg := GaussianRationalReciprocal.bounded_negative _ T one (le_refl one) (fraction_bound a b T ht.andE₁.andE₂ ht.andE₂.andE₂)
  exact GaussianRationalReciprocal.bound_congr (exponent_at p z B a b).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalPowerDifference.bounded_sum_one prod neg)

theorem clock_later (p z B a b : PTm n) : Γ ⊢[PRAAx] le p (clock p z B a b) := by
  unfold clock GaussianEulerIntegrandName.powerClock GaussianFastValueCut.exponent
  exact le_of_eq_add (d := GaussianFastValueCut.normalizer two+
    GaussianFastValueCut.normalizer (GaussianNameArithmetic.multiplyModulus GaussianGammaCanonicalExponent.constantF
      GaussianPositiveRationalLogarithm.logF (coefficient z B) (GaussianPositiveRationalLogarithm.data a b))) (by ipra_ring)

theorem negative_distance (a b A D : PTm n) (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] distanceBounded a b A D) : Γ ⊢[PRAAx]
    distanceBounded (GaussianRationalMetric.qnegative a) (GaussianRationalMetric.qnegative b) A D :=
  GaussianRationalReciprocal.bound_congr (GaussianCharacteristicEntryNorm.negative_difference a b).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalReciprocal.bounded_negative _ A D hD h)

/-- Both real operation clocks are used; neither is replaced by p. -/
theorem retimed_log_distance (p z B a b c d E A D : PTm n)
    (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] GaussianNamedInverseRate.independentRate GaussianPositiveRationalLogarithm.logF GaussianPositiveRationalLogarithm.logF
      (GaussianPositiveRationalLogarithm.data a b) (GaussianPositiveRationalLogarithm.data c d) (E*A) D) : Γ ⊢[PRAAx]
    distanceBounded (GaussianPositiveRationalLogarithm.sample (clock p z B a b) a b)
      (GaussianPositiveRationalLogarithm.sample (clock p z B c d) c d) ((E*A)*unit p+two*D) (D*unit p) := by
  let s := clock p z B a b
  let t := clock p z B c d
  have old := GaussianNamedInverseRate.rate_at _ _ _ _ _ _ s t h
  have gs : Γ ⊢[PRAAx] le (unit p) (unit s) := GaussianFactorBudget.power_monotone_length two p s (le_succ_self one) (clock_later p z B a b)
  have gt : Γ ⊢[PRAAx] le (unit p) (unit t) := GaussianFactorBudget.power_monotone_length two p t (le_succ_self one) (clock_later p z B c d)
  apply distance_radius_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive D s t hD) (positive_product _ _ hD (unit_positive p)) _ old
  unfold GaussianNamedInverseRate.rateNumerator GaussianNamedInverseRate.rateDenominator
  ipra_le (𝔞(D)*𝔞(D)*𝔞(unit t))*sl gs+(𝔞(D)*𝔞(D)*𝔞(unit s))*sl gt

/-- Genuine source-only variation of the unchanged actual exponent. -/
theorem exponent_diagonal (p z R B E T a b c d A D : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B E) (ha : Γ ⊢[PRAAx] domain a b E T) (hc : Γ ⊢[PRAAx] domain c d E T)
    (hD : Γ ⊢[PRAAx] le one D) (hd : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) A D) : Γ ⊢[PRAAx]
    distanceBounded (ap2 exponentF p (exponentData z B a b)) (ap2 exponentF p (exponentData z B c d))
      ((factor R E*A)*unit p+(two*(R+one))*D) (D*unit p) := by
  have logRate := GaussianCompactLogarithmBounds.original_log_rate a b c d E A D ha.andE₁ hc.andE₁ hD ha.andE₂.andE₁ hc.andE₂.andE₁ hd
  have logs := retimed_log_distance p z B a b c d E A D hD logRate
  have den := positive_product _ _ hD (unit_positive p)
  have multiplied := GaussianNameRingLaws.product_right_error (coefficient z B) _ _ _ _ (GaussianCompactLogarithmBounds.radius E T) (R+one) den logs
    (GaussianCompactLogarithmBounds.sample_bound _ a b E T hz.andE₂.andE₁ ha)
    (GaussianEulerIntegrandName.coefficient_bound z R B hz.andE₁ hz.andE₂.andE₂)
  have decay := distance_radius_mono _ _ _ _ (A*unit p) (D*unit p) hD den
    (le_of_eq_add (d := zero) (by ipra_ring)) (negative_distance _ _ A D hD hd)
  have both := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ den multiplied decay
  exact distance_congr (exponent_at p z B a b).eqSymm (exponent_at p z B c d).eqSymm (by unfold factor; ipra_ring) (.eqRefl _) both


def input (z R B E T a b c d A D : PTm n) : Fm PTm n := source z R B E ⋏
  (domain a b E T ⋏ (domain c d E T ⋏ (le one D ⋏ distanceBounded (fraction a b) (fraction c d) A D)))
ipra_subst input

theorem exponent_envelope (z R B E T a b c d A D : PTm n) (h : Γ ⊢[PRAAx] input z R B E T a b c d A D) : Γ ⊢[PRAAx]
    GaussianNamedLipschitzRate.diagonalEnvelope exponentF exponentF (exponentData z B a b) (exponentData z B c d)
      (factor R E*A) D (two*(R+one)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift E) (Syn.shift T)
      (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d) (Syn.shift A) (Syn.shift D) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa only [GaussianNamedLipschitzRate.diagonalEnvelope,GaussianNamedLipschitzRate.diagonalNumerator,
    GaussianNamedLipschitzRate.diagonalDenominator,GaussianEulerIntegrandName.subst_exponentData,
    PTm.subst_mul,PTm.subst_add,subst_factor,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using
    exponent_diagonal (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift E) (Syn.shift T)
      (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d) (Syn.shift A) (Syn.shift D)
      hs.andE₁ hs.andE₂.andE₁ hs.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₂.andE₂

/-- Actual original exponent names, with the sharp ordinary errors. -/
theorem independent_rate (z R B E T a b c d A D : PTm n) (h : Γ ⊢[PRAAx] input z R B E T a b c d A D) : Γ ⊢[PRAAx]
    GaussianNamedInverseRate.independentRate exponentF exponentF (exponentData z B a b) (exponentData z B c d) (factor R E*A) D :=
  GaussianNamedLipschitzRate.independent_rate exponentF exponentF (exponentData z B a b) (exponentData z B c d)
    (factor R E*A) D (two*(R+one)) h.andE₂.andE₂.andE₂.andE₁
    (GaussianEulerIntegrandName.exponent_regular z B a b (.andI h.andE₁.andE₁ h.andE₂.andE₁.andE₁))
    (GaussianEulerIntegrandName.exponent_regular z B c d (.andI h.andE₁.andE₁ h.andE₂.andE₂.andE₁.andE₁)) (exponent_envelope z R B E T a b c d A D h)

/-- A common input radius for the ORIGINAL exponent program, independent
of the time fraction's encoding and the individual computed name radius. -/
theorem common_exponential_input (z R B E T a b : PTm n) (hz : Γ ⊢[PRAAx] source z R B E) (ht : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input exponentF (radius R E T) (exponentData z B a b) := by
  refine .andI (GaussianEulerIntegrandName.exponent_regular z B a b (.andI hz.andE₁ ht.andE₁)) (.allI ?_)
  have zs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hz.shift
  have ts : Γ.map Fm.shift ⊢[PRAAx] domain (Syn.shift a) (Syn.shift b) (Syn.shift E) (Syn.shift T) := by simpa [Fm.shift,Syn.shift] using ht.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples,GaussianEulerIntegrandName.subst_exponentData,subst_radius,Syn.shift] using
    exponent_bound (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift E) (Syn.shift T) (Syn.shift a) (Syn.shift b) zs ts

def output (p z R B E T a b : PTm n) : PTm n := pairT (ap2 exponentF p (exponentData z B a b)) (pairT (radius R E T) (factor R E))
def outputF : PR 8 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
def run (p z R B E T a b : PTm n) : PTm n := PTm.app outputF ![p,z,R,B,E,T,a,b]
ipra_subst output
theorem program_at (p z R B E T a b : PTm n) : Γ ⊢[PRAAx] run p z R B E T a b ≐ output p z R B E T a b := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) : PTm 8) ![p,z,R,B,E,T,a,b]
theorem returned_sample (p z R B E T a b : PTm n) : Γ ⊢[PRAAx] fstT (run p z R B E T a b) ≐ ap2 exponentF p (exponentData z B a b) :=
  (program_at p z R B E T a b).fstE
theorem returned_tail (p z R B E T a b : PTm n) : Γ ⊢[PRAAx] sndT (run p z R B E T a b) ≐ pairT (radius R E T) (factor R E) :=
  (program_at p z R B E T a b).sndE
theorem returned_radius (p z R B E T a b : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run p z R B E T a b)) ≐ radius R E T :=
  (returned_tail p z R B E T a b).fstE
theorem returned_factor (p z R B E T a b : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run p z R B E T a b)) ≐ factor R E :=
  (returned_tail p z R B E T a b).sndE

theorem actual_original_compact_Euler_exponent_disk_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 1) (var 2) (var 3) (var 4) ⟶ domain (var 6) (var 7) (var 4) (var 5) ⟶
      bounded (ap2 exponentF (var 0) (exponentData (var 1) (var 3) (var 6) (var 7))) (radius (var 2) (var 4) (var 5)) one) :=
  closeUniv 8 (.impI (.impI (exponent_bound _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_compact_Euler_exponent_independent_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
      GaussianNamedInverseRate.independentRate exponentF exponentF (exponentData (var 0) (var 2) (var 5) (var 6))
        (exponentData (var 0) (var 2) (var 7) (var 8)) (factor (var 1) (var 3)*var 9) (var 10)) :=
  closeUniv 11 (.impI (independent_rate _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_original_Euler_exponent_common_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 0) (var 1) (var 2) (var 3) ⟶ domain (var 5) (var 6) (var 3) (var 4) ⟶
      GaussianRadiusExponentialName.input exponentF (radius (var 1) (var 3) (var 4)) (exponentData (var 0) (var 2) (var 5) (var 6))) :=
  closeUniv 7 (.impI (.impI (common_exponential_input _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_compact_Euler_exponent_bound_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) :=
  closeUniv 8 (program_at _ _ _ _ _ _ _ _)

theorem scale_value_bound (c d : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx] bounded (fraction c d) c one :=
  GaussianEulerExponentCompactBounds.fraction_bound c d c hd
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right c hd))

end LeanProofs.IPRA.Analysis.GaussianEulerExponentCompactBounds
