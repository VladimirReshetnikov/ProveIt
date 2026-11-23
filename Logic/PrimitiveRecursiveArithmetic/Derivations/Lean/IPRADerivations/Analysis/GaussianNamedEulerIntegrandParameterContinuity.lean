import IPRADerivations.Analysis.GaussianNamedEulerIntegrand
import IPRADerivations.Analysis.GaussianEulerIntegrandParameterContinuity

/-!
# Actual named Euler integrand versus an encoded parameter

The radius is computed from the given original name. Exact observations
of its nested original additions and multiplication retain every real
query clock. The original compact logarithm disk and a genuine named
input distance yield the same uniform parameter Lipschitz factor as for
two rational parameters, with the two ordinary observation errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedEulerIntegrandParameterContinuity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedEulerIntegrand (coefficientF coefficientData powerExponentF powerExponentData exponentF exponentData)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianRationalHorner (qadd qmul ofGaussian positive_product)
open GaussianRationalMetric (qsub bounded distanceBounded)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def radius (f : PR 2) (x : PTm n) : PTm n := GaussianNameBounds.U f x
def factor (f : PR 2) (x E T : PTm n) : PTm n := GaussianEulerIntegrandParameterContinuity.factor (radius f x) E T
def input (f : PR 2) (x z B E T a b A N : PTm n) : Fm PTm n := pointCN f x ⋏
  (GaussianEulerExponentCompactBounds.source z (radius f x) B E ⋏ (GaussianCompactLogarithmBounds.domain a b E T ⋏
    (le one N ⋏ independentRate f constantF x (ofGaussian z B) A N)))
def addClock (p : PTm n) : PTm n := GaussianFastValueCut.exponent two p
def productClock (f : PR 2) (p x a b : PTm n) : PTm n := GaussianFastValueCut.exponent
  (GaussianNameArithmetic.multiplyModulus (coefficientF f) GaussianEulerIntegrandName.logarithmF
    (coefficientData x) (GaussianPositiveRationalLogarithm.data a b)) p
def logarithmClock (f : PR 2) (p x a b : PTm n) : PTm n := productClock f (addClock p) x a b
def inputClock (f : PR 2) (p x a b : PTm n) : PTm n := addClock (logarithmClock f p x a b)
def coefficientPoint (f : PR 2) (p x : PTm n) : PTm n := qsub (ap2 f p x) qone

@[simp] theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x : PTm n) :
    Syn.subst σ (radius f x) = radius f (Syn.subst σ x) := by simp [radius]
@[simp] theorem subst_factor {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x E T : PTm n) :
    Syn.subst σ (factor f x E T) = factor f (Syn.subst σ x) (Syn.subst σ E) (Syn.subst σ T) := by simp [factor]
@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x z B E T a b A N : PTm n) :
    (input f x z B E T a b A N).subst σ = input f (Syn.subst σ x) (Syn.subst σ z) (Syn.subst σ B)
      (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ A) (Syn.subst σ N) := by simp [input]
@[simp] theorem subst_exponentData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x a b : PTm n) :
    Syn.subst σ (exponentData f x a b) = exponentData f (Syn.subst σ x) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [exponentData,powerExponentData,coefficientData,qone,ComplexLogarithmRemainder.oneCode,
    ComplexLogarithmRemainder.code,ZT.ofNat]

theorem coefficient_at (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    ap2 (coefficientF f) p (coefficientData x) ≐ coefficientPoint f (addClock p) x :=
  (GaussianNameArithmetic.add_at f constantF _ _ p).eqTrans
    ((GaussianNameArithmetic.recode_congr (qadd_congr (.eqRefl _) (constant_at _ _))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qadd_canonical _ _)))

theorem power_exponent_at (f : PR 2) (p x a b : PTm n) : Γ ⊢[PRAAx]
    ap2 (powerExponentF f) p (powerExponentData f x a b) ≐
      qmul (coefficientPoint f (addClock (productClock f p x a b)) x)
        (GaussianPositiveRationalLogarithm.sample (productClock f p x a b) a b) :=
  (GaussianNameArithmetic.multiply_at (coefficientF f) GaussianEulerIntegrandName.logarithmF _ _ p).eqTrans
    ((GaussianNameArithmetic.recode_congr (qmul_congr (coefficient_at f _ x) (.eqRefl _))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _)))

theorem exponent_at (f : PR 2) (p x a b : PTm n) : Γ ⊢[PRAAx]
    ap2 (exponentF f) p (exponentData f x a b) ≐ qadd
      (qmul (coefficientPoint f (inputClock f p x a b) x)
        (GaussianPositiveRationalLogarithm.sample (logarithmClock f p x a b) a b)) (GaussianEulerIntegrandName.decayPoint a b) :=
  (GaussianNameArithmetic.add_at (powerExponentF f) constantF _ _ p).eqTrans
    ((GaussianNameArithmetic.recode_congr (qadd_congr (power_exponent_at f _ x a b) (constant_at _ _))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qadd_canonical _ _)))

theorem add_clock_later (p : PTm n) : Γ ⊢[PRAAx] le p (addClock p) := le_add_right _ _
theorem product_clock_later (f : PR 2) (p x a b : PTm n) : Γ ⊢[PRAAx] le p (productClock f p x a b) := le_add_right _ _
theorem logarithm_clock_later (f : PR 2) (p x a b : PTm n) : Γ ⊢[PRAAx] le p (logarithmClock f p x a b) :=
  le_trans (add_clock_later p) (product_clock_later f _ x a b)
theorem input_clock_later (f : PR 2) (p x a b : PTm n) : Γ ⊢[PRAAx] le p (inputClock f p x a b) :=
  le_trans (logarithm_clock_later f p x a b) (add_clock_later _)

theorem coefficient_point_bound (f : PR 2) (p x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    bounded (coefficientPoint f p x) (radius f x+one) one :=
  GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (GaussianRationalReciprocal.bounded_difference _ _ (radius f x) one one one (le_refl _) (le_refl _)
      (GaussianNameBounds.sample_bound f x p hf) GaussianRationalReciprocal.qone_bounded)

theorem exponent_bound (f : PR 2) (p x E T a b : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hE : Γ ⊢[PRAAx] le one E) (ht : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain a b E T) : Γ ⊢[PRAAx]
    bounded (ap2 (exponentF f) p (exponentData f x a b)) (GaussianEulerExponentCompactBounds.radius (radius f x) E T) one := by
  have prod := GaussianRationalReciprocal.bounded_product _ _ (radius f x+one) one (GaussianCompactLogarithmBounds.radius E T) one
    (le_refl one) (le_refl one) (coefficient_point_bound f (inputClock f p x a b) x hf)
    (GaussianCompactLogarithmBounds.sample_bound (logarithmClock f p x a b) a b E T hE ht)
  have neg := GaussianRationalReciprocal.bounded_negative _ T one (le_refl one)
    (GaussianEulerExponentCompactBounds.fraction_bound a b T ht.andE₁.andE₂ ht.andE₂.andE₂)
  have both := GaussianRationalReciprocal.bounded_sum _ _ _ (one*one) T one
    (positive_product _ _ (le_refl one) (le_refl one)) (le_refl one) prod neg
  exact GaussianRationalReciprocal.bound_congr (exponent_at f p x a b).eqSymm
    (by unfold GaussianEulerExponentCompactBounds.radius; ipra_ring) (by ipra_ring) both

theorem actual_input_distance (f : PR 2) (p x z B a b A N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] independentRate f constantF x (ofGaussian z B) A N) : Γ ⊢[PRAAx]
    distanceBounded (coefficientPoint f (inputClock f p x a b) x) (GaussianEulerIntegrandName.coefficient z B)
      (A*unit p+two*N) (N*unit p) := by
  let s := inputClock f p x a b
  have old := distance_congr (.eqRefl _) (constant_at p (ofGaussian z B)) (.eqRefl _) (.eqRefl _)
    (GaussianNamedInverseRate.rate_at f constantF x (ofGaussian z B) A N s p h)
  have gs := GaussianExponentialReference.unit_monotone (Γ := Γ) (input_clock_later f p x a b)
  have coarse := distance_radius_mono _ _ _ _ (A*unit p+two*N) (N*unit p)
    (GaussianNamedInverseRate.denominator_positive N s p hN) (positive_product _ _ hN (unit_positive p)) ?_ old
  · exact GaussianNameRingLaws.sum_left_error _ _ _ _ _ (positive_product _ _ hN (unit_positive p)) coarse
  · unfold rateNumerator rateDenominator
    dsimp only [s]
    ipra_le (𝔞 N*𝔞 N*𝔞(unit p))*sl gs

theorem actual_logarithm_distance (f : PR 2) (p x z B a b : PTm n)
    (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) : Γ ⊢[PRAAx]
    distanceBounded (GaussianPositiveRationalLogarithm.sample (logarithmClock f p x a b) a b)
      (GaussianPositiveRationalLogarithm.sample (GaussianEulerExponentCompactBounds.clock p z B a b) a b) two (unit p) := by
  let s := logarithmClock f p x a b
  let t := GaussianEulerExponentCompactBounds.clock p z B a b
  have old := GaussianNameEquivalence.point_at GaussianPositiveRationalLogarithm.logF
    (GaussianPositiveRationalLogarithm.data a b) s t (GaussianPositiveRationalLogarithm.name_regular a b ht)
  have gs := GaussianExponentialReference.unit_monotone (Γ := Γ) (logarithm_clock_later f p x a b)
  have gt := GaussianExponentialReference.unit_monotone (Γ := Γ) (GaussianEulerExponentCompactBounds.clock_later p z B a b)
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive s) (unit_positive t)) (unit_positive p) _ old
  ipra_le 𝔞(unit t)*sl gs+𝔞(unit s)*sl gt

theorem exponent_diagonal (f : PR 2) (p x z B E T a b A N : PTm n)
    (h : Γ ⊢[PRAAx] input f x z B E T a b A N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (exponentF f) p (exponentData f x a b))
      (ap2 GaussianEulerIntegrandName.exponentF p (GaussianEulerIntegrandName.exponentData z B a b))
      ((GaussianCompactLogarithmBounds.radius E T*A)*unit p+
        (two*GaussianCompactLogarithmBounds.radius E T+two*(radius f x+one))*N) (N*unit p) := by
  have hN := h.andE₂.andE₂.andE₂.andE₁
  have ht := h.andE₂.andE₂.andE₁
  have den := positive_product _ _ hN (unit_positive p)
  have logs := distance_radius_mono _ _ _ _ (two*N) (N*unit p) (unit_positive p) den
    (le_of_eq_add (d := zero) (by ipra_ring)) (actual_logarithm_distance f p x z B a b ht.andE₁)
  have products := GaussianNameArithmetic.product_distance _ _ _ _ (A*unit p+two*N) (two*N) (N*unit p)
    (GaussianCompactLogarithmBounds.radius E T) (radius f x+one) den
    (actual_input_distance f p x z B a b A N hN h.andE₂.andE₂.andE₂.andE₂) logs
    (GaussianCompactLogarithmBounds.sample_bound _ a b E T h.andE₂.andE₁.andE₂.andE₁ ht)
    (GaussianEulerIntegrandName.coefficient_bound z (radius f x) B h.andE₂.andE₁.andE₁ h.andE₂.andE₁.andE₂.andE₂)
  have both := GaussianNameRingLaws.sum_left_error _ _ (GaussianEulerIntegrandName.decayPoint a b) _ _ den products
  exact distance_congr (exponent_at f p x a b).eqSymm (GaussianEulerIntegrandName.exponent_at p z B a b).eqSymm (by ipra_ring) (.eqRefl _) both

theorem exponent_envelope (f : PR 2) (x z B E T a b A N : PTm n)
    (h : Γ ⊢[PRAAx] input f x z B E T a b A N) : Γ ⊢[PRAAx]
    GaussianNamedLipschitzRate.diagonalEnvelope (exponentF f) GaussianEulerIntegrandName.exponentF
      (exponentData f x a b) (GaussianEulerIntegrandName.exponentData z B a b) (GaussianCompactLogarithmBounds.radius E T*A) N
      (two*GaussianCompactLogarithmBounds.radius E T+two*(radius f x+one)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input f (Syn.shift x) (Syn.shift z) (Syn.shift B) (Syn.shift E) (Syn.shift T)
      (Syn.shift a) (Syn.shift b) (Syn.shift A) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa only [GaussianNamedLipschitzRate.diagonalEnvelope,GaussianNamedLipschitzRate.diagonalNumerator,
    GaussianNamedLipschitzRate.diagonalDenominator,subst_exponentData,GaussianEulerIntegrandName.subst_exponentData,
    GaussianCompactLogarithmBounds.subst_radius,subst_radius,PTm.subst_mul,PTm.subst_add,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using
    exponent_diagonal f (var 0) (Syn.shift x) (Syn.shift z) (Syn.shift B) (Syn.shift E) (Syn.shift T)
      (Syn.shift a) (Syn.shift b) (Syn.shift A) (Syn.shift N) hs

theorem exponent_rate (f : PR 2) (x z B E T a b A N : PTm n)
    (h : Γ ⊢[PRAAx] input f x z B E T a b A N) : Γ ⊢[PRAAx]
    independentRate (exponentF f) GaussianEulerIntegrandName.exponentF (exponentData f x a b)
      (GaussianEulerIntegrandName.exponentData z B a b) (GaussianCompactLogarithmBounds.radius E T*A) N :=
  GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ _ h.andE₂.andE₂.andE₂.andE₁
    (GaussianNamedEulerIntegrand.exponent_regular f x a b h.andE₁ h.andE₂.andE₂.andE₁.andE₁)
    (GaussianEulerIntegrandName.exponent_regular z B a b (.andI h.andE₂.andE₁.andE₁ h.andE₂.andE₂.andE₁.andE₁))
    (exponent_envelope f x z B E T a b A N h)

theorem common_input (f : PR 2) (x E T a b : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hE : Γ ⊢[PRAAx] le one E) (ht : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain a b E T) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input (exponentF f) (GaussianEulerExponentCompactBounds.radius (radius f x) E T) (exponentData f x a b) := by
  refine .andI (GaussianNamedEulerIntegrand.exponent_regular f x a b hf ht.andE₁) (.allI ?_)
  have fs : Γ.map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using hf.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hE.shift
  have ts : Γ.map Fm.shift ⊢[PRAAx] GaussianCompactLogarithmBounds.domain (Syn.shift a) (Syn.shift b) (Syn.shift E) (Syn.shift T) := by
    simpa [Fm.shift,Syn.shift] using ht.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples,subst_exponentData,GaussianEulerExponentCompactBounds.subst_radius,subst_radius,Syn.shift] using
    exponent_bound f (var 0) (Syn.shift x) (Syn.shift E) (Syn.shift T) (Syn.shift a) (Syn.shift b) fs es ts

theorem original_rate (f : PR 2) (x z B E T a b A N : PTm n)
    (h : Γ ⊢[PRAAx] input f x z B E T a b A N) : Γ ⊢[PRAAx]
    independentRate (GaussianNamedEulerIntegrand.nameF f) GaussianEulerIntegrandName.nameF
      (GaussianNamedEulerIntegrand.data f x a b) (GaussianEulerIntegrandName.data z B a b) (factor f x E T*A) N := by
  let M := GaussianEulerExponentCompactBounds.radius (radius f x) E T
  let L := GaussianCompactLogarithmBounds.radius E T
  have ca := common_input f x E T a b h.andE₁ h.andE₂.andE₁.andE₂.andE₁ h.andE₂.andE₂.andE₁
  have cz := GaussianEulerExponentCompactBounds.common_exponential_input z (radius f x) B E T a b h.andE₂.andE₁ h.andE₂.andE₂.andE₁
  have origF := GaussianGammaFiniteApproximantName.exponential_input _ _
    (GaussianNamedEulerIntegrand.exponent_regular f x a b h.andE₁ h.andE₂.andE₂.andE₁.andE₁)
  have origZ := GaussianEulerIntegrandName.exponent_input z B a b (.andI h.andE₂.andE₁.andE₁ h.andE₂.andE₂.andE₁.andE₁)
  have common := GaussianRadiusExponentialLipschitzRate.independent_rate (exponentF f) GaussianEulerIntegrandName.exponentF M
    (exponentData f x a b) (GaussianEulerIntegrandName.exponentData z B a b) (L*A) N
    (.andI h.andE₂.andE₂.andE₂.andE₁ (.andI ca (.andI cz (exponent_rate f x z B E T a b A N h))))
  have left := GaussianExponentialRadiusIndependence.independent_radii_proper (exponentF f) (exponentF f)
    (GaussianNameBounds.U (exponentF f) (exponentData f x a b)) M (exponentData f x a b) (exponentData f x a b) origF ca
    (GaussianNameEquivalence.cross_refl _ _ origF.andE₁)
  have right := GaussianExponentialRadiusIndependence.independent_radii_proper GaussianEulerIntegrandName.exponentF GaussianEulerIntegrandName.exponentF
    (GaussianEulerIntegrandName.radius z B a b) M (GaussianEulerIntegrandName.exponentData z B a b) (GaussianEulerIntegrandName.exponentData z B a b) origZ cz
    (GaussianNameEquivalence.cross_refl _ _ origZ.andE₁)
  have moved := GaussianNamedRateTransport.transport (GaussianRadiusExponentialName.nameF (exponentF f)) (GaussianRadiusExponentialName.nameF GaussianEulerIntegrandName.exponentF)
    (GaussianNamedEulerIntegrand.nameF f) GaussianEulerIntegrandName.nameF (GaussianRadiusExponentialName.data M (exponentData f x a b))
    (GaussianRadiusExponentialName.data M (GaussianEulerIntegrandName.exponentData z B a b)) (GaussianNamedEulerIntegrand.data f x a b) (GaussianEulerIntegrandName.data z B a b)
    (GaussianRadiusExponentialLipschitzRate.factor M*(L*A)) N h.andE₂.andE₂.andE₂.andE₁ common left right
  exact GaussianEulerCompactModulus.rate_congr _ _ _ _ _ _ _ (by unfold factor GaussianEulerIntegrandParameterContinuity.factor M L; ipra_ring) moved

theorem original_observations (f : PR 2) (p q x z B E T a b A N : PTm n)
    (h : Γ ⊢[PRAAx] input f x z B E T a b A N) : Γ ⊢[PRAAx]
    distanceBounded (ap3 (GaussianNamedEulerIntegrand.evaluatorF f) p (pairT a b) x) (GaussianEulerIntegrandName.sample q z B a b)
      (rateNumerator (factor f x E T*A) N p q) (rateDenominator N p q) :=
  distance_congr (GaussianNamedEulerIntegrand.sample_at f p x a b).eqSymm (GaussianEulerIntegrandName.sample_at q z B a b).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q (original_rate f x z B E T a b A N h))

theorem original_named_fixed_compact_Euler_parameter_rate_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (input f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      independentRate (GaussianNamedEulerIntegrand.nameF f) GaussianEulerIntegrandName.nameF
        (GaussianNamedEulerIntegrand.data f (var 0) (var 5) (var 6)) (GaussianEulerIntegrandName.data (var 1) (var 2) (var 5) (var 6))
        (factor f (var 0) (var 3) (var 4)*var 7) (var 8)) :=
  closeUniv 9 (.impI (original_rate f _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedEulerIntegrandParameterContinuity
