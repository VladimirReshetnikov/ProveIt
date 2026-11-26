import IPRADerivations.Analysis.Euler.GaussianEulerCompactModulus

/-!
# Parameter continuity of the original Euler integrand on a fixed compact

Two arbitrary rational encodings of the complex parameter retain their
own original multiplication and exponential clocks. At the same time in
[1/E,T], the actual logarithm disk gives a uniform parameter Lipschitz
factor. Finite diagonal error removal preserves the two ordinary output
observation errors. No integrand continuity premise is used.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrandParameterContinuity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerExponentCompactBounds (source clock)
open GaussianCompactLogarithmBounds (domain)
open GaussianEulerIntegrandName (coefficient exponentF exponentData exponent_at)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def factor (R E T : PTm n) : PTm n := GaussianRadiusExponentialLipschitzRate.factor
  (GaussianEulerExponentCompactBounds.radius R E T)*GaussianCompactLogarithmBounds.radius E T
def input (z w R B D E T a b A N : PTm n) : Fm PTm n := source z R B E ⋏
  (source w R D E ⋏ (domain a b E T ⋏ (le one N ⋏ distanceBounded (ofGaussian z B) (ofGaussian w D) A N)))
@[simp] theorem subst_factor {m : ℕ} (σ : Fin n → PTm m) (R E T : PTm n) :
    Syn.subst σ (factor R E T) = factor (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) := by simp [factor]
@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (z w R B D E T a b A N : PTm n) :
    (input z w R B D E T a b A N).subst σ = input (Syn.subst σ z) (Syn.subst σ w) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ a) (Syn.subst σ b)
      (Syn.subst σ A) (Syn.subst σ N) := by simp [input]

theorem coefficient_distance (z w B D A N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A N) : Γ ⊢[PRAAx]
    distanceBounded (coefficient z B) (coefficient w D) A N :=
  GaussianNameRingLaws.sum_left_error _ _ _ _ _ hN h

/-- Both actual coefficient-dependent logarithm clocks remain in the estimate. -/
theorem logarithm_distance (p z w B D a b : PTm n)
    (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) : Γ ⊢[PRAAx]
    distanceBounded (GaussianPositiveRationalLogarithm.sample (clock p z B a b) a b)
      (GaussianPositiveRationalLogarithm.sample (clock p w D a b) a b) two (unit p) := by
  let s := clock p z B a b
  let t := clock p w D a b
  have old := GaussianNameEquivalence.point_at GaussianPositiveRationalLogarithm.logF
    (GaussianPositiveRationalLogarithm.data a b) s t (GaussianPositiveRationalLogarithm.name_regular a b ht)
  have gs := GaussianExponentialReference.unit_monotone (Γ := Γ) (GaussianEulerExponentCompactBounds.clock_later p z B a b)
  have gt := GaussianExponentialReference.unit_monotone (Γ := Γ) (GaussianEulerExponentCompactBounds.clock_later p w D a b)
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive s) (unit_positive t)) (unit_positive p) _ old
  ipra_le 𝔞(unit t)*sl gs+𝔞(unit s)*sl gt

theorem exponent_diagonal (p z w R B D E T a b A N : PTm n)
    (h : Γ ⊢[PRAAx] input z w R B D E T a b A N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 exponentF p (exponentData z B a b)) (ap2 exponentF p (exponentData w D a b))
      ((GaussianCompactLogarithmBounds.radius E T*A)*unit p+(two*(R+one))*N) (N*unit p) := by
  have hN := h.andE₂.andE₂.andE₂.andE₁
  have ht := h.andE₂.andE₂.andE₁
  have den := positive_product _ _ hN (unit_positive p)
  have coeff := distance_radius_mono _ _ _ _ (A*unit p) (N*unit p) hN den
    (le_of_eq_add (d := zero) (by ipra_ring)) (coefficient_distance z w B D A N hN h.andE₂.andE₂.andE₂.andE₂)
  have logs := distance_radius_mono _ _ _ _ (two*N) (N*unit p) (unit_positive p) den
    (le_of_eq_add (d := zero) (by ipra_ring)) (logarithm_distance p z w B D a b ht.andE₁)
  have products := GaussianNameArithmetic.product_distance (coefficient z B) (coefficient w D)
    (GaussianPositiveRationalLogarithm.sample (clock p z B a b) a b)
    (GaussianPositiveRationalLogarithm.sample (clock p w D a b) a b)
    (A*unit p) (two*N) (N*unit p) (GaussianCompactLogarithmBounds.radius E T) (R+one) den coeff logs
    (GaussianCompactLogarithmBounds.sample_bound _ a b E T h.andE₁.andE₂.andE₁ ht)
    (GaussianEulerIntegrandName.coefficient_bound w R D h.andE₂.andE₁.andE₁ h.andE₂.andE₁.andE₂.andE₂)
  have both := GaussianNameRingLaws.sum_left_error _ _ (GaussianEulerIntegrandName.decayPoint a b) _ _ den products
  exact distance_congr (exponent_at p z B a b).eqSymm (exponent_at p w D a b).eqSymm (by ipra_ring) (.eqRefl _) both

theorem exponent_envelope (z w R B D E T a b A N : PTm n)
    (h : Γ ⊢[PRAAx] input z w R B D E T a b A N) : Γ ⊢[PRAAx]
    GaussianNamedLipschitzRate.diagonalEnvelope exponentF exponentF (exponentData z B a b) (exponentData w D a b)
      (GaussianCompactLogarithmBounds.radius E T*A) N (two*(R+one)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift z) (Syn.shift w) (Syn.shift R) (Syn.shift B) (Syn.shift D)
      (Syn.shift E) (Syn.shift T) (Syn.shift a) (Syn.shift b) (Syn.shift A) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa only [GaussianNamedLipschitzRate.diagonalEnvelope,GaussianNamedLipschitzRate.diagonalNumerator,
    GaussianNamedLipschitzRate.diagonalDenominator,GaussianEulerIntegrandName.subst_exponentData,
    GaussianCompactLogarithmBounds.subst_radius,PTm.subst_mul,PTm.subst_add,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using
    exponent_diagonal (var 0) (Syn.shift z) (Syn.shift w) (Syn.shift R) (Syn.shift B) (Syn.shift D)
      (Syn.shift E) (Syn.shift T) (Syn.shift a) (Syn.shift b) (Syn.shift A) (Syn.shift N) hs

theorem exponent_rate (z w R B D E T a b A N : PTm n)
    (h : Γ ⊢[PRAAx] input z w R B D E T a b A N) : Γ ⊢[PRAAx]
    independentRate exponentF exponentF (exponentData z B a b) (exponentData w D a b)
      (GaussianCompactLogarithmBounds.radius E T*A) N :=
  GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ _ h.andE₂.andE₂.andE₂.andE₁
    (GaussianEulerIntegrandName.exponent_regular z B a b (.andI h.andE₁.andE₁ h.andE₂.andE₂.andE₁.andE₁))
    (GaussianEulerIntegrandName.exponent_regular w D a b (.andI h.andE₂.andE₁.andE₁ h.andE₂.andE₂.andE₁.andE₁))
    (exponent_envelope z w R B D E T a b A N h)

/-- SAME original integrand names, arbitrary separate parameter encodings,
and the sharp two independent observation errors. -/
theorem original_rate (z w R B D E T a b A N : PTm n)
    (h : Γ ⊢[PRAAx] input z w R B D E T a b A N) : Γ ⊢[PRAAx]
    independentRate GaussianEulerIntegrandName.nameF GaussianEulerIntegrandName.nameF
      (GaussianEulerIntegrandName.data z B a b) (GaussianEulerIntegrandName.data w D a b) (factor R E T*A) N := by
  let M := GaussianEulerExponentCompactBounds.radius R E T
  let L := GaussianCompactLogarithmBounds.radius E T
  have ca := GaussianEulerExponentCompactBounds.common_exponential_input z R B E T a b h.andE₁ h.andE₂.andE₂.andE₁
  have cw := GaussianEulerExponentCompactBounds.common_exponential_input w R D E T a b h.andE₂.andE₁ h.andE₂.andE₂.andE₁
  have origZ := GaussianEulerIntegrandName.exponent_input z B a b (.andI h.andE₁.andE₁ h.andE₂.andE₂.andE₁.andE₁)
  have origW := GaussianEulerIntegrandName.exponent_input w D a b (.andI h.andE₂.andE₁.andE₁ h.andE₂.andE₂.andE₁.andE₁)
  have common := GaussianRadiusExponentialLipschitzRate.independent_rate exponentF exponentF M
    (exponentData z B a b) (exponentData w D a b) (L*A) N
    (.andI h.andE₂.andE₂.andE₂.andE₁ (.andI ca (.andI cw (exponent_rate z w R B D E T a b A N h))))
  have left := GaussianExponentialRadiusIndependence.independent_radii_proper exponentF exponentF
    (GaussianEulerIntegrandName.radius z B a b) M (exponentData z B a b) (exponentData z B a b) origZ ca
    (GaussianNameEquivalence.cross_refl _ _ origZ.andE₁)
  have right := GaussianExponentialRadiusIndependence.independent_radii_proper exponentF exponentF
    (GaussianEulerIntegrandName.radius w D a b) M (exponentData w D a b) (exponentData w D a b) origW cw
    (GaussianNameEquivalence.cross_refl _ _ origW.andE₁)
  have moved := GaussianNamedRateTransport.transport (GaussianRadiusExponentialName.nameF exponentF) (GaussianRadiusExponentialName.nameF exponentF)
    GaussianEulerIntegrandName.nameF GaussianEulerIntegrandName.nameF (GaussianRadiusExponentialName.data M (exponentData z B a b))
    (GaussianRadiusExponentialName.data M (exponentData w D a b)) (GaussianEulerIntegrandName.data z B a b) (GaussianEulerIntegrandName.data w D a b)
    (GaussianRadiusExponentialLipschitzRate.factor M*(L*A)) N h.andE₂.andE₂.andE₂.andE₁ common left right
  exact GaussianEulerCompactModulus.rate_congr _ _ _ _ _ _ _ (by unfold factor M L; ipra_ring) moved

theorem original_observations (p q z w R B D E T a b A N : PTm n)
    (h : Γ ⊢[PRAAx] input z w R B D E T a b A N) : Γ ⊢[PRAAx]
    distanceBounded (GaussianEulerIntegrandName.sample p z B a b) (GaussianEulerIntegrandName.sample q w D a b)
      (rateNumerator (factor R E T*A) N p q) (rateDenominator N p q) :=
  distance_congr (GaussianEulerIntegrandName.sample_at p z B a b).eqSymm (GaussianEulerIntegrandName.sample_at q w D a b).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q (original_rate z w R B D E T a b A N h))

theorem original_fixed_compact_Euler_parameter_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
      independentRate GaussianEulerIntegrandName.nameF GaussianEulerIntegrandName.nameF
        (GaussianEulerIntegrandName.data (var 0) (var 3) (var 7) (var 8)) (GaussianEulerIntegrandName.data (var 1) (var 4) (var 7) (var 8))
        (factor (var 2) (var 5) (var 6)*var 9) (var 10)) :=
  closeUniv 11 (.impI (original_rate _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))
theorem original_fixed_compact_Euler_parameter_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
    (input (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) ⟶
      distanceBounded (GaussianEulerIntegrandName.sample (var 0) (var 2) (var 5) (var 9) (var 10))
        (GaussianEulerIntegrandName.sample (var 1) (var 3) (var 6) (var 9) (var 10))
        (rateNumerator (factor (var 4) (var 7) (var 8)*var 11) (var 12) (var 0) (var 1)) (rateDenominator (var 12) (var 0) (var 1))) :=
  closeUniv 13 (.impI (original_observations _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrandParameterContinuity
