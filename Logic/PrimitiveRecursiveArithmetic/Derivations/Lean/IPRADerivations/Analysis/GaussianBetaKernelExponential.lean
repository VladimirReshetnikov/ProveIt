import IPRADerivations.Analysis.GaussianBetaKernelLogarithm
import IPRADerivations.Analysis.GaussianLocalLogarithmExponentialIdentity
import IPRADerivations.Analysis.GaussianBoundedIntegerExponential
import IPRADerivations.Analysis.GaussianRadiusExponentialLipschitzRate

/-!
# Actual exponential representation of the finite beta kernel

Original local C4 and the true bounded integer-exponential theorem bind
the literal power (1-a/(bN))^N to exp(N log(1-a/(bN))). The compact
logarithm rate then controls the original exp(-a/b) with a radius bound
independent of N. Only the original rational time and compact guards are
used; no kernel identity, variation, or output law is supplied.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaKernelExponential

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBetaKernelLogarithm (source negativeNumerator localData target radius)
open GaussianRationalHorner (qadd ofGaussian positive_product)
open GaussianRationalSyntheticDivision (qone)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (power)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm cross_at)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def base (a b N : PTm n) : PTm n := qadd qone (ofGaussian (negativeNumerator a) (b*N))
def kernel (a b N : PTm n) : PTm n := power (base a b N) N
def expF : PR 2 := GaussianRadiusExponentialName.nameF GaussianBetaKernelLogarithm.nameF
def expData (a b N T : PTm n) : PTm n := GaussianRadiusExponentialName.data (radius T) (GaussianBetaKernelLogarithm.data a b N)
def decayData (a b T : PTm n) : PTm n := GaussianRadiusExponentialName.data (radius T) (GaussianEulerIntegrandName.decayPoint a b)
def constantBound (_a b N : PTm n) : PTm n := b*b*N

@[simp] theorem subst_base {m : ℕ} (σ : Fin n → PTm m) (a b N : PTm n) :
    Syn.subst σ (base a b N) = base (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by simp [base]
@[simp] theorem subst_kernel {m : ℕ} (σ : Fin n → PTm m) (a b N : PTm n) :
    Syn.subst σ (kernel a b N) = kernel (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by simp [kernel]
@[simp] theorem subst_expData {m : ℕ} (σ : Fin n → PTm m) (a b N T : PTm n) :
    Syn.subst σ (expData a b N T) = expData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) (Syn.subst σ T) := by simp [expData]
@[simp] theorem subst_decayData {m : ℕ} (σ : Fin n → PTm m) (a b T : PTm n) :
    Syn.subst σ (decayData a b T) = decayData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ T) := by simp [decayData,GaussianEulerIntegrandName.decayPoint]
@[simp] theorem subst_constantBound {m : ℕ} (σ : Fin n → PTm m) (a b N : PTm n) :
    Syn.subst σ (constantBound a b N) = constantBound (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by simp [constantBound]

@[simp] theorem subst_originalDecayData {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (GaussianEulerIntegrandName.decayData a b) = GaussianEulerIntegrandName.decayData (Syn.subst σ a) (Syn.subst σ b) := by
  simp [GaussianEulerIntegrandName.decayData,GaussianGammaFiniteApproximantName.exponentialInputData]

theorem original_subtraction_base (a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    base a b N ≐ qsub qone (GaussianPositiveRationalLogarithm.fraction a (b*N)) :=
  GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _)
    (GaussianBetaKernelLogarithm.target_is_original_decay a (b*N) (positive_product _ _ h.andE₁ h.andE₂.andE₁))

theorem linear_constant_cross (w : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent GaussianFiniteLogarithmCompositionName.constantF constantF w (GaussianFiniteLogarithmCompositionTail.linearValue w) := by
  refine .allI (.allI ?_)
  let u : PTm (n+2) := Syn.shift (Syn.shift w)
  let D : PTm (n+2) := unit (var 1)*unit (var 0)
  have d := positive_product (Γ := (Γ.map Fm.shift).map Fm.shift) _ _ (unit_positive (var 1)) (unit_positive (var 0))
  have exactPoint := GaussianRationalPowerDifference.distance_refl_zero (Γ := (Γ.map Fm.shift).map Fm.shift)
    (GaussianFiniteLogarithmCompositionTail.linearValue u) D d
  have grown := distance_radius_mono _ _ _ _ (unit (var 1)+unit (var 0)) D d d (le_of_eq_add (d := (unit (var 1)+unit (var 0))*D) (by dsimp only [D]; ipra_ring)) exactPoint
  simpa only [crossEquivalent,Syn.shift,GaussianFiniteLogarithmCompositionTail.subst_linearValue,
    GaussianFiniteLogarithmCompositionName.constant,u,D] using
    distance_congr (GaussianFiniteLogarithmCompositionName.constant_at (var 1) u).eqSymm
      (constant_at (var 0) (GaussianFiniteLogarithmCompositionTail.linearValue u)).eqSymm (.eqRefl _) (.eqRefl _) grown

theorem local_input (a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input GaussianLocalLogarithmName.pointF one (localData a b N) :=
  GaussianExponentialRadiusIndependence.radius_one_input _ _ (GaussianLocalLogarithmName.original_exponential_input _ _ _
    (GaussianBetaKernelLogarithm.local_source a b N h))

theorem base_exponential (a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianRadiusExponentialName.nameF GaussianLocalLogarithmName.pointF) constantF
      (GaussianRadiusExponentialName.data one (localData a b N)) (base a b N) := by
  have src := GaussianBetaKernelLogarithm.local_source a b N h
  have inp := GaussianLocalLogarithmName.original_exponential_input _ _ _ src
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (GaussianExponentialRadiusIndependence.original_unit_cross _ _ inp))
    (cross_trans _ _ _ _ _ _ (GaussianLocalLogarithmExponentialIdentity.source_cross _ _ _ src)
      (linear_constant_cross (ofGaussian (negativeNumerator a) (b*N))))

theorem base_bound (a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx] bounded (base a b N) two one :=
  GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (GaussianRationalReciprocal.bounded_sum _ _ _ _ _ _ (le_refl one) (le_refl one)
      GaussianRationalReciprocal.qone_bounded (GaussianLocalLogarithmLinearRemainder.linear_unit_bound _ _ _
        (GaussianBetaKernelLogarithm.local_source a b N h)))

theorem integer_input (a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    GaussianBoundedIntegerExponentialStages.input GaussianLocalLogarithmName.pointF one (localData a b N) (base a b N) two :=
  .andI (local_input a b N h) (.andI (base_exponential a b N h) (base_bound a b N h))

/-- Exact finite kernel identity at the compact exponential radius.
The radius-dependent representation is transported through actual names. -/
theorem original_kernel_exponential (a b N T : PTm n) (h : Γ ⊢[PRAAx] source a b N) (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    crossEquivalent expF constantF (expData a b N T) (kernel a b N) :=
  cross_trans _ _ _ _ _ _
    (GaussianExponentialRadiusIndependence.same_input_cross GaussianBetaKernelLogarithm.nameF (radius T)
      (GaussianNamedNaturalScale.radius N one) (GaussianBetaKernelLogarithm.data a b N)
      (GaussianBetaKernelLogarithm.compact_input a b N T h ht)
      (GaussianNamedNaturalScale.exponential_input _ N N one (localData a b N) (local_input a b N h) (le_refl N)))
    (GaussianBoundedIntegerExponential.integer_power_cross _ N one (localData a b N) (base a b N) two (integer_input a b N h))

theorem constant_input (q R : PTm n) (hq : Γ ⊢[PRAAx] bounded q R one) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input constantF R q := by
  refine .andI (constant_regular q) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift q) (Syn.shift R) one := by simpa [Fm.shift,Syn.shift] using hq.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples] using
    GaussianRationalReciprocal.bound_congr (constant_at (var 0) (Syn.shift q)).eqSymm (.eqRefl _) (.eqRefl _) hs

theorem decay_input (a b N T : PTm n) (h : Γ ⊢[PRAAx] source a b N) (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input constantF (radius T) (GaussianEulerIntegrandName.decayPoint a b) := by
  have targetBound := GaussianRationalReciprocal.bound_congr
    (GaussianBetaKernelLogarithm.target_is_original_decay a b h.andE₁) (.eqRefl _) (.eqRefl _)
    (GaussianBetaKernelLogarithm.target_bound a b T h.andE₁ ht)
  exact constant_input _ _ (GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) (le_of_eq_add (d := T+one) (by unfold radius; ipra_ring))) targetBound)

theorem logarithm_rate (a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    GaussianNamedInverseRate.independentRate GaussianBetaKernelLogarithm.nameF constantF
      (GaussianBetaKernelLogarithm.data a b N) (GaussianEulerIntegrandName.decayPoint a b) (a*a) (constantBound a b N) := by
  have den := positive_product (Γ := Γ) _ _ (positive_product _ _ h.andE₁ h.andE₁) h.andE₂.andE₁
  apply GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ one den
    (GaussianBetaKernelLogarithm.name_regular a b N h) (constant_regular _)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using h.shift
  have e := (GaussianBetaKernelLogarithm.target_is_original_decay (Γ := Γ.map Fm.shift) (Syn.shift a) (Syn.shift b) hs.andE₁).eqTrans
    (constant_at (var 0) (GaussianEulerIntegrandName.decayPoint (Syn.shift a) (Syn.shift b))).eqSymm
  simpa only [GaussianNamedLipschitzRate.diagonalEnvelope,GaussianNamedLipschitzRate.diagonalNumerator,
    GaussianNamedLipschitzRate.diagonalDenominator,GaussianBetaKernelLogarithm.observation,Syn.shift,
    GaussianBetaKernelLogarithm.subst_data,GaussianEulerIntegrandName.subst_decayPoint,PTm.subst_mul,constantBound] using
    distance_congr (.eqRefl _) e (by simp only [Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]; ipra_ring) (.eqRefl _)
      (GaussianBetaKernelLogarithm.original_logarithm_rate (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift N) hs)

theorem exponential_rate_input (a b N T : PTm n) (h : Γ ⊢[PRAAx] source a b N) (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialLipschitzRate.input GaussianBetaKernelLogarithm.nameF constantF (radius T)
      (GaussianBetaKernelLogarithm.data a b N) (GaussianEulerIntegrandName.decayPoint a b) (a*a) (constantBound a b N) :=
  .andI (positive_product _ _ (positive_product _ _ h.andE₁ h.andE₁) h.andE₂.andE₁)
    (.andI (GaussianBetaKernelLogarithm.compact_input a b N T h ht) (.andI (decay_input a b N T h ht) (logarithm_rate a b N h)))

theorem original_decay_cross (a b N T : PTm n) (h : Γ ⊢[PRAAx] source a b N) (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    crossEquivalent GaussianEulerIntegrandName.decayF GaussianEulerIntegrandName.decayF
      (decayData a b T) (GaussianEulerIntegrandName.decayData a b) :=
  GaussianExponentialRadiusIndependence.same_input_cross constantF (radius T)
    (GaussianNameBounds.U constantF (GaussianEulerIntegrandName.decayPoint a b)) (GaussianEulerIntegrandName.decayPoint a b)
    (decay_input a b N T h ht)
    (GaussianGammaFiniteApproximantName.exponential_input constantF _ (constant_regular _))

def coefficient (T : PTm n) : PTm n := GaussianRadiusExponentialLipschitzRate.factor (radius T)
def errorNumerator (p a b N T : PTm n) : PTm n := coefficient T*a*a*unit p+constantBound a b N
def errorDenominator (p a b N : PTm n) : PTm n := constantBound a b N*unit p
@[simp] theorem subst_coefficient {m : ℕ} (σ : Fin n → PTm m) (T : PTm n) :
    Syn.subst σ (coefficient T) = coefficient (Syn.subst σ T) := by simp [coefficient]
@[simp] theorem subst_errorNumerator {m : ℕ} (σ : Fin n → PTm m) (p a b N T : PTm n) :
    Syn.subst σ (errorNumerator p a b N T) = errorNumerator (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) (Syn.subst σ T) := by simp [errorNumerator]
@[simp] theorem subst_errorDenominator {m : ℕ} (σ : Fin n → PTm m) (p a b N : PTm n) :
    Syn.subst σ (errorDenominator p a b N) = errorDenominator (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by simp [errorDenominator]

theorem diagonal_kernel_rate (p a b N T : PTm n) (h : Γ ⊢[PRAAx] source a b N) (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 constantF p (kernel a b N)) (ap2 GaussianEulerIntegrandName.decayF p (GaussianEulerIntegrandName.decayData a b))
      (coefficient T*a*a*unit p+num 6*constantBound a b N) (constantBound a b N*unit p) := by
  let U := unit p
  let D := constantBound a b N*U
  have u := unit_positive (Γ := Γ) p
  have n := positive_product (Γ := Γ) _ _ (positive_product _ _ h.andE₁ h.andE₁) h.andE₂.andE₁
  have d : Γ ⊢[PRAAx] le one D := positive_product _ _ n u
  have uu := positive_product (Γ := Γ) _ _ u u
  have firstRaw := distance_symmetric _ _ _ _ uu (cross_at _ _ _ _ p p (original_kernel_exponential a b N T h ht))
  have first := distance_radius_mono _ _ _ _ (two*constantBound a b N) D uu d
    (le_of_eq_add (d := zero) (by dsimp only [D,U]; ipra_ring)) firstRaw
  have middleRaw := GaussianRadiusExponentialLipschitzRate.observations GaussianBetaKernelLogarithm.nameF constantF
    (radius T) _ _ (a*a) (constantBound a b N) p p (exponential_rate_input a b N T h ht)
  have middle := distance_radius_mono _ _ _ _ (coefficient T*a*a*U+two*constantBound a b N) D
    (positive_product _ _ (positive_product _ _ n u) u) d
    (le_of_eq_add (d := zero) (by dsimp only [GaussianNamedInverseRate.rateNumerator,GaussianNamedInverseRate.rateDenominator,D,U,coefficient,constantBound]; ipra_ring)) middleRaw
  have lastRaw := cross_at _ _ _ _ p p (original_decay_cross a b N T h ht)
  have last := distance_radius_mono _ _ _ _ (two*constantBound a b N) D uu d
    (le_of_eq_add (d := zero) (by dsimp only [D,U]; ipra_ring)) lastRaw
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ d (distance_triangle_same _ _ _ _ _ _ d first middle) last)

theorem kernel_rate (a b N T : PTm n) (h : Γ ⊢[PRAAx] source a b N) (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    GaussianNamedInverseRate.independentRate constantF GaussianEulerIntegrandName.decayF (kernel a b N) (GaussianEulerIntegrandName.decayData a b)
      (coefficient T*a*a) (constantBound a b N) := by
  have n := positive_product (Γ := Γ) _ _ (positive_product _ _ h.andE₁ h.andE₁) h.andE₂.andE₁
  apply GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ (num 6) n (constant_regular _)
    (GaussianRadiusExponentialName.name_regular constantF _ _
      (GaussianGammaFiniteApproximantName.exponential_input constantF _ (constant_regular _)))
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using h.shift
  have ts : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a) (Syn.shift T*Syn.shift b) := by simpa [Fm.shift,Syn.shift] using ht.shift
  simpa [GaussianNamedLipschitzRate.diagonalEnvelope,GaussianNamedLipschitzRate.diagonalNumerator,
    GaussianNamedLipschitzRate.diagonalDenominator,GaussianEulerIntegrandName.decayF,
    GaussianEulerIntegrandName.decayData,GaussianGammaFiniteApproximantName.exponentialInputData,constantBound,Syn.shift] using
    diagonal_kernel_rate (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift N) (Syn.shift T) hs ts

/-- One actual finite query removes the constant kernel's superfluous
precision error, keeping only the requested original decay observation. -/
theorem decay_sample_slack (p t a b N T : PTm n) (h : Γ ⊢[PRAAx] source a b N) (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (kernel a b N) (ap2 GaussianEulerIntegrandName.decayF p (GaussianEulerIntegrandName.decayData a b)))
      (errorNumerator p a b N T) (errorDenominator p a b N) one t := by
  have old := GaussianNamedInverseRate.rate_at _ _ _ _ _ _ t p (kernel_rate a b N T h ht)
  exact distance_congr (constant_at t (kernel a b N)) (.eqRefl _)
    (by unfold GaussianNamedInverseRate.rateNumerator errorNumerator errorDenominator unit; ipra_ring)
    (by unfold GaussianNamedInverseRate.rateDenominator errorDenominator unit; ipra_ring) old

theorem original_decay_sample_bound (p a b N T : PTm n) (h : Γ ⊢[PRAAx] source a b N) (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    distanceBounded (kernel a b N) (ap2 GaussianEulerIntegrandName.decayF p (GaussianEulerIntegrandName.decayData a b))
      (errorNumerator p a b N T) (errorDenominator p a b N) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ one
    (positive_product _ _ (positive_product _ _ (positive_product _ _ h.andE₁ h.andE₁) h.andE₂.andE₁) (unit_positive p))
    (decay_sample_slack p (GaussianRationalSlackRemoval.precision
      (qsub (kernel a b N) (ap2 GaussianEulerIntegrandName.decayF p (GaussianEulerIntegrandName.decayData a b)))
      (errorNumerator p a b N T) (errorDenominator p a b N) one) a b N T h ht)

theorem original_kernel_power (a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    kernel a b N ≐ power (qsub qone (GaussianPositiveRationalLogarithm.fraction a (b*N))) N :=
  congrAp2 GaussianRationalReciprocal.powerF (.eqRefl N) (original_subtraction_base a b N h)

def output (p a b N T : PTm n) : PTm n := pairT (kernel a b N)
  (pairT (ap2 GaussianEulerIntegrandName.decayF p (GaussianEulerIntegrandName.decayData a b))
    (pairT (errorNumerator p a b N T) (errorDenominator p a b N)))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (p a b N T : PTm n) : PTm n := PTm.app outputF ![p,a,b,N,T]
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (p a b N T : PTm n) :
    Syn.subst σ (output p a b N T) = output (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) (Syn.subst σ T) := by simp [output]
theorem program_at (p a b N T : PTm n) : Γ ⊢[PRAAx] run p a b N T ≐ output p a b N T := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![p,a,b,N,T]
theorem returned_kernel (p a b N T : PTm n) : Γ ⊢[PRAAx] fstT (run p a b N T) ≐ kernel a b N :=
  (congrFst (program_at p a b N T)).eqTrans (fst_pair _ _)
theorem returned_tail (p a b N T : PTm n) : Γ ⊢[PRAAx] sndT (run p a b N T) ≐
    pairT (ap2 GaussianEulerIntegrandName.decayF p (GaussianEulerIntegrandName.decayData a b)) (pairT (errorNumerator p a b N T) (errorDenominator p a b N)) :=
  (congrSnd (program_at p a b N T)).eqTrans (snd_pair _ _)
theorem returned_decay (p a b N T : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run p a b N T)) ≐
    ap2 GaussianEulerIntegrandName.decayF p (GaussianEulerIntegrandName.decayData a b) :=
  (congrFst (returned_tail p a b N T)).eqTrans (fst_pair _ _)
theorem returned_last (p a b N T : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run p a b N T)) ≐ pairT (errorNumerator p a b N T) (errorDenominator p a b N) :=
  (congrSnd (returned_tail p a b N T)).eqTrans (snd_pair _ _)
theorem returned_numerator (p a b N T : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run p a b N T))) ≐ errorNumerator p a b N T :=
  (congrFst (returned_last p a b N T)).eqTrans (fst_pair _ _)
theorem returned_denominator (p a b N T : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run p a b N T))) ≐ errorDenominator p a b N :=
  (congrSnd (returned_last p a b N T)).eqTrans (snd_pair _ _)
theorem returned_comparison (p a b N T : PTm n) (h : Γ ⊢[PRAAx] source a b N) (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    distanceBounded (fstT (run p a b N T)) (fstT (sndT (run p a b N T)))
      (fstT (sndT (sndT (run p a b N T)))) (sndT (sndT (sndT (run p a b N T)))) :=
  distance_congr (returned_kernel p a b N T).eqSymm (returned_decay p a b N T).eqSymm
    (returned_numerator p a b N T).eqSymm (returned_denominator p a b N T).eqSymm (original_decay_sample_bound p a b N T h ht)

theorem actual_original_beta_subtraction_kernel_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ kernel (var 0) (var 1) (var 2) ≐
      power (qsub qone (GaussianPositiveRationalLogarithm.fraction (var 0) (var 1*var 2))) (var 2)) :=
  closeUniv 3 (.impI (original_kernel_power _ _ _ Prf.hyp0))
theorem actual_original_beta_kernel_exponential_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((source (var 0) (var 1) (var 2) ⋏ le (var 0) (var 3*var 1)) ⟶
      crossEquivalent expF constantF (expData (var 0) (var 1) (var 2) (var 3)) (kernel (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.impI (original_kernel_exponential _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem original_beta_kernel_compact_decay_approximation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((source (var 1) (var 2) (var 3) ⋏ le (var 1) (var 4*var 2)) ⟶ distanceBounded
      (kernel (var 1) (var 2) (var 3)) (ap2 GaussianEulerIntegrandName.decayF (var 0) (GaussianEulerIntegrandName.decayData (var 1) (var 2)))
      (errorNumerator (var 0) (var 1) (var 2) (var 3) (var 4)) (errorDenominator (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 5 (.impI (original_decay_sample_bound _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem actual_beta_kernel_approximation_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_beta_kernel_decay_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((source (var 1) (var 2) (var 3) ⋏ le (var 1) (var 4*var 2)) ⟶ distanceBounded
      (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4))) (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))
      (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))) (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))))) :=
  closeUniv 5 (.impI (returned_comparison _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaKernelExponential
