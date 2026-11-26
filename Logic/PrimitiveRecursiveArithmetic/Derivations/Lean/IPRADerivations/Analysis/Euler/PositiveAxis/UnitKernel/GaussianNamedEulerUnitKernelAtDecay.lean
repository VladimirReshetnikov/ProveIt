import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.GaussianNamedEulerUnitKernelAtTime
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.GaussianNamedEulerUnitTimeExponential
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.GaussianEulerUnitDecayInput
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianRealNameExponentialInjectivity

/-!
# The genuine unit kernel at the original decay image

The certified decay name is the original decay with a fixed precision
retiming. Injectivity of the original real exponential identifies its
positive logarithmic time with the original rational time. The genuine
named kernel then agrees with the original Euler power at that time,
with independent requested precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedEulerUnitKernelAtDecay

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitDecayInput (source compactDenominator)
open GaussianNamedEulerUnitTimeExponential (inputF inputData)
open GaussianEulerIntegrandName (powerF powerData decayPoint decayF decayData)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianNameEquivalence (crossEquivalent cross_at cross_trans point_at)
open GaussianRationalMetric (distanceBounded qnegative)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianUnitIntervalInputDecoding (numerator denominator)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRealNameExponentialInjectivity (axisSamples)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

abbrev decayInputF : PR 2 := GaussianEulerUnitDecayInput.nameF
def timeData (a b E T : PTm n) : PTm n :=
  GaussianNamedEulerUnitTime.data (GaussianEulerUnitDecayInput.data a b E T) (compactDenominator E T)

/-- The parameter radius and the unit compact denominator are independent. -/
def kernelData (z R B a b E T : PTm n) : PTm n :=
  GaussianNamedEulerUnitKernel.data (GaussianEulerUnitDecayInput.data a b E T) z R B (compactDenominator E T)
def frozenKernelData (k z B a b E T : PTm n) : PTm n :=
  let q := ap2 decayF (GaussianEulerUnitDecayInput.clock k E T) (decayData a b)
  GaussianEulerUnitSubstitutionKernel.data z B (numerator q) (denominator q)

@[simp] theorem subst_timeData {m : ℕ} (σ : Fin n → PTm m) (a b E T : PTm n) :
    Syn.subst σ (timeData a b E T) = timeData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ E) (Syn.subst σ T) := by simp [timeData]

theorem compact_time_domain (a b E T : PTm n) (h : Γ ⊢[PRAAx] source a b E T) : Γ ⊢[PRAAx]
    GaussianCompactLogarithmBounds.domain a b (compactDenominator E T) (compactDenominator E T) := by
  let G := compactDenominator E T
  have low := h.andE₂.andE₂.andE₂.andE₁
  have high := h.andE₂.andE₂.andE₂.andE₂
  have eG : Γ ⊢[PRAAx] le E G := by
    unfold G compactDenominator
    exact le_of_eq_add (d := two*pw (num 3) T+num 7*E) (by ipra_ring)
  have tExp := le_trans (Γ := Γ) (AnalyticNumberTheory.ZetaFiniteContract.le_pow_self T)
    (pw_le_pw T (le_succ_self two))
  have tG : Γ ⊢[PRAAx] le T G := le_trans tExp
    (le_trans (le_congr (.eqRefl _) (by ipra_ring) (le_add_right (pw (num 3) T) (pw (num 3) T)))
      (GaussianEulerUnitDecayInput.lower_margin_budget E T))
  have aPositive : Γ ⊢[PRAAx] le one a := by
    have bound := le_trans h.andE₁ low
    refine .orE (zero_or_succ a) ?_ ?_
    · have e : (a ≐ zero)::Γ ⊢[PRAAx] E*a ≐ zero :=
        (congrMul (.eqRefl E) Prf.hyp0).eqTrans (mul_zero E)
      have bad : (a ≐ zero)::Γ ⊢[PRAAx] le one zero := le_congr (.eqRefl _) e bound.wk
      exact .botE _ (succ_ne_zero ((monus_zero one).eqSymm.eqTrans bad))
    · exact le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ (pred a))
  exact .andI (.andI aPositive h.andE₁)
    (.andI (le_trans low (mul_le_mul_right a eG)) (le_trans high (mul_le_mul_right b tG)))

private theorem named_time_source (a b E T : PTm n) (h : Γ ⊢[PRAAx] source a b E T) : Γ ⊢[PRAAx]
    GaussianNamedEulerUnitTime.source decayInputF (GaussianEulerUnitDecayInput.data a b E T) (compactDenominator E T) :=
  .andI (GaussianEulerUnitDecayInput.name_regular a b E T) (GaussianEulerUnitDecayInput.admissible_samples a b E T h)

private theorem negative_time_axis (a b E T : PTm n) : Γ ⊢[PRAAx]
    axisSamples (inputF decayInputF) (inputData (GaussianEulerUnitDecayInput.data a b E T) (compactDenominator E T)) := by
  refine .allI ?_
  let x := GaussianEulerUnitDecayInput.data (Syn.shift a) (Syn.shift b) (Syn.shift E) (Syn.shift T)
  let G := compactDenominator (Syn.shift E) (Syn.shift T)
  let r : PTm (n+1) := GaussianFastValueCut.exponent (one+one) (var 0)
  have real := (GaussianNamedEulerUnitTime.sample_real (Γ := Γ.map Fm.shift) decayInputF r x G).andE₂
  simpa only [axisSamples,GaussianNamedEulerUnitTimeExponential.subst_inputData,
    GaussianEulerUnitDecayInput.subst_data,GaussianEulerUnitDecayInput.subst_compactDenominator,
    GaussianNameRingLaws.subst_negativeData,GaussianNamedEulerUnitTime.subst_data,Syn.shift,inputF,inputData,x,G] using
    RationalGaussianEmbedding.axis_congr
      (GaussianRealNameExponentialUnitReflection.negative_sample_at (GaussianNamedEulerUnitTime.nameF decayInputF) (var 0)
        (GaussianNamedEulerUnitTime.data x G)).eqSymm
      (RationalGaussianEmbedding.axis_negative _ real)

private theorem negative_rational_axis (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    axisSamples constantF (decayPoint a b) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hb.shift
  have neg := RationalGaussianEmbedding.axis_congr (GaussianEulerDecayOrder.signed_time_embedding (Syn.shift a) (Syn.shift b) hs)
    (RationalGaussianEmbedding.embed_axis (GaussianEulerDecayOrder.signedTime (Syn.shift a) (Syn.shift b)))
  simpa only [axisSamples,GaussianEulerIntegrandName.subst_decayPoint,Syn.shift] using
    RationalGaussianEmbedding.axis_congr (constant_at (var 0) (decayPoint (Syn.shift a) (Syn.shift b))).eqSymm neg

private theorem negative_time_at_decay (a b E T : PTm n) (h : Γ ⊢[PRAAx] source a b E T) : Γ ⊢[PRAAx]
    crossEquivalent (inputF decayInputF) constantF
      (inputData (GaussianEulerUnitDecayInput.data a b E T) (compactDenominator E T)) (decayPoint a b) := by
  let x := GaussianEulerUnitDecayInput.data a b E T
  let G := compactDenominator E T
  let S := GaussianNameBounds.U constantF (decayPoint a b)
  have hs := named_time_source a b E T h
  have equality := cross_trans _ decayInputF decayF _ x _
    (GaussianNamedEulerUnitTimeExponential.original_recovery decayInputF x G hs)
    (GaussianEulerUnitDecayInput.original_decay a b E T)
  exact GaussianRealNameExponentialInjectivity.independent_radii_injective (inputF decayInputF) constantF G S (inputData x G) (decayPoint a b)
    (GaussianNamedEulerUnitTimeExponential.negative_input decayInputF x G hs)
    (GaussianGammaFiniteApproximantName.exponential_input constantF (decayPoint a b) (constant_regular _))
    (negative_time_axis a b E T) (negative_rational_axis a b h.andE₁) equality

private theorem time_diagonal (p a b E T : PTm n) (h : Γ ⊢[PRAAx] source a b E T) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (GaussianNamedEulerUnitTime.nameF decayInputF) p (timeData a b E T))
      (ap2 constantF p (fraction a b)) (two+two) (unit p) := by
  let F := GaussianNamedEulerUnitTime.nameF decayInputF
  let x := timeData a b E T
  let r := GaussianFastValueCut.exponent (one+one) p
  have hp := unit_positive (Γ := Γ) p
  have hd := positive_product _ _ hp hp
  have hpr := positive_product _ _ hp (unit_positive r)
  have cg : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (fraction a b) :=
    GaussianRationalHorner.ofGaussian_canonical _ _ h.andE₁
  have cx : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (ap2 F r x) :=
    (GaussianNamedEulerUnitTime.sample_real decayInputF r (GaussianEulerUnitDecayInput.data a b E T) (compactDenominator E T)).andE₁
  have neg := cross_at _ _ _ _ p p (negative_time_at_decay a b E T h)
  have n := distance_congr (GaussianRealNameExponentialUnitReflection.negative_sample_at F p x)
    (constant_at p (decayPoint a b)) (.eqRefl _) (.eqRefl _) neg
  have back := distance_congr (GaussianDeterminantSignTransport.negative_involution _ cx)
    (GaussianDeterminantSignTransport.negative_involution _ cg) (.eqRefl _) (.eqRefl _)
    (GaussianNamedDifference.negative_distance _ _ _ _ hd n)
  have last := distance_radius_mono _ _ _ _ two (unit p) hd hp (le_of_eq_add (d := zero) (by ipra_ring)) back
  have first := point_at F x p r (GaussianNamedEulerUnitTime.name_regular _ _ _ (named_time_source a b E T h))
  have grow : Γ ⊢[PRAAx] le (unit p) (unit r) := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have first' := distance_radius_mono _ _ _ _ two (unit p) hpr hp (by ipra_le 𝔞(unit p)*sl grow) first
  exact distance_congr (.eqRefl _) (constant_at p (fraction a b)).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp first' last)

theorem original_time_at_decay (a b E T : PTm n) (h : Γ ⊢[PRAAx] source a b E T) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNamedEulerUnitTime.nameF decayInputF) constantF (timeData a b E T) (fraction a b) := by
  have hreg : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN (GaussianNamedEulerUnitTime.nameF decayInputF) (timeData a b E T) :=
    GaussianNamedEulerUnitTime.name_regular _ _ _ (named_time_source a b E T h)
  refine GaussianNameRingLaws.equivalent_of_envelope (GaussianNamedEulerUnitTime.nameF decayInputF) constantF
    (timeData a b E T) (fraction a b) (two+two) hreg (constant_regular _) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) (Syn.shift E) (Syn.shift T) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,subst_timeData,GaussianPositiveRationalLogarithm.subst_fraction,
    PTm.subst_add,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using
    time_diagonal (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift E) (Syn.shift T) hs

theorem original_kernel_at_decay (z R B a b E T : PTm n) (h : Γ ⊢[PRAAx] source a b E T)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNamedEulerUnitKernel.nameF decayInputF) powerF (kernelData z R B a b E T) (powerData z B a b) :=
  GaussianNamedEulerUnitKernelAtTime.original_kernel_at_time _ _ z R B a b (compactDenominator E T)
    (.andI (GaussianEulerUnitDecayInput.unit_kernel_source z R B a b E T h hB hz)
      (.andI (named_time_source a b E T h) (.andI (compact_time_domain a b E T h) (original_time_at_decay a b E T h))))

private theorem kernel_sample_congr (q z B u v : PTm n) (h : Γ ⊢[PRAAx] u ≐ v) : Γ ⊢[PRAAx]
    ap2 GaussianEulerUnitSubstitutionKernel.nameF q (GaussianEulerUnitSubstitutionKernel.data z B (numerator u) (denominator u)) ≐
      ap2 GaussianEulerUnitSubstitutionKernel.nameF q (GaussianEulerUnitSubstitutionKernel.data z B (numerator v) (denominator v)) := by
  let read (s : PTm 4) := GaussianEulerUnitSubstitutionKernel.data (var 1) (var 2) (numerator s) (denominator s)
  have readback := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (ap2 GaussianEulerUnitSubstitutionKernel.nameF (var 0) (read (var 3)))
    (σ := ![q,z,B,u]) (σ' := ![q,z,B,v]) (fun i => by
      fin_cases i
      exact .eqRefl _
      exact .eqRefl _
      exact .eqRefl _
      exact h)
  simpa only [read,subst_ap2,GaussianEulerUnitSubstitutionKernel.subst_data,
    GaussianUnitIntervalInputDecoding.subst_numerator,GaussianUnitIntervalInputDecoding.subst_denominator,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] using readback

/-- Compare an Euler-power row to the rational unit kernel at a literal original decay sample. -/
theorem original_frozen_image_observations (p q k z R B a b E T : PTm n)
    (h : Γ ⊢[PRAAx] source a b E T) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 powerF p (powerData z B a b))
      (ap2 GaussianEulerUnitSubstitutionKernel.nameF q (frozenKernelData k z B a b E T))
      (rateNumerator (GaussianNamedEulerUnitKernel.lipschitz R (compactDenominator E T)) (unit k) p q)
      (rateDenominator (unit k) p q) := by
  let x := GaussianEulerUnitDecayInput.data a b E T
  let G := compactDenominator E T
  let F := GaussianNamedEulerUnitKernel.nameF decayInputF
  let K := GaussianEulerUnitSubstitutionKernel.nameF
  let y := GaussianNamedEulerUnitKernel.encodedData decayInputF k x z B
  let L := GaussianNamedEulerUnitKernel.lipschitz R G
  have hs := GaussianEulerUnitDecayInput.unit_kernel_source z R B a b E T h hB hz
  have hc := GaussianEulerUnitKernelCompactRate.kernel_source _ _ _ _ _ _
    (GaussianNamedEulerUnitKernel.encoded_source decayInputF k x z R B G hs)
  have reg : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN K y :=
    GaussianEulerUnitSubstitutionKernel.name_regular _ _ _ _ hc
  have close := GaussianNamedRateTransport.observation_error F K powerF K (kernelData z R B a b E T) y
    (powerData z B a b) y L (unit k) p q (unit_positive k)
    (GaussianNamedEulerUnitKernelFrozenRate.original_rate decayInputF k x z R B G hs)
    (GaussianNameEquivalence.cross_symm _ _ _ _ (original_kernel_at_decay z R B a b E T h hB hz))
    (GaussianNameEquivalence.cross_refl K y reg)
  have actual : Γ ⊢[PRAAx] ap2 K q y ≐ ap2 K q (frozenKernelData k z B a b E T) := by
    exact kernel_sample_congr q z B _ _ (GaussianEulerUnitDecayInput.sample_at k a b E T)
  exact distance_congr (.eqRefl _) actual (.eqRefl _) (.eqRefl _) close

theorem actual_named_unit_time_at_original_decay_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent (GaussianNamedEulerUnitTime.nameF decayInputF) constantF
      (timeData (var 0) (var 1) (var 2) (var 3)) (fraction (var 0) (var 1))) :=
  closeUniv 4 (.impI (original_time_at_decay _ _ _ _ Prf.hyp0))

theorem actual_named_unit_kernel_at_original_decay_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((source (var 3) (var 4) (var 5) (var 6) ⋏ (le one (var 2) ⋏ ComplexLogarithmRemainder.bounded (var 0) (var 1*var 2))) ⟶
      crossEquivalent (GaussianNamedEulerUnitKernel.nameF decayInputF) powerF
        (kernelData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) (powerData (var 0) (var 2) (var 3) (var 4))) :=
  closeUniv 7 (.impI (original_kernel_at_decay _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

theorem actual_frozen_decay_image_kernel_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    ((source (var 6) (var 7) (var 8) (var 9) ⋏ (le one (var 5) ⋏ ComplexLogarithmRemainder.bounded (var 3) (var 4*var 5))) ⟶
      distanceBounded (ap2 powerF (var 0) (powerData (var 3) (var 5) (var 6) (var 7)))
        (ap2 GaussianEulerUnitSubstitutionKernel.nameF (var 1) (frozenKernelData (var 2) (var 3) (var 5) (var 6) (var 7) (var 8) (var 9)))
        (rateNumerator (GaussianNamedEulerUnitKernel.lipschitz (var 4) (compactDenominator (var 8) (var 9))) (unit (var 2)) (var 0) (var 1))
        (rateDenominator (unit (var 2)) (var 0) (var 1))) :=
  closeUniv 10 (.impI (original_frozen_image_observations _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedEulerUnitKernelAtDecay
