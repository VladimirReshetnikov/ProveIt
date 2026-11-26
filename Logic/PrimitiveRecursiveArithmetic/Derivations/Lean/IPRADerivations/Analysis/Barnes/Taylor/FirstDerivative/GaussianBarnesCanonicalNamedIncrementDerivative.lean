import IPRADerivations.Analysis.Barnes.Names.GaussianBarnesCanonicalNamedIncrementEndpoints
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalNamedValueDerivative
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalDerivativeIncrementPrecision

/-!
# The original Barnes quotient along an apart regular Gaussian step

Read the two original endpoints and the step at synchronized clocks.
Compare the actual named quotient with the exact native quotient on
the shared rational chart, where the small-step rate is available.
The resulting precision bound is independent of the apartness
certificate, although the chosen late read uses that certificate.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedIncrementDerivative

open_ipra
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalNamedDemand (source native_source)
open GaussianBarnesCanonicalNamedFrozen (source_widen)
open GaussianBarnesCanonicalNamedIncrementEndpoints (nativeClock native_clock_later observation)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianFastValueCut (exponent)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNamedIncrementChart (baseNumerator stepNumerator denominator step_separated)
open GaussianNamedIncrementQuotientFrozenRate (differenceCap commonNumerator common_precision_rate late_separated)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRateComposition (same_denominator symmetric)
open GaussianRationalL1 (rawGaussian rawDen)
open GaussianRationalMetric (bounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "B" => GaussianBarnesCanonicalNamed.nameF
local notation "bd" => GaussianBarnesCanonicalNamedDemand.data
local notation "C" => GaussianBarnesCanonicalNamedValueDerivative.nameF
local notation "cd" => GaussianBarnesCanonicalNamedValueDerivative.data
local notation "cdClock" => GaussianBarnesCanonicalNamedValueDerivative.clock
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data
local notation "D" => GaussianBarnesCanonicalValueDerivative.nameF
local notation "dd" => GaussianBarnesCanonicalValueDerivative.data
local notation "Q" => GaussianBarnesCanonicalValueDerivative.quotientF
local notation "qd" => GaussianBarnesCanonicalValueDerivative.quotientData

def stepSamples (K : PR 2) (y M : PTm n) : Fm PTm n :=
  .all (bounded (ap2 K (var 0) (Syn.shift y)) one (Syn.shift M))

@[simp] theorem subst_stepSamples {m : ℕ} (σ : Fin n → PTm m) (K : PR 2) (y M : PTm n) :
    (stepSamples K y M).subst σ = stepSamples K (Syn.subst σ y) (Syn.subst σ M) := by
  simp [stepSamples,Syn.subst_shift,Syn.shift_subst,one]

def stepClock (R p : PTm n) : PTm n :=
  GaussianBarnesCanonicalDerivativeIncrementPrecision.inputClock (R+one) (p+two)

def input (F K : PR 2) (p x y R a : PTm n) : Fm PTm n :=
  source F x R ⋏ (GaussianNameReciprocal.input K a y ⋏ stepSamples K y (unit (stepClock R p)))

def nameF (F K : PR 2) : PR 2 := GaussianNamedIncrementDifferenceQuotient.nameF (B (addF F K)) (B F) K

def data (F K : PR 2) (x y R a : PTm n) : PTm n :=
  GaussianNamedIncrementDifferenceQuotient.data (B (addF F K)) (B F) K (bd (addData x y) (R+one)) (bd x (R+one)) y a

theorem step_at (K : PR 2) (y M k : PTm n) (h : Γ ⊢[PRAAx] stepSamples K y M) :
    Γ ⊢[PRAAx] bounded (ap2 K k y) one M := by
  simpa [stepSamples,one] using h.allE k

theorem step_source (K : PR 2) (y M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hK : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN K y) (h : Γ ⊢[PRAAx] stepSamples K y M) :
    Γ ⊢[PRAAx] source K y one := by
  refine .andI hK (.allI ?_)
  let sh (u : PTm n) := Syn.shift u
  let Δ := Γ.map Fm.shift
  have hm : Δ ⊢[PRAAx] le one (sh M) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hM.shift
  have hs : Δ ⊢[PRAAx] stepSamples K (sh y) (sh M) :=
    by simpa only [subst_stepSamples,Fm.shift,Syn.shift,sh,Δ] using h.shift
  have d := step_at K (sh y) (sh M) (var 0) hs
  have fit : Δ ⊢[PRAAx] le (one*one) (one*sh M) :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right one hm)
  simpa only [GaussianRootApproximationWitness.pointBounds,Syn.shift,sh,Δ,one,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    bounded_radius_mono _ _ _ _ _ hm (le_refl one) fit d

private theorem rational_derivative_cross (F K : PR 2) (k x y R : PTm n) (hf : Γ ⊢[PRAAx] source F x R) :
    Γ ⊢[PRAAx] crossEquivalent D D
      (dd (baseNumerator (observation F k x) (observation K k y)) (R+one)
        (denominator (observation F k x) (observation K k y)))
      (GaussianBarnesCanonicalNamedValueDerivative.frozenData F (nativeClock k) x R) := by
  let q := observation F k x
  let r := observation K k y
  let S := R+one
  have hfS := source_widen F x R S hf (le_add_right R one)
  have same := GaussianBarnesCanonicalValueDerivativeProperness.proper (baseNumerator q r) (rawGaussian q) S
    (denominator q r) (rawDen q)
    (GaussianBarnesCanonicalNamedIncrementEndpoints.base_chart_source F K k x y R hf)
    (native_source F (nativeClock k) x S hfS) (GaussianNamedIncrementChart.base_fraction q r)
  have widen : Γ ⊢[PRAAx] dd (rawGaussian q) S (rawDen q) ≐ dd (rawGaussian q) (succ R) (rawDen q) := by
    have eq := (succ_eq_add_one (Γ := Γ) R).eqSymm
    simpa only [GaussianBarnesCanonicalDerivativeDiskIndependence.subst_data,Syn.subst_inst_shift,Syn.subst_var,Syn.inst_zero] using
      Prf.eqCongr1 (dd (Syn.shift (rawGaussian q)) (var 0) (Syn.shift (rawDen q))) eq
  exact GaussianGammaCompactCutoffAlignment.cross_data_congr D D _ _ _ _ (.eqRefl _) widen same

theorem rate (F K : PR 2) (p x y R a : PTm n) (hs : Γ ⊢[PRAAx] input F K p x y R a) :
    Γ ⊢[PRAAx] independentRate (nameF F K) (C F) (data F K x y R a) (cd x R) one (unit p) := by
  let S := R+one
  let F₀ := B F
  let F₁ := B (addF F K)
  let x₀ := bd x S
  let x₁ := bd (addData x y) S
  let E := commonNumerator a one one (differenceCap F₁ F₀ x₁ x₀)
  let s := p+two
  let U := unit s
  let t := exponent E s
  let d := GaussianBarnesCanonicalNamed.clock t S
  let c := cdClock s R
  let b := GaussianNameReciprocal.anchor a
  let k := d+c+(b+t)
  let j := nativeClock k
  let q := observation F k x
  let r := observation K k y
  let z := baseNumerator q r
  let h := stepNumerator q r
  let M := denominator q r
  let x' := vd (add z h) S M
  let y' := vd z S M
  let v := dd z S M
  have hf := hs.andE₁
  have hfS := source_widen F x R S hf (le_add_right _ _)
  have hK := hs.andE₂.andE₁
  have hsmall := hs.andE₂.andE₂
  have hU := unit_positive (Γ := Γ) s
  have hStepU := unit_positive (Γ := Γ) (stepClock R p)
  have step := step_source K y _ hStepU hK.andE₁ hsmall
  have shifted := GaussianBarnesCanonicalNamedIncrementEndpoints.shifted_source F K x y R hf step
  have late := native_clock_later (Γ := Γ) k
  have hd : Γ ⊢[PRAAx] le d k := le_trans (le_add_right _ _) (le_add_right _ _)
  have hc : Γ ⊢[PRAAx] le c j := le_trans (le_add_left _ _) (le_trans (le_add_right _ _) late)
  have ht : Γ ⊢[PRAAx] le t j := le_trans (le_add_left _ _) (le_trans (le_add_left _ _) late)
  have hb : Γ ⊢[PRAAx] le b j := le_trans (le_add_right _ _) (le_trans (le_add_left _ _) late)
  have endpts := GaussianBarnesCanonicalNamedIncrementEndpoints.rates F K t k x y R S hf hfS step hd (le_trans hd late)
  have chart := GaussianBarnesCanonicalNamedIncrementEndpoints.chart_sources F K k x y R hf step
  have n₀ := GaussianBarnesCanonicalValue.regular z S M chart.andE₁
  have n₁ := GaussianBarnesCanonicalValue.regular (add z h) S M chart.andE₂
  have nr := late_separated K a y j hK hb
  have sep := step_separated q r nr.andE₂
  have size := GaussianNamedIncrementChart.step_norm1_bound q r one (unit (stepClock R p)) hStepU
    (step_at K y _ j hsmall)
  have small : Γ ⊢[PRAAx] le (GaussianL1.norm1 h*unit (stepClock R p)) (two*M) :=
    le_congr (.eqRefl _) (by change Γ ⊢[PRAAx] two*one*denominator q r ≐ two*denominator q r; ipra_ring) size
  have rational := GaussianBarnesCanonicalDerivativeIncrementPrecision.rate s z h S M chart.andE₁ chart.andE₂ sep.andE₂ small
  have lf := GaussianBarnesCanonicalNamed.name_regular (addF F K) (addData x y) S shifted
  have rf := GaussianBarnesCanonicalNamed.name_regular F x S hfS
  have ar := common_precision_rate F₁ F₀ V V K x₁ x₀ x' y' y a j t one one
    (.andI lf (.andI rf hK)) n₁ n₀ hb ht endpts.andE₁ endpts.andE₂
  have shrunk := GaussianEulerNamedPowerScalingPowerFrozen.unit_rate_after _ _ _ _ E t s (le_refl _) ar
  have nativeEq := GaussianBarnesCanonicalNamedIncrementEndpoints.native_quotient_data_equal (Γ := Γ) F K V V k x y x' y'
  have qn := GaussianNamedDifferenceQuotient.name_regular V V x' y' h M (.andI n₁ (.andI n₀ sep))
  have qa := GaussianNamedIncrementDifferenceQuotient.name_regular F₁ F₀ K x₁ x₀ y a (.andI lf (.andI rf hK))
  have first := GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ hU shrunk
    (cross_refl _ _ qa)
    (GaussianGammaCompactCutoffAlignment.cross_data_congr Q Q (qd z h S M) (qd z h S M) (qd z h S M) _
      (.eqRefl _) nativeEq.eqSymm (cross_refl _ _ qn))
  have frozen := GaussianBarnesCanonicalNamedValueDerivative.frozen_rate F s j x R hf hc
  have last := GaussianNamedRateTransport.transport (C F) D (C F) D (cd x R) _ (cd x R) v one U hU frozen
    (cross_refl _ _ (GaussianBarnesCanonicalNamedValueDerivative.regular F x R hf))
    (rational_derivative_cross F K k x y R hf)
  have both := same_denominator (nameF F K) Q D (data F K x y R a) (qd z h S M) v one U one hU first rational
  have complete := same_denominator (nameF F K) D (C F) (data F K x y R a) v (cd x R) (one+one) U one hU both
    (symmetric (C F) D (cd x R) v one U hU last)
  have pow : Γ ⊢[PRAAx] U ≐ unit p*(two*two) :=
    (pw_add two p two).eqTrans (congrMul (.eqRefl _) ((pw_succ two one).eqTrans (congrMul (pw_one two) (.eqRefl _))))
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ hU (unit_positive p)
    (le_congr (.eqRefl _) (congrMul (.eqRefl one) pow).eqSymm
      (le_of_eq_add (d := unit p) (by ipra_ring))) complete

theorem actual_original_Barnes_named_increment_derivative_closed (F K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (let p := var 0
       let x := var 1
       let y := var 2
       let R := var 3
       let a := var 4
       input F K p x y R a ⟶ independentRate (nameF F K) (C F) (data F K x y R a) (cd x R) one (unit p)) :=
  closeUniv 5 (.impI (rate F K _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedIncrementDerivative
