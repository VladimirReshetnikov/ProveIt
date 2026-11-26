import IPRADerivations.Analysis.Gamma.Digamma.NegativeAxis.GaussianGammaNegativeIntervalNamedDigamma
import IPRADerivations.Analysis.Gamma.Digamma.NegativeAxis.GaussianGammaNegativeIntervalDigammaRate
import IPRADerivations.Analysis.Gamma.NegativeAxis.Input.GaussianGammaNegativeIntervalNamedInput

/-!
# Original normalized Gamma unit-step quotients at a named negative offset

The program freezes the offset at a certified rational sample and
uses the original reciprocal Gamma times the original forward unit-step
Gamma quotient there. The step denominators grow with the precision.
The native quotient rate and the named frozen digamma rate give the
same shifted digamma name with the usual independent observation errors.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedDigammaQuotient

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeCriticalSlope (coefficient)
open GaussianGammaNegativeIntervalDigammaRate (quotientF quotientData cost minimumDenominator original_rate side_bound)
open GaussianGammaNegativeIntervalNamedDigamma (source data subst_data frozenData original_frozen_rate clock_budget)
open GaussianGammaNegativeIntervalNamedInput (sampleNumerator sampleDenominator frozen_guard)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm point_at)
open GaussianNamedInverseRate (diagonal_rate)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "DF" => GaussianGammaNegativeIntervalNamedDigamma.nameF
local notation "NF" => GaussianGammaNegativeCriticalEndpoints.nameF
local notation "nd" => GaussianGammaNegativeCriticalEndpoints.nameData

def stage (p : PTm n) : PTm n := succ (succ (succ p))
def offsetClock (p E N : PTm n) : PTm n := GaussianGammaNegativeIntervalNamedDigamma.clock (stage p) E N
def argumentNumerator (f : PR 2) (p x E N : PTm n) : PTm n := sampleNumerator f (offsetClock p E N) x
def argumentDenominator (f : PR 2) (p x E N : PTm n) : PTm n := sampleDenominator f (offsetClock p E N) x
def demand (f : PR 2) (p x E N : PTm n) : PTm n :=
  exponent (cost (argumentNumerator f p x E N) (argumentDenominator f p x E N) N) (stage p)
def step (f : PR 2) (p x E N : PTm n) : PTm n :=
  minimumDenominator (demand f p x E N) (argumentNumerator f p x E N) (argumentDenominator f p x E N)
def value (f : PR 2) (p x E N : PTm n) : PTm n :=
  ap2 quotientF (stage p) (quotientData (argumentNumerator f p x E N) (argumentDenominator f p x E N) N (step f p x E N))
def nameF (f : PR 2) : PR 2 := PTm.toPR
  (value f (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2)

@[simp] theorem subst_stage {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (stage p) = stage (Syn.subst σ p) := by simp [stage]
@[simp] theorem subst_offsetClock {m : ℕ} (σ : Fin n → PTm m) (p E N : PTm n) :
    Syn.subst σ (offsetClock p E N) = offsetClock (Syn.subst σ p) (Syn.subst σ E) (Syn.subst σ N) :=
  by simp [offsetClock]
@[simp] theorem subst_argumentNumerator {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x E N : PTm n) :
    Syn.subst σ (argumentNumerator f p x E N) = argumentNumerator f (Syn.subst σ p) (Syn.subst σ x)
      (Syn.subst σ E) (Syn.subst σ N) :=
  by simp [argumentNumerator]
@[simp] theorem subst_argumentDenominator {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x E N : PTm n) :
    Syn.subst σ (argumentDenominator f p x E N) = argumentDenominator f (Syn.subst σ p) (Syn.subst σ x)
      (Syn.subst σ E) (Syn.subst σ N) :=
  by simp [argumentDenominator]
@[simp] theorem subst_demand {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x E N : PTm n) :
    Syn.subst σ (demand f p x E N) = demand f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ E) (Syn.subst σ N) := by
  simp [demand,cost,GaussianGammaNegativeIntervalDerivativeRate.cost,
    GaussianGammaNegativeIntervalDerivativeRate.firstCost,GaussianGammaNegativeIntervalDerivativeRate.secondCost,
    GaussianGammaNegativeIntervalDerivativeRate.eulerCap,GaussianGammaNegativeIntervalInverseStepCoefficient.inverseCap,
    GaussianGammaNegativeIntervalDerivativeTarget.reciprocalData,GaussianGammaNegativeIntervalNative.argument,
    GaussianNameRingLaws.three]
@[simp] theorem subst_step {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x E N : PTm n) :
    Syn.subst σ (step f p x E N) = step f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ E) (Syn.subst σ N) :=
  by simp [step,minimumDenominator]
@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x E N : PTm n) :
    Syn.subst σ (value f p x E N) = value f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ E) (Syn.subst σ N) := by
  simp [value,quotientData,GaussianGammaNegativeIntervalStep.data,GaussianGammaNegativeIntervalStep.denominator,
    GaussianGammaDigammaStep.neighborNumerator,GaussianGammaNegativeIntervalDerivativeTarget.reciprocalData,
    GaussianGammaNegativeIntervalNative.data,GaussianGammaNegativeIntervalNative.argument]

theorem sample_at (f : PR 2) (p x E N : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF f) p (data x E N) ≐ value f p x E N := by
  let X := data x E N
  have raw : Γ ⊢[PRAAx] ap2 (nameF f) p X ≐ value f p (fstT X) (fstT (sndT X)) (sndT (sndT X)) := by
    simpa [nameF,ap2] using toPR_eq (Γ := Γ)
      (value f (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2) ![p,X]
  have first : Γ ⊢[PRAAx] fstT X ≐ x := fst_pair _ _
  have rest : Γ ⊢[PRAAx] sndT X ≐ pairT E N := snd_pair _ _
  have mid := (congrFst rest).eqTrans (fst_pair E N)
  have last := (congrSnd rest).eqTrans (snd_pair E N)
  have fields := Prf.eqCongr (Ax := PRAAx) (Γ := Γ)
    (value f (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![p,fstT X,fstT (sndT X),sndT (sndT X)]) (σ' := ![p,x,E,N]) (fun i => by
      fin_cases i
      exact .eqRefl _
      exact first
      exact mid
      exact last)
  exact raw.eqTrans (by simpa using fields)

theorem selected_fraction (f : PR 2) (p x E N : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] distanceBounded (fraction (argumentNumerator f p x E N) (argumentDenominator f p x E N))
      (ap2 f (offsetClock p E N) x) zero one :=
  GaussianUnitIntervalInputDecoding.decoded_distance _ E (GaussianNamedEulerUnitTime.source_at f (offsetClock p E N) x E h)

theorem base_guard (f : PR 2) (p x E N : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] guard (argumentNumerator f p x E N) (argumentDenominator f p x E N) :=
  frozen_guard f (offsetClock p E N) x E h

theorem step_inside (f : PR 2) (p x E N : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] lt (argumentDenominator f p x E N) (step f p x E N) :=
  GaussianGammaNegativeIntervalInverseStepCoefficient.step_inside _ _ _ (base_guard f p x E N h)
    (side_bound (demand f p x E N) _ _ (step f p x E N) (le_refl (step f p x E N)))

theorem step_cofinal (f : PR 2) (p x E N : PTm n) : Γ ⊢[PRAAx] le (unit p) (step f p x E N) := by
  let r := demand f p x E N
  have later : Γ ⊢[PRAAx] le p r :=
    le_trans (le_trans (le_succ_self p) (le_trans (le_succ_self (succ p)) (le_succ_self (succ (succ p)))))
      (le_add_right (stage p) _)
  have bound : Γ ⊢[PRAAx] le (unit r) (step f p x E N) :=
    le_trans (le_add_left _ _) (le_add_left _ _)
  exact le_trans (GaussianExponentialReference.unit_monotone later) bound

private theorem stage_unit (p : PTm n) : Γ ⊢[PRAAx] unit (stage p) ≐ num 8*unit p :=
  (pw_succ two (succ (succ p))).eqTrans
    ((congrMul ((pw_succ two (succ p)).eqTrans (congrMul (pw_succ two p) (.eqRefl _))) (.eqRefl _)).eqTrans
      (by unfold unit; ipra_ring))

theorem diagonal_at (f : PR 2) (p x E N : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] distanceBounded (value f p x E N) (ap2 (DF f) (stage p) (data x E N)) (num 6) (unit (stage p)) := by
  let s := stage p
  let k := offsetClock p E N
  let a := argumentNumerator f p x E N
  let b := argumentDenominator f p x E N
  let r := demand f p x E N
  let D := step f p x E N
  let P := unit s
  let U := unit r
  let V := unit k
  let C := cost a b N
  let L := coefficient N E
  let y := ap2 NF s (nd a b N)
  have hp := unit_positive (Γ := Γ) s
  have hu := unit_positive (Γ := Γ) r
  have hv := unit_positive (Γ := Γ) k
  have hr := original_rate r a b N D (base_guard f p x E N h) (le_refl D)
  have d := diagonal_rate quotientF NF (quotientData a b N D) (nd a b N) C U s hu hr
  have pay : Γ ⊢[PRAAx] le (C*P) U := query_budget C s
  have first : Γ ⊢[PRAAx] distanceBounded (value f p x E N) y (num 3) P :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hu hp) hp
      (by change Γ ⊢[PRAAx] le ((C*P+two*U)*P) (num 3*(U*P))
          ipra_le 𝔞(P)*sl pay) d
  have frozen := original_frozen_rate f k x E N h
  have rest := diagonal_rate (DF f) NF (data x E N) (frozenData f k x N) L V s hv frozen
  have clockPay : Γ ⊢[PRAAx] le (L*P) V :=
    le_trans (by ipra_le 𝔞(L)*𝔞(P)) (clock_budget s E N)
  have later : Γ ⊢[PRAAx] distanceBounded (ap2 (DF f) s (data x E N)) y (num 3) P :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hv hp) hp
      (by change Γ ⊢[PRAAx] le ((L*P+two*V)*P) (num 3*(V*P))
          ipra_le 𝔞(P)*sl clockPay) rest
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp first (distance_symmetric _ _ _ _ hp later))

theorem original_observations (f : PR 2) (p q x E N : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x E N)) (ap2 (DF f) q (data x E N))
      (unit p+unit q) (unit p*unit q) := by
  let s := stage p
  let V := unit s
  let P := unit p
  let Q := unit q
  let X := data x E N
  have hv := unit_positive (Γ := Γ) s
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have reg := GaussianGammaNegativeIntervalNamedDigamma.name_regular f x E N h
  have close := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hv (positive_product _ _ hv hq)
    (diagonal_at f p x E N h) (point_at (DF f) X s q reg)
  have ver := natEq (stage_unit (Γ := Γ) p)
  apply distance_congr (sample_at f p x E N).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hv (positive_product _ _ hv hq))
    (positive_product _ _ hp hq) (by
      change Γ ⊢[PRAAx] le ((num 6*(V*Q)+(V+Q)*V)*(P*Q)) ((P+Q)*(V*(V*Q)))
      ipra_le 𝔞(V)*𝔞(Q)^2*𝔞(P) using rw [ver]; ring) close

theorem original_cross (f : PR 2) (x E N : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (DF f) (data x E N) (data x E N) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f (sh x) (sh E) :=
    by simpa [Fm.shift,Syn.shift,sh] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,subst_data,Syn.shift,sh] using
    original_observations f (var 1) (var 0) (sh x) (sh E) (sh N) hs

theorem name_regular (f : PR 2) (x E N : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data x E N) :=
  cross_trans _ _ _ _ _ _ (original_cross f x E N h) (cross_symm _ _ _ _ (original_cross f x E N h))

theorem actual_original_negative_interval_named_normalized_derivative_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) ⟶
        pointCN (nameF f) (data (var 0) (var 1) (var 2)) ⋏
          crossEquivalent (nameF f) (DF f) (data (var 0) (var 1) (var 2)) (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.andI (name_regular f _ _ _ Prf.hyp0) (original_cross f _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedDigammaQuotient
