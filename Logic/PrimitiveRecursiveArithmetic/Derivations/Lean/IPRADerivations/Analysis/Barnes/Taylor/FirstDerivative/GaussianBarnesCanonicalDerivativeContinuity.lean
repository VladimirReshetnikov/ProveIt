import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalDerivativeCofinal
import IPRADerivations.Analysis.Barnes.HeadProducts.GaussianBarnesCanonicalFactorLipschitz
import IPRADerivations.Analysis.Series.GaussianReciprocalSquareSumDistance
import IPRADerivations.Analysis.Names.Rates.GaussianNamedLipschitzRate
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedMultiplyRate

/-!
# Disk Lipschitz bound for the original cofinal Barnes logarithmic derivative

Each actual rational row has a Lipschitz coefficient summable by
the reciprocal-square telescoper. The estimate is uniform over
the original diagonal cutoffs, and the named regularity bound gives
the rate at independent observation precisions.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeContinuity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalDerivativeCofinal (nameF sample_at regular)
open GaussianBarnesCanonicalDerivativeRow (offset offset_bound base_lower inverse_base_bound boundNumerator)
open GaussianBarnesCanonicalLogCofinal (source data)
open GaussianBarnesCanonicalLogCofinalRate (initial_source)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (qmul ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded bounded qsub)
open GaussianRationalPowerDifference (product_difference bounded_sum_same distance_refl_zero)
open GaussianRationalReciprocal (bounded_product bound_congr reciprocal qone)
open GaussianReciprocalSquareInterval (denominator denominator_positive)
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Row" => GaussianBarnesCanonicalDerivativeRow.value
local notation "Base" => GaussianBarnesCanonicalFactor.base
local notation "Value" => GaussianBarnesCanonicalDerivativeTail.value
local notation "rowSource" => GaussianBarnesCanonicalLogRow.source
local notation "body" => GaussianBarnesCanonicalDerivativeTail.body
local notation "rowData" => GaussianBarnesCanonicalDerivativeTail.data

def gain (R : PTm n) : PTm n := num 4*(R+R*R)

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (gain R) = gain (Syn.subst σ R) := by simp [gain]

theorem row_rate (z w R B D k A M : PTm n)
    (hz : Γ ⊢[PRAAx] rowSource z R B k) (hw : Γ ⊢[PRAAx] rowSource w R D k)
    (hM : Γ ⊢[PRAAx] le one M)
    (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A M) :
    Γ ⊢[PRAAx] distanceBounded (Row z B k) (Row w D k) (gain R*A) (M*(k*k)) := by
  let x := offset z B k
  let y := offset w D k
  let b := Base z B k
  let c := Base w D k
  let d := M*k
  let K := M*(k*k)
  have hk := hz.andE₂.andE₁
  have hd : Γ ⊢[PRAAx] le one d := positive_product _ _ hM hk
  have hk2 := positive_product k k hk hk
  have hK : Γ ⊢[PRAAx] le one K := positive_product _ _ hM hk2
  have hxy : Γ ⊢[PRAAx] distanceBounded x y A d :=
    GaussianBarnesCanonicalFactorLipschitz.scaled_fraction_distance z w B D k A M hz.andE₁ hw.andE₁ hk hM h
  have hb : Γ ⊢[PRAAx] distanceBounded b c A d :=
    distance_congr (.eqRefl _) (.eqRefl _) (zero_add A) (.eqRefl _)
      (GaussianNameArithmetic.sum_distance qone qone x y zero A d hd (distance_refl_zero qone d hd) hxy)
  have iDist := GaussianNameReciprocal.inverse_distance b c two A d (le_succ_self one) hd
    (base_lower z R B k hz) (base_lower w R D k hw) hb
  have hx := offset_bound z R B k hz
  have hy := offset_bound w R D k hw
  have l : Γ ⊢[PRAAx] bounded (qmul (qsub x y) x) (R*A) K :=
    bound_congr (.eqRefl _) (mul_comm _ _) (by unfold d K; ipra_ring)
      (bounded_product _ _ A d R k hd hk hxy hx)
  have r : Γ ⊢[PRAAx] bounded (qmul y (qsub x y)) (R*A) K :=
    bound_congr (.eqRefl _) (.eqRefl _) (by unfold d K; ipra_ring)
      (bounded_product _ _ R k A d hk hd hy hxy)
  have sqDist : Γ ⊢[PRAAx] distanceBounded (qmul x x) (qmul y y) (two*R*A) K :=
    bound_congr (product_difference x y x y).eqSymm (by ipra_ring) (.eqRefl _)
      (bounded_sum_same _ _ _ _ _ hK l r)
  have left : Γ ⊢[PRAAx] bounded (qmul (qsub (qmul x x) (qmul y y)) (reciprocal b)) (num 4*R*A) K :=
    bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (bounded_product _ _ _ K two one hK (le_refl one) sqDist (inverse_base_bound z R B k hz))
  have y2 := bounded_product _ _ R k R k hk hk hy hy
  have raw := bounded_product _ _ (R*R) (k*k) (two*two*A) d hk2 hd y2 iDist
  have fit : Γ ⊢[PRAAx] le (((R*R)*(two*two*A))*K) ((num 4*(R*R)*A)*((k*k)*d)) :=
    le_congr (by unfold K; ipra_ring) (by unfold d K; ipra_ring)
      (mul_le_mul_right ((num 4*(R*R)*A)*K) hk)
  have right := bounded_radius_mono _ _ _ _ _ (positive_product _ _ hk2 hd) hK fit raw
  have e := product_difference (Γ := Γ) (qmul x x) (qmul y y) (reciprocal b) (reciprocal c)
  exact bound_congr e.eqSymm (by unfold gain; ipra_ring) (.eqRefl _)
    (bounded_sum_same _ _ _ _ _ hK left right)

theorem finite_rate (z w R B D N r A M : PTm n)
    (hz : Γ ⊢[PRAAx] rowSource z R B N) (hw : Γ ⊢[PRAAx] rowSource w R D N)
    (hM : Γ ⊢[PRAAx] le one M)
    (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A M) :
    Γ ⊢[PRAAx] distanceBounded (Value z B N r) (Value w D N r) (gain R*A) M := by
  let C := gain R*A
  let x := rowData z B N
  let y := rowData w D N
  have hN := hz.andE₂.andE₁
  have rows : Γ ⊢[PRAAx] GaussianReciprocalSquareSumDistance.rows body body N C M zero one x y := by
    refine .allI ?_
    let sh (t : PTm n) := Syn.shift t
    let Δ := Γ.map Fm.shift
    let i : PTm (n+1) := var 0
    let k := succ (sh N+i)
    let E := sh M*(k*k)
    have hz' : Δ ⊢[PRAAx] rowSource (sh z) (sh R) (sh B) (sh N) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hz.shift
    have hw' : Δ ⊢[PRAAx] rowSource (sh w) (sh R) (sh D) (sh N) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hw.shift
    have hm' : Δ ⊢[PRAAx] le one (sh M) := by simpa [Δ,Fm.shift,Syn.shift,sh,one] using hM.shift
    have h' : Δ ⊢[PRAAx] distanceBounded (ofGaussian (sh z) (sh B)) (ofGaussian (sh w) (sh D)) (sh A) (sh M) :=
      by simpa [Δ,Fm.shift,Syn.shift,sh] using h.shift
    have d := row_rate (sh z) (sh w) (sh R) (sh B) (sh D) k (sh A) (sh M)
      (GaussianBarnesCanonicalLogTail.row_source (sh z) (sh R) (sh B) (sh N) i hz')
      (GaussianBarnesCanonicalLogTail.row_source (sh w) (sh R) (sh D) (sh N) i hw') hm' h'
    have a := GaussianBarnesCanonicalDerivativeTail.body_at (Γ := Δ) (sh z) (sh B) (sh N) i
    have b := GaussianBarnesCanonicalDerivativeTail.body_at (Γ := Δ) (sh w) (sh D) (sh N) i
    have d' : Δ ⊢[PRAAx] distanceBounded (inst2 body i (rowData (sh z) (sh B) (sh N)))
        (inst2 body i (rowData (sh w) (sh D) (sh N))) ((gain (sh R)*sh A)*one+zero*E) (E*one) :=
      distance_congr a.eqSymm b.eqSymm (by ipra_ring) (by unfold E; ipra_ring) d
    simpa only [GaussianReciprocalSquareSumDistance.rows,GaussianReciprocalSquareSumDistance.radiusDenominator,
      GaussianBarnesCanonicalDerivativeTail.subst_data,subst_gain,C,x,y,Syn.shift,sh,i,k,E,PTm.subst_mul,one,
      ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ] using d'
  have cert := GaussianReciprocalSquareSumDistance.sum_distance body body N C M zero one x y r hN hM (le_refl one) rows
  have hden := positive_product _ _ (positive_product _ _ hM (denominator_positive N r hN)) (le_refl one)
  have fit : Γ ⊢[PRAAx] le (GaussianReciprocalSquareSumDistance.radiusNumerator C zero (M*denominator N r) one r*M)
      (C*GaussianReciprocalSquareSumDistance.radiusDenominator (M*denominator N r) one) := by
    have lo : Γ ⊢[PRAAx] le r (N+r) := le_add_left _ _
    have hi : Γ ⊢[PRAAx] le (N+r) (N*(N+r)) :=
      le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (N+r) hN)
    exact le_congr (by unfold GaussianReciprocalSquareSumDistance.radiusNumerator; ipra_ring)
      (by unfold GaussianReciprocalSquareSumDistance.radiusDenominator denominator; ipra_ring)
      (mul_le_mul_right (C*M) (le_trans lo hi))
  exact distance_radius_mono _ _ _ _ _ _ hden hM fit cert

theorem diagonal (p z w R B D A M : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w R D)
    (hM : Γ ⊢[PRAAx] le one M) (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A M) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z R B)) (ap2 nameF p (data w R D)) (gain R*A) M :=
  distance_congr (sample_at p z R B).eqSymm (sample_at p w R D).eqSymm (.eqRefl _) (.eqRefl _)
    (finite_rate z w R B D (initial R) (GaussianBarnesCanonicalDerivativeCofinal.length p R) A M
      (initial_source z R B hz) (initial_source w R D hw) hM h)

theorem rate (z w R B D A M : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w R D)
    (hM : Γ ⊢[PRAAx] le one M) (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A M) :
    Γ ⊢[PRAAx] independentRate nameF nameF (data z R B) (data w R D) (gain R*A) M := by
  apply GaussianNamedLipschitzRate.independent_rate nameF nameF _ _ _ M zero hM (regular z R B hz) (regular w R D hw)
  refine .allI ?_
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  have hz' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hz.shift
  have hw' : Δ ⊢[PRAAx] source (sh w) (sh R) (sh D) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hw.shift
  have hm' : Δ ⊢[PRAAx] le one (sh M) := by simpa [Δ,Fm.shift,Syn.shift,sh,one] using hM.shift
  have h' : Δ ⊢[PRAAx] distanceBounded (ofGaussian (sh z) (sh B)) (ofGaussian (sh w) (sh D)) (sh A) (sh M) :=
    by simpa [Δ,Fm.shift,Syn.shift,sh] using h.shift
  have raw := diagonal p (sh z) (sh w) (sh R) (sh B) (sh D) (sh A) (sh M) hz' hw' hm' h'
  have e := distance_radius_mono _ _ _ _ (gain (sh R)*sh A*unit p+zero*sh M) (sh M*unit p)
    hm' (positive_product _ _ hm' (unit_positive p)) (le_of_eq_add (d := zero) (by ipra_ring)) raw
  simpa only [GaussianNamedLipschitzRate.diagonalEnvelope,GaussianNamedLipschitzRate.diagonalNumerator,
    GaussianNamedLipschitzRate.diagonalDenominator,GaussianBarnesCanonicalLogCofinal.subst_data,subst_gain,
    PTm.subst_mul,ConciseIPRA.PTm.subst_zero,Δ,Syn.shift,sh,p] using e

theorem sample_bound (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data z R B)) (boundNumerator R) one := by
  have b := GaussianBarnesCanonicalDerivativeTail.tail_bound z R B (initial R)
    (GaussianBarnesCanonicalDerivativeCofinal.length p R) (initial_source z R B h)
  have hi := initial_positive (Γ := Γ) R
  exact bound_congr (sample_at p z R B).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_radius_mono _ _ _ _ _ hi (le_refl one)
      (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (boundNumerator R) hi)) b)

theorem samples (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound nameF (data z R B) (boundNumerator R) := by
  refine .allI ?_
  let sh (t : PTm n) := Syn.shift t
  have h' : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Fm.shift,Syn.shift,sh] using h.shift
  simpa only [GaussianNamedMultiplyRate.sampleBound,Syn.shift,sh,GaussianBarnesCanonicalLogCofinal.subst_data,
    GaussianBarnesCanonicalDerivativeRow.subst_boundNumerator] using sample_bound (var 0) (sh z) (sh R) (sh B) h'

theorem actual_Barnes_cofinal_logarithmic_derivative_disk_Lipschitz_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let z := var 0
     let w := var 1
     let R := var 2
     let B := var 3
     let D := var 4
     let A := var 5
     let M := var 6
     (source z R B ⋏ (source w R D ⋏ (le one M ⋏ distanceBounded (ofGaussian z B) (ofGaussian w D) A M))) ⟶
       independentRate nameF nameF (data z R B) (data w R D) (gain R*A) M) :=
  closeUniv 7 (.impI (rate _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeContinuity
