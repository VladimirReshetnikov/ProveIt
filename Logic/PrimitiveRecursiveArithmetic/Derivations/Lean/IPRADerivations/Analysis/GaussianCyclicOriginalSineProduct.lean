import IPRADerivations.Analysis.GaussianCyclicSineProductNormalization

/-!
# The original named sine product at the cyclic normalization clock

Each raw real factor approximates the corresponding original sine
observation. The actual finite multiplication loop transfers the
explicit positive normalization to the original doubled sine factors.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianCyclicOriginalSineProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCyclicExponentialRoots (source sampleRadius)
open GaussianCyclicFullHalfAngle (sineSample)
open GaussianCyclicChordSquare (realSine doubledSine real_sine_bound doubled_sine_bound sine_error twiceSineRadius)
open GaussianCyclicSineProductSquare (data index sine_at normBudget)
open GaussianCyclicSineProductNormalization (clock clock_fine product_real_error)
open GaussianNamedFiniteProduct (sample sample_distance rowBoundsAt rowDistance amplification)
open GaussianNamedFiniteProductMap (mapF map_at applyMap)
open GaussianNamedSineFromExponential (sine_canonical)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalHorner (qadd)
open GaussianRationalReciprocal (bound_congr bounded_sum)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianNameArithmetic (sum_distance)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def body : PTm 3 :=
  sineSample (var 0) (succ (index (fstT (var 2)) (var 1))) (succ (fstT (var 2))) (sndT (var 2))
def originalF : PR 3 := PTm.toPR body
def doubleBody : PTm 1 := qadd (var 0) (var 0)
def doubledF : PR 3 := mapF doubleBody originalF
def radius : PTm n := two*(sampleRadius+num 10)
def budget (N : PTm n) : PTm n := normBudget N+amplification radius N*num 20

theorem original_at (p N x i : PTm n) :
    Γ ⊢[PRAAx] ap3 originalF p i (data N x) ≐ sineSample p (succ (index N i)) (succ N) x := by
  have first : Γ ⊢[PRAAx] ap3 originalF p i (data N x) ≐
      sineSample p (succ (index (fstT (data N x)) i)) (succ (fstT (data N x))) (sndT (data N x)) := by
    simpa [originalF,body,ap3] using toPR_eq (Γ := Γ) body ![p,i,data N x]
  have next := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (sineSample (var 0) (succ (index (var 1) (var 3))) (succ (var 1)) (var 2) : PTm 4)
    (σ := ![p,fstT (data N x), sndT (data N x),i]) (σ' := ![p,N,x,i])
    (fun j => by fin_cases j; exact .eqRefl _; exact fst_pair _ _; exact snd_pair _ _; exact .eqRefl _)
  exact first.eqTrans (by simpa using next)

theorem doubled_at (p N x i : PTm n) :
    Γ ⊢[PRAAx] ap3 doubledF p i (data N x) ≐
      qadd (sineSample p (succ (index N i)) (succ N) x) (sineSample p (succ (index N i)) (succ N) x) := by
  have mapped : Γ ⊢[PRAAx] ap3 doubledF p i (data N x) ≐
      qadd (ap3 originalF p i (data N x)) (ap3 originalF p i (data N x)) := by
    simpa [doubledF,doubleBody,applyMap] using map_at doubleBody originalF p i (data N x)
  exact mapped.eqTrans (GaussianRationalSyntheticDivision.qadd_congr (original_at p N x i) (original_at p N x i))

private theorem index_source (N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] source (succ (index N i)) (succ N) := by
  have e : Γ ⊢[PRAAx] N ≐ succ i+index N i := eq_add_of_le hi
  have h : Γ ⊢[PRAAx] le (succ (index N i)) N := le_of_eq_add (d := i) (e.eqTrans (by ipra_ring))
  exact .andI (zero_lt_succ N) (le_trans h (le_succ_self N))

theorem original_bound (p r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] bounded (sineSample p r m x) (sampleRadius+num 10) one := by
  let s := sineSample p r m x
  let q := realSine p r m x
  have h0 : Γ ⊢[PRAAx] bounded q sampleRadius one := real_sine_bound p r m x h
  have h1 : Γ ⊢[PRAAx] bounded (qsub s q) (num 10) one :=
    bounded_radius_mono _ _ _ _ _ (unit_positive p) (le_refl one)
      (le_mul_mono (le_refl (num 10)) (unit_positive p)) (sine_error p r m x h)
  have hc := sine_canonical (Γ := Γ) GaussianCyclicExponentialRoots.angleF
    GaussianArctangentExponentialPeriod.fullTurnRadius (GaussianCyclicExponentialRoots.angleData r (two*m) x) p
  exact bound_congr (GaussianRationalLinearProduct.add_sub_right q s hc)
    (by ipra_ring) (by ipra_ring) (bounded_sum _ _ _ _ _ _ (le_refl one) (le_refl one) h0 h1)

theorem original_rows (p N x : PTm n) :
    Γ ⊢[PRAAx] rowBoundsAt doubledF p N radius (data N x) := by
  refine .allI (.impI ?_)
  let P := Syn.shift p
  let J := Syn.shift N
  let X := Syn.shift x
  let i : PTm (n+1) := var 0
  let Δ := lt i J :: Γ.map Fm.shift
  have H : Δ ⊢[PRAAx] source (succ (index J i)) (succ J) := index_source J i Prf.hyp0
  have b := original_bound P _ _ X H
  have t : Δ ⊢[PRAAx] bounded (ap3 doubledF P i (data J X)) radius one :=
    bound_congr (doubled_at P J X i).eqSymm (by unfold radius; ipra_ring) (by ipra_ring)
    (bounded_sum _ _ _ _ _ _ (le_refl one) (le_refl one) b b)
  simpa [rowBoundsAt,Δ,Syn.shift,P,J,X,i,radius,one] using t

theorem real_rows (p N x : PTm n) :
    Γ ⊢[PRAAx] rowBoundsAt GaussianCyclicSineProductSquare.sineF p N radius (data N x) := by
  refine .allI (.impI ?_)
  let P := Syn.shift p
  let J := Syn.shift N
  let X := Syn.shift x
  let i : PTm (n+1) := var 0
  let Δ := lt i J :: Γ.map Fm.shift
  have H : Δ ⊢[PRAAx] source (succ (index J i)) (succ J) := index_source J i Prf.hyp0
  have b := doubled_sine_bound P _ _ X H
  have r : Δ ⊢[PRAAx] le twiceSineRadius radius :=
    le_mul_mono (le_refl two) (le_add_right sampleRadius (num 10))
  have l := bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) r) b
  simpa [rowBoundsAt,Δ,Syn.shift,P,J,X,i,radius,one] using
    bound_congr (sine_at P J X i).eqSymm (.eqRefl _) (.eqRefl _) l

theorem same_clock_rows (p N x : PTm n) :
    Γ ⊢[PRAAx] rowDistance doubledF GaussianCyclicSineProductSquare.sineF p p N (num 20) (unit p) (data N x) (data N x) := by
  refine .allI (.impI ?_)
  let P := Syn.shift p
  let J := Syn.shift N
  let X := Syn.shift x
  let i : PTm (n+1) := var 0
  let Δ := lt i J :: Γ.map Fm.shift
  have H : Δ ⊢[PRAAx] source (succ (index J i)) (succ J) := index_source J i Prf.hyp0
  have b := sine_error P _ _ X H
  have t := sum_distance _ _ _ _ _ _ _ (unit_positive P) b b
  simpa [rowDistance,Δ,Syn.shift,P,J,X,i] using
    distance_congr (doubled_at P J X i).eqSymm (sine_at P J X i).eqSymm (by ipra_ring) (.eqRefl _) t

theorem actual_doubled_product_error (p N x : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (naturalPoint (succ N))
      (sample doubledF (clock p (succ N)) N (data N x)) (budget N) (unit (clock p (succ N))) := by
  let q := clock p (succ N)
  let hU := unit_positive (Γ := Γ) q
  have a := product_real_error (Γ := Γ) q N x (clock_fine _ _) (GaussianCyclicExponentialSeparation.clock_fine _ _)
  have b := sample_distance doubledF GaussianCyclicSineProductSquare.sineF q q N radius (num 20) (unit q)
    (data N x) (data N x) hU (original_rows q N x) (real_rows q N x) (same_clock_rows q N x)
  exact distance_triangle_same _ _ _ _ _ _ hU a (distance_symmetric _ _ _ _ hU b)

theorem actual_original_doubled_sine_product_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (distanceBounded (naturalPoint (succ (var 1)))
        (sample doubledF (clock (var 2) (succ (var 1))) (var 1) (data (var 1) (var 0)))
        (budget (var 1)) (unit (clock (var 2) (succ (var 1))))) :=
  closeUniv 3 (actual_doubled_product_error _ _ _)

end LeanProofs.IPRA.Analysis.GaussianCyclicOriginalSineProduct
