import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.FirstDerivative.GaussianBarnesCanonicalPositiveFirstDerivativeRow
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalSecondDerivativeTail
import IPRADerivations.Analysis.Series.ReciprocalSquares.GaussianScaledReciprocalSquareInterval
import IPRADerivations.Analysis.Integration.Quadrature.GaussianRationalQuadratureDifference

/-!
# Finite first-to-second positive Barnes logarithm comparison

The two original first derivative sums and the original second derivative
model use the same cutoff. Summing the exact row residuals gives a uniform
quadratic remainder on a common positive margin.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveSecondDerivativeInterval

open_ipra
open GaussianBarnesCanonicalThirdDerivativePositiveMargin (source step)
open GaussianBarnesCanonicalPositiveFirstDerivativeRow (gain)
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianRationalFiniteSum (sum termsEqual multiplyBody multiply_body_at sum_multiply)
open GaussianRationalHorner (ofGaussian positive_product qadd qmul)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalQuadratureDifference (differenceBody difference_body_at finite_sum_difference)
open GaussianRationalReciprocal (bound_congr bounded_sum)
open GaussianRationalSyntheticDivision (qsub_congr qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "S" => GaussianBarnesCanonicalDerivativeTail.body
local notation "sd" => GaussianBarnesCanonicalDerivativeTail.data
local notation "sval" => GaussianBarnesCanonicalDerivativeTail.value
local notation "srow" => GaussianBarnesCanonicalDerivativeRow.value
local notation "T" => GaussianBarnesCanonicalSecondDerivativeTail.body
local notation "td" => GaussianBarnesCanonicalSecondDerivativeTail.data
local notation "tval" => GaussianBarnesCanonicalSecondDerivativeTail.value
local notation "trow" => GaussianBarnesCanonicalSecondDerivativeRow.value

def increment (A C B N r : PTm n) : PTm n :=
  qsub (sval (center C B) B N r) (sval (center A B) B N r)

def linear (A C B N r : PTm n) : PTm n :=
  qmul (ofGaussian (step A C) B) (tval (center A B) B N r)

def errorBody : PTm 2 := differenceBody (differenceBody S S) (multiplyBody T)

def errorData (A C B N : PTm n) : PTm n :=
  pairT (pairT (sd (center C B) B N) (sd (center A B) B N))
    (pairT (ofGaussian (step A C) B) (td (center A B) B N))

def residual (A C B k : PTm n) : PTm n :=
  qsub (qsub (srow (center C B) B k) (srow (center A B) B k))
    (qmul (ofGaussian (step A C) B) (trow (center A B) B k))

@[simp] theorem subst_increment {m : ℕ} (σ : Fin n → PTm m) (A C B N r : PTm n) :
    Syn.subst σ (increment A C B N r) = increment (Syn.subst σ A) (Syn.subst σ C)
      (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) := by simp [increment]

@[simp] theorem subst_linear {m : ℕ} (σ : Fin n → PTm m) (A C B N r : PTm n) :
    Syn.subst σ (linear A C B N r) = linear (Syn.subst σ A) (Syn.subst σ C)
      (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) := by simp [linear]

@[simp] theorem subst_errorData {m : ℕ} (σ : Fin n → PTm m) (A C B N : PTm n) :
    Syn.subst σ (errorData A C B N) =
      errorData (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ B) (Syn.subst σ N) := by simp [errorData]

@[simp] theorem subst_residual {m : ℕ} (σ : Fin n → PTm m) (A C B k : PTm n) :
    Syn.subst σ (residual A C B k) =
      residual (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ B) (Syn.subst σ k) := by simp [residual]

theorem error_body_at (A C B N i : PTm n) : Γ ⊢[PRAAx]
    inst2 errorBody i (errorData A C B N) ≐ residual A C B (succ (N+i)) := by
  let z := center A B
  let w := center C B
  let x := sd w B N
  let y := sd z B N
  let a := ofGaussian (step A C) B
  let v := td z B N
  have l := (difference_body_at (Γ := Γ) S S i x y).eqTrans
    (qsub_congr (GaussianBarnesCanonicalDerivativeTail.body_at w B N i)
      (GaussianBarnesCanonicalDerivativeTail.body_at z B N i))
  have r := (multiply_body_at (Γ := Γ) T a i v).eqTrans
    (qmul_congr (.eqRefl a) (GaussianBarnesCanonicalSecondDerivativeTail.body_at z B N i))
  exact (difference_body_at (differenceBody S S) (multiplyBody T) i (pairT x y) (pairT a v)).eqTrans (qsub_congr l r)

theorem exact_sum (A C B N r : PTm n) : Γ ⊢[PRAAx]
    sum errorBody r (errorData A C B N) ≐ qsub (increment A C B N r) (linear A C B N r) := by
  let x := sd (center C B) B N
  let y := sd (center A B) B N
  let a := ofGaussian (step A C) B
  let v := td (center A B) B N
  exact (finite_sum_difference (differenceBody S S) (multiplyBody T) r (pairT x y) (pairT a v)).eqTrans
    (qsub_congr (finite_sum_difference S S r x y) (sum_multiply T a r v))

private theorem error_at_index (A C B H K j : PTm n) (h : Γ ⊢[PRAAx] source A C B H K) :
    Γ ⊢[PRAAx] bounded (residual A C B (succ j)) (gain H K) ((B*B)*(succ j*succ j)) :=
  GaussianBarnesCanonicalPositiveFirstDerivativeRow.row_error A C B H K j h

theorem rows_bounded (A C B H K N : PTm n) (h : Γ ⊢[PRAAx] source A C B H K) :
    Γ ⊢[PRAAx] GaussianScaledReciprocalSquareInterval.rows errorBody N (gain H K) (B*B) (errorData A C B N) := by
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  let i : PTm (n+1) := var 0
  have hh : Δ ⊢[PRAAx] source (sh A) (sh C) (sh B) (sh H) (sh K) :=
    by simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift
  have term := error_at_index (sh A) (sh C) (sh B) (sh H) (sh K) (sh N+i) hh
  simpa only [GaussianScaledReciprocalSquareInterval.rows,Syn.shift,sh,Δ,i,subst_errorData,
    GaussianBarnesCanonicalPositiveFirstDerivativeRow.subst_gain,PTm.subst_mul] using
    bound_congr (error_body_at (sh A) (sh C) (sh B) (sh N) i).eqSymm (.eqRefl _) (.eqRefl _) term

theorem tail_error (A C B H K N r : PTm n) (h : Γ ⊢[PRAAx] source A C B H K)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (increment A C B N r) (linear A C B N r) (gain H K) ((B*B)*N) :=
  bound_congr (exact_sum A C B N r) (.eqRefl _) (.eqRefl _)
    (GaussianScaledReciprocalSquareInterval.tail_bound errorBody N r (gain H K) (B*B) (errorData A C B N)
      hN (positive_product _ _ h.andE₁ h.andE₁) (rows_bounded A C B H K N h))

private theorem shift_error_sum (A C B r : PTm n) :
    Γ ⊢[PRAAx] sum (shiftBody errorBody) r (errorData A C B zero) ≐ sum errorBody r (errorData A C B one) := by
  refine GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  let a := Syn.shift A
  let c := Syn.shift C
  let b := Syn.shift B
  let i : PTm (n+1) := var 0
  let Δ := lt i (Syn.shift r) :: Γ.map Fm.shift
  have e : Δ ⊢[PRAAx] residual a c b (succ (zero+succ i)) ≐ residual a c b (succ (one+i)) := by
    have idx : Δ ⊢[PRAAx] succ (zero+succ i) ≐ succ (one+i) := by ipra_ring
    ipra_congr (residual (var 0) (var 1) (var 2) (var 3) : PTm 4) with [.eqRefl _, .eqRefl _, .eqRefl _, idx]
  simpa only [termsEqual,Syn.shift,a,c,b,i,Δ,subst_errorData,inst2_shiftBody,one,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    (error_body_at (Γ := Δ) a c b zero (succ i)).eqTrans (e.eqTrans (error_body_at a c b one i).eqSymm)

theorem full_error (A C B H K r : PTm n) (h : Γ ⊢[PRAAx] source A C B H K) :
    Γ ⊢[PRAAx] distanceBounded (increment A C B zero (succ r)) (linear A C B zero (succ r))
      (two*gain H K) (B*B) := by
  let f := inst2 errorBody zero (errorData A C B zero)
  let g := sum errorBody r (errorData A C B one)
  let P := gain H K
  let D := B*B
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ h.andE₁ h.andE₁
  have first : Γ ⊢[PRAAx] bounded f P D :=
    bound_congr (error_body_at A C B zero zero).eqSymm (.eqRefl _) (by dsimp only [D]; ipra_ring)
      (error_at_index A C B H K (zero+zero) h)
  have tail : Γ ⊢[PRAAx] bounded g P D :=
    bound_congr (.eqRefl _) (.eqRefl _) (by dsimp only [D]; ipra_ring)
      (GaussianScaledReciprocalSquareInterval.tail_bound errorBody one r P D (errorData A C B one)
        (le_refl one) hD (rows_bounded A C B H K one h))
  have combine := GaussianRationalPowerDifference.bounded_sum_same f g P P D hD first tail
  have split := (GaussianRationalFiniteSum.sum_shift_first errorBody (Γ := Γ) r (errorData A C B zero)).eqTrans
    (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (shift_error_sum A C B r))
  exact bound_congr (split.eqSymm.eqTrans (exact_sum A C B zero (succ r))) (by ipra_ring) (.eqRefl _) combine

theorem actual_Barnes_positive_axis_first_to_second_full_prefix_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let A := var 0
       let C := var 1
       let B := var 2
       let H := var 3
       let K := var 4
       let r := var 5
       source A C B H K ⟶ distanceBounded (increment A C B zero (succ r)) (linear A C B zero (succ r))
         (two*gain H K) (B*B)) :=
  closeUniv 6 (.impI (full_error _ _ _ _ _ _ Prf.hyp0))

theorem actual_Barnes_positive_axis_first_to_second_interval_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (let A := var 0
       let C := var 1
       let B := var 2
       let H := var 3
       let K := var 4
       let N := var 5
       let r := var 6
       (source A C B H K ⋏ le one N) ⟶ distanceBounded (increment A C B N r) (linear A C B N r)
         (gain H K) ((B*B)*N)) :=
  closeUniv 7 (.impI (tail_error _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveSecondDerivativeInterval
