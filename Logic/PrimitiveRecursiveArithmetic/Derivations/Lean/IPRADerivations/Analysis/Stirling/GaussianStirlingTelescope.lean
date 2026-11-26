import IPRADerivations.Analysis.Stirling.GaussianStirlingNames
import IPRADerivations.Analysis.Stirling.GaussianStirlingDifference
import IPRADerivations.Analysis.Names.GaussianNamedDifference
import IPRADerivations.Analysis.Series.GaussianRationalParameterTelescope

/-!
# Finite Stirling telescope at independent observation precisions

For (N) terms at (a/b,a/b+1,ldots,a/b+N-1), the actual finite
sum of the Stirling difference samples is within
(N(2^{-p}+7cdot2^{-s})) of the difference of the actual (A)
endpoints at precision (s). The one-step named recurrence is an
explicit object-theory premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingTelescope

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianStirlingNames (source nameData source_shift name_regular)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalFiniteSum (sum)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono distance_triangle_same)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm cross_trans point_at)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "A" => GaussianStirlingNames.nameF
local notation "D" => GaussianStirlingDifference.nameF
local notation "G" => GaussianNamedDifference.nameF A A

def shifted (a b i : PTm n) : PTm n := a+b*i
def stepData (a b : PTm n) : PTm n := GaussianNamedDifference.data (nameData a b) (nameData (a+b) b)
def stepLaw (a b : PTm n) : Fm PTm n := crossEquivalent G D (stepData a b) (GaussianStirlingDifference.data a b)
def localRows (N a b : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶ stepLaw (shifted (Syn.shift a) (Syn.shift b) (var 0)) (Syn.shift b))

@[simp] theorem subst_shifted {l : ℕ} (σ : Fin n → PTm l) (a b i : PTm n) :
    Syn.subst σ (shifted a b i) = shifted (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ i) := by simp [shifted]
@[simp] theorem subst_stepData {l : ℕ} (σ : Fin n → PTm l) (a b : PTm n) :
    Syn.subst σ (stepData a b) = stepData (Syn.subst σ a) (Syn.subst σ b) := by simp [stepData]
@[simp] theorem subst_stepLaw {l : ℕ} (σ : Fin n → PTm l) (a b : PTm n) :
    (stepLaw a b).subst σ = stepLaw (Syn.subst σ a) (Syn.subst σ b) := by simp [stepLaw]
@[simp] theorem subst_localRows {l : ℕ} (σ : Fin n → PTm l) (N a b : PTm n) :
    (localRows N a b).subst σ = localRows (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [localRows,Syn.subst_shift,Syn.shift_subst]

theorem shifted_source (a b i : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] source (shifted a b i) b :=
  .andI (le_trans h.andE₁ (le_add_right a (b*i))) h.andE₂

theorem rows_at (N a b i : PTm n) (h : Γ ⊢[PRAAx] localRows N a b) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] stepLaw (shifted a b i) b := by
  have e : Γ ⊢[PRAAx] lt i N ⟶ stepLaw (shifted a b i) b := by simpa [localRows] using h.allE i
  exact .impE e hi

theorem rows_from_recurrence (N a b : PTm n) (h : Γ ⊢[PRAAx] source a b)
    (recurrence : ∀ {l : ℕ} {Δ : List (Fm PTm l)} (a b : PTm l),
      (Δ ⊢[PRAAx] source a b) → (Δ ⊢[PRAAx] stepLaw a b)) :
    Γ ⊢[PRAAx] localRows N a b := by
  refine .allI (.impI ?_)
  let X := Syn.shift a
  let Y := Syn.shift b
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source X Y := by simpa [Fm.shift,Syn.shift,Δ,X,Y] using h.shift.wk
  exact recurrence _ _ (shifted_source X Y (var 0) hs)

def sampleData (p a b : PTm n) : PTm n := pairT p (pairT a b)
def rowSample (f : PR 2) (t : PTm 2) (p a b i : PTm n) : PTm n :=
  ap2 f p (inst2 t (shifted a b i) b)
def rowBody (f : PR 2) (t : PTm 2) : PTm 2 :=
  rowSample f t (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)

@[simp] theorem subst_sampleData {l : ℕ} (σ : Fin n → PTm l) (p a b : PTm n) :
    Syn.subst σ (sampleData p a b) = sampleData (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b) := by simp [sampleData]
@[simp] theorem subst_rowSample {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (t : PTm 2) (p a b i : PTm n) :
    Syn.subst σ (rowSample f t p a b i) = rowSample f t (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ i) :=
  by simp [rowSample]

theorem row_at (f : PR 2) (t : PTm 2) (p a b i : PTm n) :
    Γ ⊢[PRAAx] inst2 (rowBody f t) i (sampleData p a b) ≐ rowSample f t p a b i := by
  let X := sampleData p a b
  have outer : Γ ⊢[PRAAx] sndT X ≐ pairT a b := snd_pair _ _
  simpa [rowBody,inst2,X] using Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (rowSample f t (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![fstT X,fstT (sndT X),sndT (sndT X),i]) (σ' := ![p,a,b,i]) (fun j => by
      fin_cases j
      · exact fst_pair _ _
      · exact (congrFst outer).eqTrans (fst_pair _ _)
      · exact (congrSnd outer).eqTrans (snd_pair _ _)
      · exact .eqRefl _)

def aBody : PTm 2 := rowBody A (nameData (var 0) (var 1))
def dBody : PTm 2 := rowBody D (GaussianStirlingDifference.data (var 0) (var 1))
def rawSum (p N a b : PTm n) : PTm n := sum dBody N (sampleData p a b)
def endpoint (p N a b : PTm n) : PTm n :=
  qsub (ap2 A p (nameData a b)) (ap2 A p (nameData (shifted a b N) b))

@[simp] theorem subst_rawSum {l : ℕ} (σ : Fin n → PTm l) (p N a b : PTm n) :
    Syn.subst σ (rawSum p N a b) = rawSum (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b) :=
  by simp [rawSum]
@[simp] theorem subst_endpoint {l : ℕ} (σ : Fin n → PTm l) (p N a b : PTm n) :
    Syn.subst σ (endpoint p N a b) = endpoint (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b) :=
  by simp [endpoint]

theorem a_at (p a b i : PTm n) :
    Γ ⊢[PRAAx] inst2 aBody i (sampleData p a b) ≐ ap2 A p (nameData (shifted a b i) b) := by
  simpa [aBody,rowSample,inst2] using row_at (Γ := Γ) A (nameData (var 0) (var 1)) p a b i

theorem d_at (p a b i : PTm n) :
    Γ ⊢[PRAAx] inst2 dBody i (sampleData p a b) ≐ ap2 D p (GaussianStirlingDifference.data (shifted a b i) b) := by
  simpa [dBody,rowSample,inst2] using row_at (Γ := Γ) D (GaussianStirlingDifference.data (var 0) (var 1)) p a b i

def backward (f : PTm 2) : PTm 2 := qsub (inst2 f (var 0) (var 1)) (inst2 f (succ (var 0)) (var 1))
@[simp] theorem backward_at (f : PTm 2) (i x : PTm n) :
    inst2 (backward f) i x = qsub (inst2 f i x) (inst2 f (succ i) x) := by
  change Syn.subst ![i,x] (backward f) = _
  simp only [backward,GaussianRationalMetric.subst_qsub,subst_inst2,ConciseIPRA.PTm.subst_succ,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]

private def backwardLaw (f : PTm 2) (x j : PTm n) : Fm PTm n :=
  sum (backward f) j x ≐ qsub (inst2 f zero x) (inst2 f j x)
@[simp] private theorem subst_backwardLaw {l : ℕ} (σ : Fin n → PTm l) (f : PTm 2) (x j : PTm n) :
    (backwardLaw f x j).subst σ = backwardLaw f (Syn.subst σ x) (Syn.subst σ j) := by simp [backwardLaw]

theorem backward_sum (f : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] sum (backward f) N x ≐ qsub (inst2 f zero x) (inst2 f N x) := by
  have all : Γ ⊢[PRAAx] .all (backwardLaw f (Syn.shift x) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_backwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (GaussianRationalFiniteSum.sum_zero (backward f) x).eqTrans (GaussianCoefficientNormOrder.qsub_self _).eqSymm
    · simp only [subst_backwardLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let X := Syn.shift x
      let i : PTm (n+1) := var 0
      let Δ := backwardLaw f X i :: Γ.map Fm.shift
      change Δ ⊢[PRAAx] sum (backward f) (succ i) X ≐ qsub (inst2 f zero X) (inst2 f (succ i) X)
      have ih : Δ ⊢[PRAAx] sum (backward f) i X ≐ qsub (inst2 f zero X) (inst2 f i X) := Prf.hyp0
      refine (GaussianRationalFiniteSum.sum_succ (backward f) i X).eqTrans ?_
      rw [backward_at]
      exact (qadd_congr ih (.eqRefl _)).eqTrans (GaussianReconstructionRoots.difference_chain _ _ _)
  change Γ ⊢[PRAAx] backwardLaw f x N
  simpa only [subst_backwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem endpoint_sum (p N a b : PTm n) :
    Γ ⊢[PRAAx] sum (backward aBody) N (sampleData p a b) ≐ endpoint p N a b := by
  have e : Γ ⊢[PRAAx] shifted a b zero ≐ a := by unfold shifted; ipra_ring
  have align : Γ ⊢[PRAAx] nameData (shifted a b zero) b ≐ nameData a b := by
    simpa using Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (nameData (var 0) (var 1) : PTm 2)
      (σ := ![shifted a b zero,b]) (σ' := ![a,b]) (fun j => by fin_cases j; exact e; exact .eqRefl _)
  exact (backward_sum aBody N (sampleData p a b)).eqTrans
    (qsub_congr ((a_at p a b zero).eqTrans (congrAp2 A (.eqRefl _) align))
      (a_at p a b N))

def errorNumerator (p s : PTm n) : PTm n := unit s+num 7*unit p
def errorDenominator (p s : PTm n) : PTm n := unit s*unit p

@[simp] theorem subst_errorNumerator {l : ℕ} (σ : Fin n → PTm l) (p s : PTm n) :
    Syn.subst σ (errorNumerator p s) = errorNumerator (Syn.subst σ p) (Syn.subst σ s) := by simp [errorNumerator]
@[simp] theorem subst_errorDenominator {l : ℕ} (σ : Fin n → PTm l) (p s : PTm n) :
    Syn.subst σ (errorDenominator p s) = errorDenominator (Syn.subst σ p) (Syn.subst σ s) := by simp [errorDenominator]

theorem error_denominator_positive (p s : PTm n) : Γ ⊢[PRAAx] le one (errorDenominator p s) :=
  positive_product _ _ (unit_positive s) (unit_positive p)

theorem local_error (p s a b : PTm n) (h : Γ ⊢[PRAAx] source a b) (step : Γ ⊢[PRAAx] stepLaw a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 D p (GaussianStirlingDifference.data a b))
      (qsub (ap2 A s (nameData a b)) (ap2 A s (nameData (a+b) b))) (errorNumerator p s) (errorDenominator p s) := by
  let X := ap2 D p (GaussianStirlingDifference.data a b)
  let Y := ap2 G s (stepData a b)
  let Z := qsub (ap2 A s (nameData a b)) (ap2 A s (nameData (a+b) b))
  let U := unit s
  let V := unit p
  have hd := error_denominator_positive (Γ := Γ) p s
  have row : Γ ⊢[PRAAx] distanceBounded Y X (U+V) (U*V) :=
    cross_at G D (stepData a b) (GaussianStirlingDifference.data a b) s p step
  have raw := GaussianNamedDifference.sample_error A A (nameData a b) (nameData (a+b) b) s
    (name_regular a b h) (name_regular (a+b) b (source_shift a b h))
  have scale : Γ ⊢[PRAAx] distanceBounded Y Z (num 6*V) (U*V) :=
    distance_radius_mono _ _ _ _ _ _ (unit_positive s) hd (by ipra_le 0) raw
  exact distance_congr (.eqRefl X) (.eqRefl Z) (by unfold errorNumerator; ipra_ring) (.eqRefl _)
    (distance_triangle_same X Y Z (U+V) (num 6*V) (U*V) hd (distance_symmetric _ _ _ _ hd row) scale)

theorem error_rows (p s N a b : PTm n) (h : Γ ⊢[PRAAx] source a b) (hs : Γ ⊢[PRAAx] localRows N a b) :
    Γ ⊢[PRAAx] termsDistance dBody (backward aBody) N (sampleData p a b) (sampleData s a b)
      (errorNumerator p s) (errorDenominator p s) := by
  refine .allI (.impI ?_)
  let l := Syn.shift a
  let b' := Syn.shift b
  let J := Syn.shift N
  let P := Syn.shift p
  let S := Syn.shift s
  let i : PTm (n+1) := var 0
  let Δ := lt i J :: Γ.map Fm.shift
  let c := shifted l b' i
  have hsrc : Δ ⊢[PRAAx] source l b' := by simpa [Fm.shift,Syn.shift,Δ,l,b'] using h.shift.wk
  have hr : Δ ⊢[PRAAx] localRows J l b' := by simpa [Fm.shift,Syn.shift,Δ,l,b',J] using hs.shift.wk
  have step : Δ ⊢[PRAAx] stepLaw c b' := rows_at J l b' i hr Prf.hyp0
  have face := local_error P S c b' (shifted_source l b' i hsrc) step
  have e : Δ ⊢[PRAAx] shifted l b' (succ i) ≐ c+b' := by
    dsimp only [c,shifted]
    ipra_ring
  have q := Prf.eqCongr (Γ := Δ) (Ax := PRAAx) (nameData (var 0) (var 1) : PTm 2)
    (σ := ![shifted l b' (succ i),b']) (σ' := ![c+b',b']) (fun j => by fin_cases j; exact e; exact .eqRefl _)
  have read : Δ ⊢[PRAAx] inst2 (backward aBody) i (sampleData S l b') ≐
      qsub (ap2 A S (nameData c b')) (ap2 A S (nameData (c+b') b')) := by
    rw [backward_at]
    exact qsub_congr (a_at S l b' i) ((a_at S l b' (succ i)).eqTrans
      (congrAp2 A (.eqRefl _) (by simpa using q)))
  simpa [termsDistance,Syn.shift,Δ,l,b',J,P,S,i] using
    distance_congr (d_at P l b' i).eqSymm read.eqSymm (.eqRefl _) (.eqRefl _) face

theorem independent_error (p s N a b : PTm n) (h : Γ ⊢[PRAAx] source a b) (hs : Γ ⊢[PRAAx] localRows N a b) :
    Γ ⊢[PRAAx] distanceBounded (rawSum p N a b) (endpoint s N a b)
      (N*errorNumerator p s) (errorDenominator p s) :=
  distance_congr (.eqRefl _) (endpoint_sum s N a b) (.eqRefl _) (.eqRefl _)
    (sum_distance dBody (backward aBody) N (sampleData p a b) (sampleData s a b)
      (errorNumerator p s) (errorDenominator p s) (error_denominator_positive p s) (error_rows p s N a b h hs))

theorem diagonal_error (p N a b : PTm n) (h : Γ ⊢[PRAAx] source a b) (hs : Γ ⊢[PRAAx] localRows N a b) :
    Γ ⊢[PRAAx] distanceBounded (rawSum p N a b) (endpoint p N a b) (num 8*N) (unit p) := by
  apply distance_radius_mono _ _ _ _ _ _ (error_denominator_positive p p) (unit_positive p) _ (independent_error p p N a b h hs)
  unfold errorNumerator errorDenominator
  ipra_le 0

theorem actual_Stirling_finite_telescope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((source (var 1) (var 0) ⋏ localRows (var 2) (var 1) (var 0)) ⟶
      distanceBounded (rawSum (var 4) (var 2) (var 1) (var 0)) (endpoint (var 3) (var 2) (var 1) (var 0))
        (var 2*errorNumerator (var 4) (var 3)) (errorDenominator (var 4) (var 3))) :=
  closeUniv 5 (.impI (independent_error _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianStirlingTelescope
