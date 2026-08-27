import FabiusFunction.FabiusLambertSaddle
import FabiusFunction.GeometricLagrangeWeights

/-!
# Phase-locked Lambert nodes and reciprocal Richardson weights

The lower-Lambert coordinate is the exact inverse of

`y ↦ y * 2 ^ (-y)`

on the decreasing branch `1 / log 2 < y`.  Sampling this map at the additive
lattice `lambda + j` therefore locks every one-periodic phase exactly, rather
than merely asymptotically.

The second half of the file develops the finite algebra behind extrapolation
on the reciprocal nodes

`h_j = (lambda + j)⁻¹`,  `0 ≤ j ≤ r`.

The interpolation layer is deliberately field-generic.  The canonical
weights are Mathlib Lagrange-basis evaluations at zero.  Their total mass,
inverse-power cancellation, and first omitted moment follow from the shared
Lagrange exactness API.  Only the closed factorial/binomial formula needs the
natural nonvanishing condition on the shifted denominators.  No asymptotic
expansion, uniformity assertion, or remainder estimate is made here.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset Set Function

noncomputable section

/-! ## Exact phase locking on the lower Lambert branch -/

/-- The physical argument whose lower-Lambert phase is intended to be
`lambda + j`. -/
noncomputable def lambertPhaseLockedNode (lambda : ℝ) (j : ℕ) : ℝ :=
  (lambda + j) * (2 : ℝ) ^ (-(lambda + j))

private theorem lowerLambertNode_spec {y : ℝ}
    (hy : 1 < Real.log 2 * y) :
    y * (2 : ℝ) ^ (-y) ∈
        Ioo (0 : ℝ) (Real.exp (-1) / Real.log 2) ∧
      fabiusLambertPhase (y * (2 : ℝ) ^ (-y)) = y := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hy0 : 0 < y := by nlinarith
  let u : ℝ := Real.log 2 * y
  let x : ℝ := y * (2 : ℝ) ^ (-y)
  have hu : 1 < u := hy
  have hx : 0 < x := by
    dsimp [x]
    exact mul_pos hy0 (Real.rpow_pos_of_pos (by norm_num) _)
  have hrpow : (2 : ℝ) ^ (-y) = Real.exp (-u) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    dsimp [u]
    ring
  have hux : Real.log 2 * x = u * Real.exp (-u) := by
    dsimp [x, u]
    rw [hrpow]
    ring
  have hlt : u * Real.exp (-u) < Real.exp (-1) := by
    have hexp : u < Real.exp (u - 1) := by
      have h := Real.add_one_lt_exp (by linarith : u - 1 ≠ 0)
      simpa only [sub_add_cancel] using h
    have hmul := mul_lt_mul_of_pos_right hexp (Real.exp_pos (-u))
    calc
      u * Real.exp (-u) < Real.exp (u - 1) * Real.exp (-u) := hmul
      _ = Real.exp (-1) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hxsmall : x < Real.exp (-1) / Real.log 2 := by
    apply (lt_div_iff₀ hL).2
    rw [mul_comm, hux]
    exact hlt
  have hz : -(Real.log 2 * x) ∈ Ioo (-Real.exp (-1)) 0 := by
    constructor
    · rw [hux]
      linarith
    · exact neg_lt_zero.mpr (mul_pos hL hx)
  have hw : -u < -1 := neg_lt_neg hu
  have heq : (-u) * Real.exp (-u) = -(Real.log 2 * x) := by
    rw [hux]
    ring
  have hunique := lowerLambertW_unique hz hw heq
  refine ⟨⟨hx, hxsmall⟩, ?_⟩
  unfold fabiusLambertPhase paperLambertN
  rw [← hunique]
  dsimp [u]
  field_simp [hL.ne']

private lemma one_lt_log_two_mul_phaseLockedParameter
    {lambda : ℝ} (hlambda : (Real.log 2)⁻¹ < lambda) (j : ℕ) :
    1 < Real.log 2 * (lambda + j) := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbase := mul_lt_mul_of_pos_left hlambda hL
  have hshift : Real.log 2 * lambda ≤
      Real.log 2 * (lambda + (j : ℝ)) := by
    gcongr
    positivity
  calc
    1 = Real.log 2 * (Real.log 2)⁻¹ := (mul_inv_cancel₀ hL.ne').symm
    _ < Real.log 2 * lambda := hbase
    _ ≤ Real.log 2 * (lambda + (j : ℝ)) := hshift

/-- Every phase-locked node lies strictly inside the positive lower-Lambert
domain.  The strict hypothesis on `lambda` excludes the branch point once and
then works uniformly for every natural translate. -/
theorem lambertPhaseLockedNode_mem_lowerBranch
    {lambda : ℝ} (hlambda : (Real.log 2)⁻¹ < lambda) (j : ℕ) :
    lambertPhaseLockedNode lambda j ∈
      Ioo (0 : ℝ) (Real.exp (-1) / Real.log 2) := by
  exact (lowerLambertNode_spec
    (one_lt_log_two_mul_phaseLockedParameter hlambda j)).1

/-- Exact lower-Lambert inversion on the additive phase lattice:
`phase ((lambda + j) * 2 ^ (-(lambda + j))) = lambda + j`. -/
theorem fabiusLambertPhase_phaseLockedNode
    {lambda : ℝ} (hlambda : (Real.log 2)⁻¹ < lambda) (j : ℕ) :
    fabiusLambertPhase (lambertPhaseLockedNode lambda j) = lambda + j := by
  exact (lowerLambertNode_spec
    (one_lt_log_two_mul_phaseLockedParameter hlambda j)).2

/-- A one-periodic function has exactly the same value at every lower-Lambert
phase-locked node as at the base phase `lambda`.  The codomain is arbitrary:
this is a purely algebraic consequence of exact inversion and periodicity. -/
theorem Periodic.apply_fabiusLambertPhase_phaseLockedNode
    {A : Type*} {G : ℝ → A} (hG : Periodic G 1)
    {lambda : ℝ} (hlambda : (Real.log 2)⁻¹ < lambda) (j : ℕ) :
    G (fabiusLambertPhase (lambertPhaseLockedNode lambda j)) = G lambda := by
  rw [fabiusLambertPhase_phaseLockedNode hlambda j]
  simpa only [Nat.cast_ofNat, mul_one] using (hG.nat_mul j lambda)

/-- Functional form of exact phase locking: sampling any one-periodic
function along all phase-locked nodes gives the constant sequence `G lambda`. -/
theorem Periodic.comp_fabiusLambertPhase_phaseLockedNode
    {A : Type*} {G : ℝ → A} (hG : Periodic G 1)
    {lambda : ℝ} (hlambda : (Real.log 2)⁻¹ < lambda) :
    (fun j : ℕ ↦ G
      (fabiusLambertPhase (lambertPhaseLockedNode lambda j))) =
      fun _ : ℕ ↦ G lambda := by
  funext j
  exact hG.apply_fabiusLambertPhase_phaseLockedNode hlambda j

/-! ## Reciprocal Lagrange nodes -/

/-- The shifted reciprocal node `h_j = (lambda + j)⁻¹` over a field. -/
def shiftedReciprocalNode
    {K : Type*} [Field K] (lambda : K) (j : ℕ) : K :=
  (lambda + j)⁻¹

/-- Evaluation-at-zero Lagrange weight on the reciprocal nodes
`(lambda + j)⁻¹`, indexed by `0 ≤ j ≤ r`. -/
noncomputable def shiftedReciprocalLagrangeWeight
    {K : Type*} [Field K] (lambda : K) (r j : ℕ) : K :=
  lagrangeEvalWeight (Finset.range (r + 1))
    (shiftedReciprocalNode lambda) 0 j

/-- Shifted reciprocal nodes are pairwise distinct over every
characteristic-zero field.  This does not require the shifts to be nonzero:
inversion itself is injective in a field, including at zero. -/
theorem shiftedReciprocalNode_injOn
    {K : Type*} [Field K] [CharZero K] (lambda : K) (r : ℕ) :
    Set.InjOn (shiftedReciprocalNode lambda)
      (Finset.range (r + 1)) := by
  intro i _hi j _hj hij
  have hshift : lambda + (i : K) = lambda + (j : K) :=
    inv_injective hij
  have hcast : (i : K) = (j : K) := add_left_cancel hshift
  exact Nat.cast_injective hcast

private lemma prod_natCast_sub_erase
    {K : Type*} [Field K] [CharZero K]
    {r j : ℕ} (hj : j ≤ r) :
    (∏ k ∈ (Finset.range (r + 1)).erase j,
        ((j : K) - (k : K))) =
      (-1 : K) ^ (r - j) * (j.factorial : K) *
        ((r - j).factorial : K) := by
  classical
  have herase : (Finset.range (r + 1)).erase j =
      Finset.range j ∪ Finset.Ico (j + 1) (r + 1) := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union,
      Finset.mem_Ico]
    omega
  have hdisjoint : Disjoint (Finset.range j)
      (Finset.Ico (j + 1) (r + 1)) := by
    rw [Finset.disjoint_left]
    intro k hk hkj
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Ico] at hkj
    omega
  have hleft :
      (∏ k ∈ Finset.range j, ((j : K) - (k : K))) =
        (j.factorial : K) := by
    calc
      (∏ k ∈ Finset.range j, ((j : K) - (k : K))) =
          ∏ k ∈ Finset.range j,
            (((j - 1 - k + 1 : ℕ) : K)) := by
        apply Finset.prod_congr rfl
        intro k hk
        have hkj : k ≤ j := (Finset.mem_range.mp hk).le
        rw [← Nat.cast_sub hkj]
        congr 1
        omega
      _ = ∏ k ∈ Finset.range j, (((k + 1 : ℕ) : K)) :=
        Finset.prod_range_reflect
          (fun k : ℕ ↦ (((k + 1 : ℕ) : K))) j
      _ = (j.factorial : K) := by
        rw [← Finset.prod_natCast,
          Finset.prod_range_add_one_eq_factorial]
  have hright :
      (∏ k ∈ Finset.Ico (j + 1) (r + 1),
          ((j : K) - (k : K))) =
        (-1 : K) ^ (r - j) * ((r - j).factorial : K) := by
    rw [Finset.prod_Ico_eq_prod_range]
    have hsub : r + 1 - (j + 1) = r - j := by omega
    rw [hsub]
    calc
      (∏ k ∈ Finset.range (r - j),
          ((j : K) - ((j + 1 + k : ℕ) : K))) =
          ∏ k ∈ Finset.range (r - j),
            -(((k + 1 : ℕ) : K)) := by
        apply Finset.prod_congr rfl
        intro k _hk
        push_cast
        ring
      _ = (-1 : K) ^ (r - j) *
          ∏ k ∈ Finset.range (r - j), (((k + 1 : ℕ) : K)) := by
        rw [Finset.prod_neg, Finset.card_range]
      _ = (-1 : K) ^ (r - j) *
          ((r - j).factorial : K) := by
        rw [← Finset.prod_natCast,
          Finset.prod_range_add_one_eq_factorial]
  rw [herase, Finset.prod_union hdisjoint, hleft, hright]
  ring

private lemma reciprocalLagrangeFactor
    {K : Type*} [Field K] [CharZero K]
    {lambda : K} {j k : ℕ}
    (hlambdaJ : lambda + (j : K) ≠ 0)
    (hlambdaK : lambda + (k : K) ≠ 0) (hkj : k ≠ j) :
    (-shiftedReciprocalNode lambda k) /
        (shiftedReciprocalNode lambda j -
          shiftedReciprocalNode lambda k) =
      (lambda + (j : K)) / ((j : K) - (k : K)) := by
  have hshift : lambda + (j : K) ≠ lambda + (k : K) := by
    intro heq
    have hcast : (j : K) = (k : K) := add_left_cancel heq
    exact hkj (Nat.cast_injective hcast).symm
  have hinvShift : (lambda + (j : K))⁻¹ ≠
      (lambda + (k : K))⁻¹ := by
    exact fun heq ↦ hshift (inv_injective heq)
  have hinvDiff : (lambda + (j : K))⁻¹ -
      (lambda + (k : K))⁻¹ ≠ 0 := sub_ne_zero.mpr hinvShift
  have hjk : (j : K) - (k : K) ≠ 0 := by
    intro hzero
    have hcast : (j : K) = (k : K) := sub_eq_zero.mp hzero
    exact hkj (Nat.cast_injective hcast).symm
  unfold shiftedReciprocalNode
  field_simp [hlambdaJ, hlambdaK, hinvDiff, hjk] <;> ring

/-- Factorial closed form of the reciprocal-node Lagrange weight.  The
assumption says precisely that all shifts represented in the interpolation
block are nonzero. -/
theorem shiftedReciprocalLagrangeWeight_eq_factorial
    {K : Type*} [Field K] [CharZero K]
    (lambda : K) (r j : ℕ) (hj : j ≤ r)
    (hlambda : ∀ k ∈ Finset.range (r + 1),
      lambda + (k : K) ≠ 0) :
    shiftedReciprocalLagrangeWeight lambda r j =
      (-1 : K) ^ (r - j) * (lambda + (j : K)) ^ r /
        ((j.factorial : K) * ((r - j).factorial : K)) := by
  classical
  have hjmem : j ∈ Finset.range (r + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj)
  rw [shiftedReciprocalLagrangeWeight,
    lagrangeEvalWeight_eq_product]
  simp only [zero_sub]
  calc
    (∏ k ∈ (Finset.range (r + 1)).erase j,
        (-shiftedReciprocalNode lambda k) /
          (shiftedReciprocalNode lambda j -
            shiftedReciprocalNode lambda k)) =
        ∏ k ∈ (Finset.range (r + 1)).erase j,
          (lambda + (j : K)) / ((j : K) - (k : K)) := by
      apply Finset.prod_congr rfl
      intro k hk
      have hkmem : k ∈ Finset.range (r + 1) :=
        Finset.mem_of_mem_erase hk
      exact reciprocalLagrangeFactor
        (hlambda j hjmem) (hlambda k hkmem)
          (Finset.ne_of_mem_erase hk)
    _ = (lambda + (j : K)) ^ r /
        ((-1 : K) ^ (r - j) * (j.factorial : K) *
          ((r - j).factorial : K)) := by
      rw [Finset.prod_div_distrib,
        prod_natCast_sub_erase hj]
      have hcard : ((Finset.range (r + 1)).erase j).card = r := by
        rw [Finset.card_erase_of_mem hjmem, Finset.card_range]
        omega
      rw [Finset.prod_const, hcard]
    _ = (-1 : K) ^ (r - j) * (lambda + (j : K)) ^ r /
        ((j.factorial : K) * ((r - j).factorial : K)) := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_pow, inv_neg,
        inv_one]
      ring

/-- Binomial closed form of the reciprocal-node Lagrange weight:

`(-1)^(r-j) / r! * choose r j * (lambda + j)^r`.

This is the exact coefficient used by the phase-locked Richardson filter. -/
theorem shiftedReciprocalLagrangeWeight_eq_choose
    {K : Type*} [Field K] [CharZero K]
    (lambda : K) (r j : ℕ) (hj : j ≤ r)
    (hlambda : ∀ k ∈ Finset.range (r + 1),
      lambda + (k : K) ≠ 0) :
    shiftedReciprocalLagrangeWeight lambda r j =
      (-1 : K) ^ (r - j) / (r.factorial : K) *
        (r.choose j : K) * (lambda + (j : K)) ^ r := by
  rw [shiftedReciprocalLagrangeWeight_eq_factorial
    lambda r j hj hlambda]
  have hjfac : (j.factorial : K) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  have hdfac : ((r - j).factorial : K) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (r - j)
  have hrfac : (r.factorial : K) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero r
  have hfactorial :
      (r.choose j : K) * (j.factorial : K) *
          ((r - j).factorial : K) = (r.factorial : K) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
  have hratio :
      (r.choose j : K) / (r.factorial : K) =
        1 / ((j.factorial : K) * ((r - j).factorial : K)) := by
    field_simp [hjfac, hdfac, hrfac] <;>
      simpa [mul_assoc, mul_comm, mul_left_comm] using hfactorial
  calc
    (-1 : K) ^ (r - j) * (lambda + (j : K)) ^ r /
        ((j.factorial : K) * ((r - j).factorial : K)) =
        (-1 : K) ^ (r - j) *
          (1 / ((j.factorial : K) * ((r - j).factorial : K))) *
            (lambda + (j : K)) ^ r := by ring
    _ = (-1 : K) ^ (r - j) *
          ((r.choose j : K) / (r.factorial : K)) *
            (lambda + (j : K)) ^ r := by rw [hratio]
    _ = (-1 : K) ^ (r - j) / (r.factorial : K) *
          (r.choose j : K) * (lambda + (j : K)) ^ r := by ring

/-- Over the reals, positivity of `lambda` supplies all nonvanishing
hypotheses in the binomial weight formula. -/
theorem shiftedReciprocalLagrangeWeight_eq_choose_of_pos
    (lambda : ℝ) (hlambda : 0 < lambda) (r j : ℕ) (hj : j ≤ r) :
    shiftedReciprocalLagrangeWeight lambda r j =
      (-1 : ℝ) ^ (r - j) / (r.factorial : ℝ) *
        (r.choose j : ℝ) * (lambda + (j : ℝ)) ^ r := by
  apply shiftedReciprocalLagrangeWeight_eq_choose lambda r j hj
  intro k _hk
  positivity

/-! ## Exact inverse-power moments -/

/-- Every reciprocal-node moment through degree `r` reproduces evaluation at
zero.  Keeping the right side as `0 ^ d` records normalization at `d = 0`
without a separate convention. -/
theorem sum_shiftedReciprocalLagrangeWeight_mul_pow
    {K : Type*} [Field K] [CharZero K]
    (lambda : K) (r d : ℕ) (hd : d ≤ r) :
    (∑ j ∈ Finset.range (r + 1),
      shiftedReciprocalLagrangeWeight lambda r j *
        shiftedReciprocalNode lambda j ^ d) = (0 : K) ^ d := by
  have hd' : d < (Finset.range (r + 1)).card := by
    simpa only [Finset.card_range] using Nat.lt_succ_iff.mpr hd
  simpa only [shiftedReciprocalLagrangeWeight] using
    sum_lagrangeEvalWeight_mul_pow
      (Finset.range (r + 1)) (shiftedReciprocalNode lambda) 0
      (shiftedReciprocalNode_injOn lambda r) d hd'

/-- The reciprocal-node Richardson weights have total mass one, including
the singleton block `r = 0`. -/
theorem sum_shiftedReciprocalLagrangeWeight_eq_one
    {K : Type*} [Field K] [CharZero K] (lambda : K) (r : ℕ) :
    (∑ j ∈ Finset.range (r + 1),
      shiftedReciprocalLagrangeWeight lambda r j) = 1 := by
  simpa only [pow_zero, mul_one] using
    sum_shiftedReciprocalLagrangeWeight_mul_pow lambda r 0
      (Nat.zero_le r)

/-- Every positive inverse-power moment through order `r` is cancelled
exactly. -/
theorem sum_shiftedReciprocalLagrangeWeight_mul_invPow_eq_zero
    {K : Type*} [Field K] [CharZero K]
    (lambda : K) (r m : ℕ) (hmpos : 0 < m) (hm : m ≤ r) :
    (∑ j ∈ Finset.range (r + 1),
      shiftedReciprocalLagrangeWeight lambda r j *
        (lambda + (j : K))⁻¹ ^ m) = 0 := by
  simpa only [shiftedReciprocalNode, zero_pow hmpos.ne'] using
    sum_shiftedReciprocalLagrangeWeight_mul_pow lambda r m hm

/-- The first inverse-power moment beyond the cancelled range is the signed
reciprocal nodal product.  This identity is valid even if one shift is zero,
because both sides use the field's total inverse. -/
theorem sum_shiftedReciprocalLagrangeWeight_firstOmitted
    {K : Type*} [Field K] [CharZero K] (lambda : K) (r : ℕ) :
    (∑ j ∈ Finset.range (r + 1),
      shiftedReciprocalLagrangeWeight lambda r j *
        (lambda + (j : K))⁻¹ ^ (r + 1)) =
      (-1 : K) ^ r *
        (∏ j ∈ Finset.range (r + 1), lambda + (j : K))⁻¹ := by
  have h := sum_lagrangeEvalWeight_mul_pow_card
    (Finset.range (r + 1)) (shiftedReciprocalNode lambda) 0
    (shiftedReciprocalNode_injOn lambda r)
  simp only [Finset.card_range, shiftedReciprocalLagrangeWeight,
    shiftedReciprocalNode, zero_pow (Nat.succ_ne_zero r), zero_sub] at h
  rw [h, Finset.prod_neg, Finset.card_range,
    Finset.prod_inv_distrib]
  simp only [pow_succ]
  ring

end

end Fabius
