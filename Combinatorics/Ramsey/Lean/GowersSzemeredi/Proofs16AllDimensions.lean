import GowersSzemeredi.Proofs16ClassStepDegrees

/-! Theorem 16.2 and Corollary 16.11 in every dimension, from the family
Lemma 16.6 in every dimension (Notes L.6, E6).

* `step_degrees_le`: the three degrees of the step sum to at most
  `2^(k+7)·D²·P²`.
* `classDeg k = 2^(2^(2^(k+5)))` is closed under the step
  (`step_degree_closed`). It is the degree of the uniform class in dimension
  `k ≥ 2`.
* `classV Kc pc k = 1 + Σ_{j<k} (Kc j + pc j)` is its base.
* `powerUniformClass_all`: a uniform class in every dimension `k ≥ 2`, by
  induction from `powerUniformClass_two` with `powerUniformClass_succ`.
* `theorem_16_2_of_family_lemmas`: `theorem_16_2`. Dimensions `0, 1` are
  `theorem_16_2_zero` and `lemma_16_3_holds`. Every `k ≥ 2` follows from the
  class via `PowerUniformClass.theorem162At_tower`, because
  `classDeg k + k + 1 ≤ 2^(2^(2^(k+6)))`. The family-lemma constants only
  need `Kc k + pc k ≤ 2^(2^(2^(k+5)))`.
* `corollary_16_11_of_family_lemmas`: `corollary_16_11`.

`classDeg_add_le`, `corollary_16_11_of_family_lemmas`, `powerUniformClass_all`,
`stepP_ge9`, `step_degree_closed`, `step_degrees_le`,
`theorem_16_2_of_family_lemmas` and `theorem_16_2_of_profiles_all` are in
`Proofs16AllDimensionsSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### The degree recursion -/

theorem stepT_le_sq (k : Nat) : stepT k ≤ stepP k * stepP k := by
  unfold stepT stepP
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by rw [pow_succ 2 (k + 5)]; omega)

/-- The degree of the uniform class in dimension `k`: `2^(2^(2^(k+5)))`. -/
def classDeg (k : Nat) : Nat := 2 ^ (2 ^ (2 ^ (k + 5)))

theorem two_pow_ge_double {a : Nat} (ha : 1 ≤ a) : 2 * a ≤ 2 ^ a := by
  have h : a - 1 < 2 ^ (a - 1) := Nat.lt_two_pow_self
  have h2 : 2 ^ a = 2 * 2 ^ (a - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

theorem classDeg_pos (k : Nat) : 1 ≤ classDeg k := Nat.one_le_two_pow

/-! ### The base -/

/-- The base of the class in dimension `k`: `1 + Σ_{j<k} (Kc j + pc j)`. -/
def classV (Kc pc : Nat → Nat) (k : Nat) : Real :=
  1 + ∑ j ∈ Finset.range k, ((Kc j : Real) + pc j)

theorem one_le_classV (Kc pc : Nat → Nat) (k : Nat) : 1 ≤ classV Kc pc k := by
  unfold classV
  have : 0 ≤ ∑ j ∈ Finset.range k, ((Kc j : Real) + pc j) :=
    Finset.sum_nonneg fun j _ => by positivity
  linarith

theorem classV_succ (Kc pc : Nat → Nat) (k : Nat) :
    classV Kc pc (k + 1) = classV Kc pc k + ((Kc k : Real) + pc k) := by
  unfold classV
  rw [Finset.sum_range_succ]
  ring

theorem classV_le_succ (Kc pc : Nat → Nat) (k : Nat) : classV Kc pc k ≤ classV Kc pc (k + 1) := by
  rw [classV_succ]
  have : (0 : Real) ≤ (Kc k : Real) + pc k := by positivity
  linarith

theorem const_le_classV_succ (Kc pc : Nat → Nat) (k : Nat) :
    (Kc k : Real) ≤ classV Kc pc (k + 1) ∧ (pc k : Real) ≤ classV Kc pc (k + 1) := by
  rw [classV_succ]
  have h1 := one_le_classV Kc pc k
  constructor <;> linarith

/-! ### Every dimension -/

theorem classV_bound (Kc pc : Nat → Nat)
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5)))) {k : Nat}
    (hk : 2 ≤ k) :
    2 * classV Kc pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)) - 1) := by
  set E := (2 : Nat) ^ ((2 : Nat) ^ (k + 4))
  have hterm : ∀ j ∈ Finset.range k, (Kc j : Real) + pc j ≤ 2 ^ E := by
    intro j hj
    have hjk : j + 5 ≤ k + 4 := by have := Finset.mem_range.mp hj; omega
    refine (hconst j).trans (pow_le_pow_right₀ (by norm_num) ?_)
    exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hjk)
  have hsum : ∑ j ∈ Finset.range k, ((Kc j : Real) + pc j) ≤ k * 2 ^ E := by
    have := Finset.sum_le_sum hterm
    rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  have hk2 : (2 : Real) * (k + 1) ≤ 2 ^ (k + 2) := by
    have h : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
    have h' : ((k + 1 : Nat) : Real) < ((2 ^ (k + 1) : Nat) : Real) := by exact_mod_cast h
    push_cast at h'
    rw [pow_succ]; linarith
  have hE1 : (1 : Real) ≤ 2 ^ E := one_le_pow₀ (by norm_num)
  have hstep : 2 * classV Kc pc k ≤ 2 ^ (E + k + 2) := by
    unfold classV
    rw [show E + k + 2 = E + (k + 2) by ring, pow_add]
    nlinarith
  refine hstep.trans (pow_le_pow_right₀ (by norm_num) ?_)
  have hEk : E + k + 3 ≤ (2 : Nat) ^ ((2 : Nat) ^ (k + 6)) := by
    have h4 : (2 : Nat) ^ (k + 6) = 2 ^ (k + 4) * 4 := by
      rw [show k + 6 = (k + 4) + 2 by omega, pow_add]; norm_num
    have hE4 : (2 : Nat) ^ ((2 : Nat) ^ (k + 6)) = E ^ 4 := by rw [h4, pow_mul]
    have hEk' : k + 4 < E := lt_of_lt_of_le Nat.lt_two_pow_self
      (Nat.pow_le_pow_right (by norm_num) (Nat.lt_two_pow_self (n := k + 4)).le)
    rw [hE4]
    have hE2 : 2 ≤ E := by omega
    nlinarith [Nat.mul_le_mul hE2 hE2]
  omega

end LeanProofs.GowersSzemeredi
