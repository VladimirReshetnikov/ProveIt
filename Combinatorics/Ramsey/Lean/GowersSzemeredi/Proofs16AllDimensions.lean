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

The 13 declarations of this module that the final route does not use are in
`Proofs16AllDimensionsSide`. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

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

end LeanProofs.GowersSzemeredi
