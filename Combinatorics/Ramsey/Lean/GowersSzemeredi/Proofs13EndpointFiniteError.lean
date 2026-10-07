import GowersSzemeredi.Definitions
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Expect

/-! Finite disagreement probabilities and a modal-value selector for the
additive correction argument. All averages are uniform and finite. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def endpointError {A H : Type*} [Fintype A] [DecidableEq H] (u v : A → H) : Real :=
  𝔼 a : A, if u a = v a then 0 else 1

theorem endpoint_expect_prod {A B : Type*} [Fintype A] [Fintype B] (f : A × B → Real) :
    (𝔼 p : A × B, f p) = 𝔼 a : A, 𝔼 b : B, f (a, b) := by
  simpa only [Finset.univ_product_univ] using Finset.expect_product Finset.univ Finset.univ f

theorem endpointError_nonneg {A H : Type*} [Fintype A] [DecidableEq H] (u v : A → H) :
    0 ≤ endpointError u v := by
  apply Finset.expect_nonneg
  intro a _
  split_ifs <;> norm_num

theorem endpointError_le_one {A H : Type*} [Fintype A] [Nonempty A] [DecidableEq H] (u v : A → H) :
    endpointError u v ≤ 1 := by
  apply Finset.expect_le Finset.univ_nonempty
  intro a _
  split_ifs <;> norm_num

theorem endpointError_self {A H : Type*} [Fintype A] [DecidableEq H] (u : A → H) :
    endpointError u u = 0 := by simp [endpointError]

theorem endpointError_symm {A H : Type*} [Fintype A] [DecidableEq H] (u v : A → H) :
    endpointError u v = endpointError v u := by
  unfold endpointError
  apply Finset.expect_congr rfl
  intro a _
  simp only [eq_comm]

theorem endpointError_triangle {A H : Type*} [Fintype A] [DecidableEq H] (u v w : A → H) :
    endpointError u w ≤ endpointError u v + endpointError v w := by
  unfold endpointError
  rw [← Finset.expect_add_distrib]
  apply Finset.expect_le_expect
  intro a _
  by_cases huv : u a = v a <;> by_cases hvw : v a = w a <;> by_cases huw : u a = w a <;>
    simp_all

theorem endpointError_const {A H : Type*} [Fintype A] [Nonempty A] [DecidableEq H] (u v : H) :
    endpointError (fun _ : A => u) (fun _ : A => v) = if u = v then 0 else 1 := by
  exact Fintype.expect_const _

theorem endpointError_equiv {A B H : Type*} [Fintype A] [Fintype B] [DecidableEq H]
    (e : A ≃ B) (u v : B → H) : endpointError (u ∘ e) (v ∘ e) = endpointError u v := by
  exact Fintype.expect_equiv e _ _ (fun _ => rfl)

theorem endpoint_exists_modalValue {A H : Type*} [Fintype A] [Fintype H] [Nonempty H] [DecidableEq H]
    (u : A → H) : ∃ h : H, ∀ k, endpointError u (fun _ => h) ≤ endpointError u (fun _ => k) := by
  obtain ⟨h, _, hh⟩ := Finset.exists_min_image Finset.univ
    (fun h => endpointError u (fun _ => h)) Finset.univ_nonempty
  exact ⟨h, fun k => hh k (Finset.mem_univ _)⟩

def endpointModalValue {A H : Type*} [Fintype A] [Fintype H] [Nonempty H] [DecidableEq H]
    (u : A → H) : H := Classical.choose (endpoint_exists_modalValue u)

theorem endpointModalValue_min {A H : Type*} [Fintype A] [Fintype H] [Nonempty H] [DecidableEq H]
    (u : A → H) (k : H) :
    endpointError u (fun _ => endpointModalValue u) ≤ endpointError u (fun _ => k) :=
  Classical.choose_spec (endpoint_exists_modalValue u) k

theorem endpointModalValue_error_le_collision {A H : Type*}
    [Fintype A] [Nonempty A] [Fintype H] [Nonempty H] [DecidableEq H] (u : A → H) :
    endpointError u (fun _ => endpointModalValue u) ≤
      endpointError (fun p : A × A => u p.1) (fun p : A × A => u p.2) := by
  unfold endpointError
  rw [endpoint_expect_prod, Finset.expect_comm]
  apply Finset.le_expect Finset.univ_nonempty
  intro a _
  exact endpointModalValue_min u (u a)

end LeanProofs.GowersSzemeredi
