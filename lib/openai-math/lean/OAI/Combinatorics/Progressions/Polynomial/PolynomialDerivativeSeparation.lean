/- Modified for ProveIt: use MvPolynomial.coeff_zero explicitly on Lean 4.32.
Mathematical statements are unchanged. -/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*}

theorem polynomial_eq_zero_of_pderiv_closed
    (S : Set (MvPolynomial σ ℚ))
    (hderiv : ∀ p ∈ S, ∀ i, pderiv i p ∈ S)
    (hconstant : ∀ p ∈ S, p.coeff 0 = 0) : ∀ p ∈ S, p = 0 := by
  classical
  have hcoeff : ∀ α : σ →₀ ℕ, ∀ p ∈ S, p.coeff α = 0 := by
    intro α
    induction α using Finsupp.induction with
    | zero => exact hconstant
    | @single_add i n α hi hn ih =>
      have hsteps : ∀ m : ℕ, ∀ p ∈ S, p.coeff (Finsupp.single i m + α) = 0 := by
        intro m
        induction m with
        | zero => simpa using ih
        | succ m ihm =>
          intro p hp
          have h := ihm (pderiv i p) (hderiv p hp i)
          rw [coeff_pderiv] at h
          have hindex : Finsupp.single i (m + 1) + α =
              (Finsupp.single i m + α) + Finsupp.single i 1 := by
            rw [Finsupp.single_add]
            abel
          rw [hindex]
          apply (mul_eq_zero.mp h).resolve_right
          exact_mod_cast Nat.succ_ne_zero ((Finsupp.single i m + α) i)
      exact hsteps n
  intro p hp
  ext α
  simpa only [MvPolynomial.coeff_zero] using hcoeff α p hp

theorem polynomial_submodule_eq_bot_of_pderiv_closed
    (W : Submodule ℚ (MvPolynomial σ ℚ))
    (hderiv : ∀ p ∈ W, ∀ i, pderiv i p ∈ W)
    (hconstant : ∀ p ∈ W, p.coeff 0 = 0) : W = ⊥ := by
  apply le_antisymm
  · intro p hp
    exact (Submodule.mem_bot ℚ).mpr
      (polynomial_eq_zero_of_pderiv_closed W hderiv hconstant p hp)
  · exact bot_le

end Erdos3

end

end OAI
