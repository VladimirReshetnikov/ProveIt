import GowersSzemeredi.Definitions
import Mathlib.Analysis.Complex.Basic

/-! A normalized finite Fejer kernel, expanded over pairs of frequencies.
The pair expansion keeps every coefficient nonnegative without needing an
analytic convergence theorem. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def finiteFejerKernel {N : Nat} [NeZero N] (L : Nat) (x : ZMod N) : Real :=
  ‖∑ i : Fin L, exponential ((i : ZMod N) * x)‖ ^ 2 / (L : Real) ^ 2

theorem finiteFejerKernel_nonneg {N L : Nat} [NeZero N] (x : ZMod N) :
    0 ≤ finiteFejerKernel L x := by unfold finiteFejerKernel; positivity

theorem finiteFejerKernel_le_one {N L : Nat} [NeZero N] (hL : 0 < L) (x : ZMod N) :
    finiteFejerKernel L x ≤ 1 := by
  have hnorm : ‖∑ i : Fin L, exponential ((i : ZMod N) * x)‖ ≤ L := by
    calc
      _ ≤ ∑ i : Fin L, ‖exponential ((i : ZMod N) * x)‖ := norm_sum_le _ _
      _ = _ := by
        simp only [exponential, AddChar.norm_apply, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, mul_one]
  unfold finiteFejerKernel
  exact (div_le_one (by positivity)).mpr (pow_le_pow_left₀ (norm_nonneg _) hnorm 2)

theorem finiteFejerKernel_expansion {N L : Nat} [NeZero N] (x : ZMod N) :
    (finiteFejerKernel L x : Complex) =
      ((L : Complex) ^ 2)⁻¹ *
        ∑ i : Fin L, ∑ j : Fin L, exponential (((i : ZMod N) - (j : ZMod N)) * x) := by
  have hsquare : ((‖∑ i : Fin L, exponential ((i : ZMod N) * x)‖ ^ 2 : Real) : Complex) =
      ∑ i : Fin L, ∑ j : Fin L, exponential (((i : ZMod N) - (j : ZMod N)) * x) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    unfold exponential
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [finiteFejerKernel, Complex.ofReal_div, hsquare]
  push_cast
  ring

end LeanProofs.GowersSzemeredi
