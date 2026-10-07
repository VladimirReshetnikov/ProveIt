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
  have hLr : (0 : Real) < L := by exact_mod_cast hL
  have hnorm : ‖∑ i : Fin L, exponential ((i : ZMod N) * x)‖ ≤ L := by
    calc
      _ ≤ ∑ i : Fin L, ‖exponential ((i : ZMod N) * x)‖ := norm_sum_le _ _
      _ = _ := by
        simp only [exponential, AddChar.norm_apply, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, mul_one]
  unfold finiteFejerKernel
  apply (div_le_one (by positivity)).mpr
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

theorem finiteFejerKernel_zero {N L : Nat} [NeZero N] (hL : 0 < L) :
    finiteFejerKernel (N := N) L 0 = 1 := by
  have hLr : (L : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  simp [finiteFejerKernel, exponential, hLr]

theorem finiteFejerKernel_expansion {N L : Nat} [NeZero N] (x : ZMod N) :
    (finiteFejerKernel L x : Complex) =
      ((L : Complex) ^ 2)⁻¹ *
        ∑ i : Fin L, ∑ j : Fin L, exponential (((i : ZMod N) - (j : ZMod N)) * x) := by
  have hstar (y : ZMod N) : star (exponential y) = exponential (-y) := by
    simpa only [exponential, starRingEnd_apply] using
      (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := N)) y).symm
  have hsquare : ((‖∑ i : Fin L, exponential ((i : ZMod N) * x)‖ ^ 2 : Real) : Complex) =
      ∑ i : Fin L, ∑ j : Fin L, exponential (((i : ZMod N) - (j : ZMod N)) * x) := by
    calc
      _ = (∑ i : Fin L, exponential ((i : ZMod N) * x)) *
          star (∑ j : Fin L, exponential ((j : ZMod N) * x)) := by
            rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow]
      _ = ∑ i : Fin L, ∑ j : Fin L,
          exponential ((i : ZMod N) * x) * exponential (-((j : ZMod N) * x)) := by
            simp only [star_sum, hstar, Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        unfold exponential
        rw [← AddChar.map_add_eq_mul (ZMod.stdAddChar (N := N))]
        congr 1
        ring
  unfold finiteFejerKernel
  rw [Complex.ofReal_div, hsquare]
  push_cast
  ring

end LeanProofs.GowersSzemeredi
