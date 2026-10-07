import GowersSzemeredi.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Finite quantitative density iteration with an explicit backward length
threshold. The argument keeps the gain and power-loss constants fixed. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The exact length sufficient for a prescribed number of increments. -/
def densityIterationThreshold (T c rho : Real) : Nat → Real
  | 0 => max 1 T
  | n + 1 => max (max 1 T) ((densityIterationThreshold T c rho n / c) ^ rho⁻¹)

theorem densityIterationThreshold_one_le (T c rho : Real) (n : Nat) :
    1 ≤ densityIterationThreshold T c rho n := by
  cases n with
  | zero => exact le_max_left _ _
  | succ n => exact (le_max_left _ _).trans (le_max_left _ _)

theorem densityIterationThreshold_step {T c rho x : Real} (hc : 0 < c) (hρ : 0 < rho)
    (n : Nat) (hx : densityIterationThreshold T c rho (n + 1) ≤ x) :
    T ≤ x ∧ densityIterationThreshold T c rho n ≤ c * x ^ rho := by
  have hT := ((le_max_right 1 T).trans (le_max_left _ _)).trans hx
  have hroot : (densityIterationThreshold T c rho n / c) ^ rho⁻¹ ≤ x := (le_max_right _ _).trans hx
  have hn : 0 ≤ densityIterationThreshold T c rho n :=
    (by norm_num : (0 : Real) ≤ 1).trans (densityIterationThreshold_one_le T c rho n)
  have hp : densityIterationThreshold T c rho n / c ≤ x ^ rho := by
    calc
      _ = ((densityIterationThreshold T c rho n / c) ^ rho⁻¹) ^ rho :=
        (Real.rpow_inv_rpow (div_nonneg hn hc.le) hρ.ne').symm
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg (div_nonneg hn hc.le) _) hroot hρ.le
  exact ⟨hT, by simpa only [mul_comm] using (div_le_iff₀ hc).mp hp⟩

/-- An abstract density-increment interface with exact progression transport. -/
def IntervalDensityStep (k : Nat) (delta gain c rho T : Real) : Prop :=
  ∀ (L : Nat), T ≤ L → ∀ (B : Finset (Fin L)) (d : Real), delta ≤ d → d * L ≤ B.card →
    HasNatAP (B.image Fin.val) k ∨ ∃ l : Nat, ∃ B' : Finset (Fin l),
      c * (L : Real) ^ rho ≤ l ∧ (d + gain) * l ≤ B'.card ∧
      (HasNatAP (B'.image Fin.val) k → HasNatAP (B.image Fin.val) k)

/-- After n increments the lower density would exceed one, so one of the
preceding stages must already contain the desired progression. -/
theorem hasNatAP_of_density_iteration {k : Nat} {delta gain c rho T : Real}
    (hgain : 0 ≤ gain) (hc : 0 < c) (hρ : 0 < rho)
    (hstep : IntervalDensityStep k delta gain c rho T)
    (n : Nat) (L : Nat) (hL : densityIterationThreshold T c rho n ≤ L)
    (B : Finset (Fin L)) (d : Real) (hd : delta ≤ d) (hcard : d * L ≤ B.card)
    (hend : 1 < d + (n : Real) * gain) : HasNatAP (B.image Fin.val) k := by
  induction n generalizing L d with
  | zero =>
    have hLpos : (0 : Real) < L := lt_of_lt_of_le (by norm_num)
      ((densityIterationThreshold_one_le T c rho 0).trans hL)
    have hd1 : 1 < d := by simpa using hend
    have hB : (B.card : Real) ≤ L := by
      exact_mod_cast (show B.card ≤ L by simpa using Finset.card_le_univ B)
    have hm := mul_lt_mul_of_pos_right hd1 hLpos
    linarith
  | succ n ih =>
    obtain ⟨hT, hnext⟩ := densityIterationThreshold_step hc hρ n hL
    rcases hstep L hT B d hd hcard with hAP | ⟨l, B', hsize, hinc, hback⟩
    · exact hAP
    · apply hback
      apply ih l (hnext.trans hsize) B' (d + gain) (by linarith) hinc
      push_cast at hend
      linarith

end LeanProofs.GowersSzemeredi
