import FabiusFunction.LatticeFiber
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# The regular part of `log ‖Φ‖` near an integer zero

Analytic preliminaries for the zero-order theorem at `m ≥ 1`: on the
half-width window `(m−½, m+½)`,

* points other than `m` avoid the whole lattice
  (`lobeZero_ne_abs_near`);
* the lattice tail (`a ≥ m+1`) contributes a **continuous** sum
  (`continuousOn_zero_order_tail`) — uniform gap
  `1 − x²/a² ≥ 1 − (m+½)²/(m+1)²` and the `|log(1−u)| ≤ u/c` bracket
  feed `continuous_tsum` on the window subspace;
* the finitely many low factors (`a ≤ m`, `a ≠ m`) are individually
  continuous at `m` (`continuousAt_exceptional_factor`).
-/

set_option autoImplicit false

open Filter Topology Real Set

namespace Fabius

/-- On the punctured half-width window around `m`, no lattice value is
hit. -/
theorem lobeZero_ne_abs_near {m : ℕ} (hm : 1 ≤ m) {x : ℝ}
    (hx : x ∈ Set.Ioo ((m:ℝ) - 1/2) ((m:ℝ) + 1/2)) (hne : x ≠ (m:ℝ))
    (p : ℕ × ℕ) : lobeZero p ≠ |x| := by
  obtain ⟨hx1, hx2⟩ := hx
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hx0 : 0 < x := by linarith
  rw [abs_of_pos hx0]
  rcases lt_trichotomy (2 ^ p.1 * (p.2 + 1)) m with h | h | h
  · -- `a ≤ m − 1 < x`
    have hle : (2 ^ p.1 * (p.2 + 1) : ℕ) + 1 ≤ m := h
    have : ((2 ^ p.1 * (p.2 + 1) : ℕ) : ℝ) + 1 ≤ (m:ℝ) := by
      exact_mod_cast hle
    have : lobeZero p ≤ (m:ℝ) - 1 := by
      simp only [lobeZero]
      linarith
    exact ne_of_lt (by linarith)
  · -- `a = m ≠ x`
    have : lobeZero p = (m:ℝ) := by
      simp only [lobeZero]
      exact_mod_cast congrArg (fun k : ℕ => (k:ℝ)) h
    rw [this]
    exact fun hc => hne hc.symm
  · -- `a ≥ m + 1 > x`
    have hle : m + 1 ≤ 2 ^ p.1 * (p.2 + 1) := h
    have : (m:ℝ) + 1 ≤ lobeZero p := by
      simp only [lobeZero]
      exact_mod_cast hle
    exact ne_of_gt (by linarith)

/-- Off the exceptional set of the integer `m`, lattice values jump to
`m+1`. -/
theorem add_one_le_lobeZero_of_not_mem {m : ℕ} {p : ℕ × ℕ}
    (hp : p ∉ lobeExceptional (m:ℝ)) : (m:ℝ) + 1 ≤ lobeZero p := by
  have h := floor_succ_le_lobeZero_of_not_mem
    (by positivity : (0:ℝ) ≤ (m:ℝ)) hp
  rwa [Nat.floor_natCast, Nat.cast_add, Nat.cast_one] at h

/-- The fiber sits inside the exceptional set. -/
theorem lobeFiber_subset_exceptional (m : ℕ) :
    lobeFiber m ⊆ lobeExceptional (m:ℝ) := by
  intro p hp
  rw [mem_lobeFiber_iff_lobeZero] at hp
  rw [mem_lobeExceptional_iff (by positivity : (0:ℝ) ≤ (m:ℝ))]
  rw [hp]

/-- **Continuity of the lattice tail** on the half-width window. -/
theorem continuousOn_zero_order_tail (m : ℕ) :
    ContinuousOn (fun x : ℝ =>
      ∑' p : {p : ℕ × ℕ // p ∉ lobeExceptional (m:ℝ)},
        Real.log (1 - x ^ 2 / (lobeZero p.val) ^ 2))
      (Set.Ioo ((m:ℝ) - 1/2) ((m:ℝ) + 1/2)) := by
  have hm0 : (0:ℝ) ≤ (m:ℝ) := by positivity
  have hc₂ : (0:ℝ) < 1 - ((m:ℝ) + 1/2) ^ 2 / ((m:ℝ) + 1) ^ 2 := by
    have hsq : ((m:ℝ) + 1/2) ^ 2 < ((m:ℝ) + 1) ^ 2 := by nlinarith
    have := (div_lt_one (by positivity :
      (0:ℝ) < ((m:ℝ) + 1) ^ 2)).mpr hsq
    linarith
  -- bounds valid at every point of the window, every tail pair
  have hkey : ∀ (p : {p : ℕ × ℕ // p ∉ lobeExceptional (m:ℝ)})
      (x : ↥(Set.Ioo ((m:ℝ) - 1/2) ((m:ℝ) + 1/2))),
      ‖Real.log (1 - (x:ℝ) ^ 2 / (lobeZero p.val) ^ 2)‖ ≤
        (((m:ℝ) + 1/2) ^ 2 /
          (1 - ((m:ℝ) + 1/2) ^ 2 / ((m:ℝ) + 1) ^ 2)) *
          (1 / (lobeZero p.val) ^ 2) := by
    intro p x
    obtain ⟨hx1, hx2⟩ := x.property
    have hxabs : |(x:ℝ)| ≤ (m:ℝ) + 1/2 := by
      rw [abs_le]
      constructor <;> [linarith; linarith]
    have hxsq : (x:ℝ) ^ 2 ≤ ((m:ℝ) + 1/2) ^ 2 := by
      calc (x:ℝ) ^ 2 = |(x:ℝ)| ^ 2 := (sq_abs _).symm
        _ ≤ ((m:ℝ) + 1/2) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hxabs 2
    have ha := add_one_le_lobeZero_of_not_mem p.property
    have ha0 := lobeZero_pos p.val
    have hasq : ((m:ℝ) + 1) ^ 2 ≤ (lobeZero p.val) ^ 2 :=
      pow_le_pow_left₀ (by positivity) ha 2
    have hu : (x:ℝ) ^ 2 / (lobeZero p.val) ^ 2 ≤
        ((m:ℝ) + 1/2) ^ 2 / ((m:ℝ) + 1) ^ 2 := by
      gcongr
    have hgap : 1 - ((m:ℝ) + 1/2) ^ 2 / ((m:ℝ) + 1) ^ 2 ≤
        1 - (x:ℝ) ^ 2 / (lobeZero p.val) ^ 2 := by linarith
    have hbr := abs_log_one_sub_le
      (u := (x:ℝ) ^ 2 / (lobeZero p.val) ^ 2)
      (c := 1 - ((m:ℝ) + 1/2) ^ 2 / ((m:ℝ) + 1) ^ 2)
      (by positivity) hc₂ hgap
    rw [Real.norm_eq_abs]
    calc |Real.log (1 - (x:ℝ) ^ 2 / (lobeZero p.val) ^ 2)| ≤
        ((x:ℝ) ^ 2 / (lobeZero p.val) ^ 2) /
          (1 - ((m:ℝ) + 1/2) ^ 2 / ((m:ℝ) + 1) ^ 2) := hbr
      _ ≤ (((m:ℝ) + 1/2) ^ 2 / (lobeZero p.val) ^ 2) /
          (1 - ((m:ℝ) + 1/2) ^ 2 / ((m:ℝ) + 1) ^ 2) := by
          gcongr
      _ = (((m:ℝ) + 1/2) ^ 2 /
          (1 - ((m:ℝ) + 1/2) ^ 2 / ((m:ℝ) + 1) ^ 2)) *
          (1 / (lobeZero p.val) ^ 2) := by ring
  rw [continuousOn_iff_continuous_restrict]
  apply continuous_tsum
    (u := fun p : {p : ℕ × ℕ // p ∉ lobeExceptional (m:ℝ)} =>
      (((m:ℝ) + 1/2) ^ 2 /
        (1 - ((m:ℝ) + 1/2) ^ 2 / ((m:ℝ) + 1) ^ 2)) *
        (1 / (lobeZero p.val) ^ 2))
  · intro p
    apply Continuous.log
    · exact continuous_const.sub
        ((continuous_subtype_val.pow 2).div_const _)
    · intro x
      obtain ⟨hx1, hx2⟩ := x.property
      have ha := add_one_le_lobeZero_of_not_mem p.property
      have hfpos : 0 < 1 - (x:ℝ) ^ 2 / (lobeZero p.val) ^ 2 := by
        apply factor_pos_of_abs_lt
        rw [abs_lt]
        constructor
        · have := lobeZero_pos p.val
          linarith
        · linarith
      exact hfpos.ne'
  · exact (summable_inv_sq_lobeZero.mul_left _).comp_injective
      Subtype.val_injective
  · exact fun p x => hkey p x

/-- The low factors (`a ≤ m`, off the fiber) are continuous at `m`. -/
theorem continuousAt_exceptional_factor {m : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ lobeExceptional (m:ℝ) \ lobeFiber m) :
    ContinuousAt
      (fun x : ℝ => Real.log (1 - x ^ 2 / (lobeZero p) ^ 2))
      (m:ℝ) := by
  obtain ⟨hpE, hpF⟩ := Finset.mem_sdiff.mp hp
  have hne : lobeZero p ≠ (m:ℝ) := by
    intro hc
    exact hpF ((mem_lobeFiber_iff_lobeZero p).mpr hc)
  have hle : lobeZero p ≤ (m:ℝ) :=
    (mem_lobeExceptional_iff (by positivity) p).mp hpE
  have hlt : lobeZero p < (m:ℝ) := lt_of_le_of_ne hle hne
  have hm0 : (0:ℝ) ≤ (m:ℝ) := by positivity
  have hf0 : 1 - (m:ℝ) ^ 2 / (lobeZero p) ^ 2 ≠ 0 := by
    apply (factor_neg_of_lt_abs ?_).ne
    rwa [abs_of_nonneg hm0]
  exact (continuous_const.sub
    ((continuous_pow 2).div_const _)).continuousAt.log hf0

end Fabius
