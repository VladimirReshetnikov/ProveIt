import FabiusFunction.PhiZeroOrder

/-!
# Simple zeros at odd integers, deep zeros at powers of two

The two extremes of the audits' two-adic valley picture, read off from
the exact zero order `v₂(m)+1` of `PhiZeroOrder`:

* at an **odd** integer `Φ` has a *simple* zero;
* at `m = 2^j` the zero has order `j+1`, so the order is unbounded
  along the dyadic integers — the local mechanism behind the deepening
  valleys of `|Φ|` at highly divisible frequencies.

The constant is the explicit one of `PhiZeroOrder`; here it is packaged
existentially, which is the form the valley statements actually use.

* `exists_pos_tendsto_zero_order` — the packaged zero order.
* `zero_order_odd` — simple zeros at odd integers.
* `zero_order_two_pow` — order `j+1` at `2^j`.
* `exists_zero_order_ge` — the order is unbounded.
-/

set_option autoImplicit false

open Filter Topology Real Set

namespace Fabius

/-- **The zero order, packaged**: `‖Φ(x)‖/|x−m|^{v₂(m)+1}` tends to a
strictly positive constant. -/
theorem exists_pos_tendsto_zero_order (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧
      Tendsto (fun x : ℝ => ‖rvachevFourierProduct (x:ℂ)‖ /
        |x - (m:ℝ)| ^ (padicValNat 2 m + 1)) (𝓝[≠] (m:ℝ)) (𝓝 C) :=
  ⟨_, Real.exp_pos _, tendsto_norm_div_pow_zero_order m hm⟩

/-- **Simple zeros at odd integers**: for odd `m`, `‖Φ(x)‖/|x−m|`
tends to a positive constant. -/
theorem zero_order_odd {m : ℕ} (hm : 1 ≤ m) (hodd : ¬ 2 ∣ m) :
    ∃ C : ℝ, 0 < C ∧
      Tendsto (fun x : ℝ => ‖rvachevFourierProduct (x:ℂ)‖ /
        |x - (m:ℝ)|) (𝓝[≠] (m:ℝ)) (𝓝 C) := by
  obtain ⟨C, hC, h⟩ := exists_pos_tendsto_zero_order m hm
  refine ⟨C, hC, ?_⟩
  rw [padicValNat.eq_zero_of_not_dvd hodd] at h
  simpa using h

/-- **Deep zeros at powers of two**: at `m = 2^j` the vanishing order
is exactly `j + 1`. -/
theorem zero_order_two_pow (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      Tendsto (fun x : ℝ => ‖rvachevFourierProduct (x:ℂ)‖ /
        |x - ((2 ^ j : ℕ) : ℝ)| ^ (j + 1))
        (𝓝[≠] (((2 ^ j : ℕ)) : ℝ)) (𝓝 C) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C, hC, h⟩ :=
    exists_pos_tendsto_zero_order (2 ^ j) Nat.one_le_two_pow
  refine ⟨C, hC, ?_⟩
  rwa [padicValNat.prime_pow] at h

/-- **The vanishing order is unbounded over the integers**. -/
theorem exists_zero_order_ge (N : ℕ) :
    ∃ m : ℕ, 1 ≤ m ∧ N ≤ padicValNat 2 m + 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨2 ^ N, Nat.one_le_two_pow, ?_⟩
  rw [padicValNat.prime_pow]
  exact Nat.le_succ N

end Fabius
