import FabiusFunction.PhiRealSign
import FabiusFunction.LatticeFiber
import FabiusFunction.OnePeakPerLobe

/-!
# The sign of `Φ` is constant on each lobe, and its parity is counted

Combining the sign formula of `PhiRealSign` with the fiber count of
`LatticeFiber`: the exceptional block `lobeExceptional c` depends only
on `⌊c⌋₊`, hence is constant along a lobe, and it decomposes into the
fibers over `1, …, m`.  Therefore on the lobe `(m, m+1)`

`Φ(x) = (−1)^{N(m)}·‖Φ(x)‖`,  `N(m) = ∑_{k=1}^{m} (v₂(k) + 1)`,

a single sign for the whole lobe; and crossing the integer `m` flips
the sign exactly `v₂(m)+1` times — matching the zero order of
`PhiZeroOrder`, so `Φ` changes sign at `m` precisely when that order is
odd.

* `lobeExceptional_eq_of_floor_eq`, `lobeExceptional_eq_biUnion`.
* `card_lobeExceptional` — **the count** `∑_{k≤m} (v₂(k)+1)`.
* `rvachevFourierProduct_eq_lobe_sign_mul_norm` — **one sign per
  lobe**.
* `card_lobeExceptional_succ` — the sign flip equals the zero order.
-/

set_option autoImplicit false

open Filter Topology Real Set

namespace Fabius

/-! ## The exceptional block depends only on the floor -/

/-- Equal natural floors `⌊c⌋₊ = ⌊d⌋₊` give equal exceptional blocks. -/
theorem lobeExceptional_eq_of_floor_eq {c d : ℝ}
    (h : ⌊c⌋₊ = ⌊d⌋₊) : lobeExceptional c = lobeExceptional d := by
  unfold lobeExceptional
  rw [h]

/-- Along the lobe `(m, m+1)` the exceptional block is the one of
`m`. -/
theorem lobeExceptional_abs_eq_of_mem_lobe {m : ℕ} {x : ℝ}
    (hx : x ∈ Set.Ioo (m:ℝ) ((m:ℝ) + 1)) :
    lobeExceptional |x| = lobeExceptional (m:ℝ) := by
  obtain ⟨hx1, hx2⟩ := hx
  have hm0 : (0:ℝ) ≤ (m:ℝ) := by positivity
  have hx0 : 0 < x := lt_of_le_of_lt hm0 hx1
  have habs : |x| = x := abs_of_pos hx0
  apply lobeExceptional_eq_of_floor_eq
  rw [habs, Nat.floor_natCast]
  exact (Nat.floor_eq_iff hx0.le).mpr ⟨hx1.le, hx2⟩

/-! ## The fiber decomposition -/

/-- At an integer threshold `m`, the exceptional block is the union of the fibers
`lobeFiber k` over `1 ≤ k ≤ m`. -/
theorem lobeExceptional_eq_biUnion (m : ℕ) :
    lobeExceptional (m:ℝ) = (Finset.Icc 1 m).biUnion lobeFiber := by
  ext p
  rw [Finset.mem_biUnion,
    mem_lobeExceptional_iff (by positivity : (0:ℝ) ≤ (m:ℝ))]
  constructor
  · intro hp
    refine ⟨2 ^ p.1 * (p.2 + 1), ?_, (mem_lobeFiber_iff p).mpr rfl⟩
    rw [Finset.mem_Icc]
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    · have : ((2 ^ p.1 * (p.2 + 1) : ℕ) : ℝ) ≤ (m:ℝ) := hp
      exact_mod_cast this
  · rintro ⟨k, hk, hpk⟩
    rw [Finset.mem_Icc] at hk
    have hval := (mem_lobeFiber_iff p).mp hpk
    have : ((2 ^ p.1 * (p.2 + 1) : ℕ) : ℝ) ≤ (m:ℝ) := by
      rw [hval]
      exact_mod_cast hk.2
    exact this

/-- The lattice fibers over distinct integers in `Finset.Icc 1 m` are disjoint. -/
theorem pairwiseDisjoint_lobeFiber (m : ℕ) :
    ((Finset.Icc 1 m : Finset ℕ) : Set ℕ).PairwiseDisjoint lobeFiber := by
  intro k _ l _ hkl
  rw [Function.onFun, Finset.disjoint_left]
  intro p hpk hpl
  exact hkl (((mem_lobeFiber_iff p).mp hpk).symm.trans
    ((mem_lobeFiber_iff p).mp hpl))

/-- **The count**: the lattice points at or below `m` number
`∑_{k=1}^{m} (v₂(k) + 1)`. -/
theorem card_lobeExceptional (m : ℕ) :
    (lobeExceptional (m:ℝ)).card =
      ∑ k ∈ Finset.Icc 1 m, (padicValNat 2 k + 1) := by
  classical
  rw [lobeExceptional_eq_biUnion m,
    Finset.card_biUnion (pairwiseDisjoint_lobeFiber m)]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  exact card_lobeFiber k (Finset.mem_Icc.mp hk).1

/-! ## One sign per lobe -/

/-- **The sign of `Φ` is constant on the lobe `(m, m+1)`**, equal to
`(−1)` to the number of lattice points at or below `m`. -/
theorem rvachevFourierProduct_eq_lobe_sign_mul_norm {m : ℕ} {x : ℝ}
    (hx : x ∈ Set.Ioo (m:ℝ) ((m:ℝ) + 1)) :
    rvachevFourierProduct (x : ℂ) =
      (((-1 : ℝ) ^ (∑ k ∈ Finset.Icc 1 m, (padicValNat 2 k + 1)) *
        ‖rvachevFourierProduct (x : ℂ)‖ : ℝ) : ℂ) := by
  have hlat := lobeZero_ne_abs_of_mem_lobe hx
  conv_lhs => rw [rvachevFourierProduct_eq_sign_mul_norm hlat]
  rw [lobeExceptional_abs_eq_of_mem_lobe hx, card_lobeExceptional m]

/-- **The sign flip across `m` is the zero order**: passing from the
lobe below `m` to the lobe above it multiplies the sign exponent by
`v₂(m) + 1`, the exact vanishing order of `Φ` at `m`. -/
theorem card_lobeExceptional_succ (m : ℕ) (hm : 1 ≤ m) :
    (lobeExceptional (m:ℝ)).card =
      (lobeExceptional ((m:ℝ) - 1)).card + (padicValNat 2 m + 1) := by
  have hcast : ((m:ℝ) - 1) = ((m - 1 : ℕ) : ℝ) := by
    have : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    rw [Nat.cast_sub hm, Nat.cast_one]
  rw [hcast, card_lobeExceptional, card_lobeExceptional]
  have hIcc : Finset.Icc 1 m =
      insert m (Finset.Icc 1 (m - 1)) := by
    ext k
    rw [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      rcases eq_or_lt_of_le h2 with rfl | h
      · exact Or.inl rfl
      · exact Or.inr ⟨h1, by omega⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨hm, le_refl _⟩
      · exact ⟨h1, by omega⟩
  have hnot : m ∉ Finset.Icc 1 (m - 1) := by
    rw [Finset.mem_Icc]
    omega
  rw [hIcc, Finset.sum_insert hnot]
  ring

end Fabius
