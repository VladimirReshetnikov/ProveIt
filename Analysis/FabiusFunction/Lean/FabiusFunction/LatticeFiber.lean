import FabiusFunction.LobeLogFactorization
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The fiber of the dyadic zero lattice over an integer

The lattice `{2ʰ(r+1)}` hits the integer `m ≥ 1` exactly
`v₂(m) + 1` times — once for each dyadic divisor `2ʰ ∣ m`.  This
Finset (`lobeFiber`) is the multiplicity bookkeeping for the zero of
`Φ` at `m`: the audits' `prop:canonical` multiplicity `1 + v₂(m)`, in
pair-lattice form.

* `lobeFiber`, `mem_lobeFiber_iff`, `mem_lobeFiber_iff_lobeZero`.
* `card_lobeFiber` — **the multiplicity count** `v₂(m) + 1`.
-/

set_option autoImplicit false

open Filter Topology Real Set

namespace Fabius

/-- The pairs of the dyadic lattice sitting exactly over `m`. -/
def lobeFiber (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter
    (fun p => 2 ^ p.1 * (p.2 + 1) = m)

theorem mem_lobeFiber_iff {m : ℕ} (p : ℕ × ℕ) :
    p ∈ lobeFiber m ↔ 2 ^ p.1 * (p.2 + 1) = m := by
  unfold lobeFiber
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_range]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    have h1 : 2 ^ p.1 ≤ m :=
      h ▸ Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    have h2 : p.2 + 1 ≤ m :=
      h ▸ Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    exact ⟨⟨lt_of_lt_of_le Nat.lt_two_pow_self
      (Nat.le_succ_of_le h1),
      Nat.lt_succ_of_lt (Nat.lt_of_succ_le h2)⟩, h⟩

theorem mem_lobeFiber_iff_lobeZero {m : ℕ} (p : ℕ × ℕ) :
    p ∈ lobeFiber m ↔ lobeZero p = (m:ℝ) := by
  rw [mem_lobeFiber_iff]
  simp only [lobeZero]
  exact ⟨fun h => by exact_mod_cast congrArg (fun k : ℕ => (k:ℝ)) h,
    fun h => by exact_mod_cast h⟩

/-- **The multiplicity count**: the lattice hits `m ≥ 1` exactly
`v₂(m) + 1` times. -/
theorem card_lobeFiber (m : ℕ) (hm : 1 ≤ m) :
    (lobeFiber m).card = padicValNat 2 m + 1 := by
  have hm0 : m ≠ 0 := Nat.one_le_iff_ne_zero.mp hm
  have hdvd_iff : ∀ h : ℕ, 2 ^ h ∣ m ↔ h ≤ padicValNat 2 m :=
    fun h => padicValNat_dvd_iff_le_of_ne_one
      (by norm_num : (2:ℕ) ≠ 1) hm0
  symm
  rw [← Finset.card_range (padicValNat 2 m + 1)]
  apply Finset.card_bij
    (fun (h : ℕ) (_ : h ∈ Finset.range (padicValNat 2 m + 1)) =>
      ((h, m / 2 ^ h - 1) : ℕ × ℕ))
  · intro h hh
    rw [Finset.mem_range, Nat.lt_succ_iff] at hh
    have hdvd : 2 ^ h ∣ m := (hdvd_iff h).mpr hh
    have hle : 2 ^ h ≤ m := Nat.le_of_dvd (by omega) hdvd
    have hq1 : 1 ≤ m / 2 ^ h :=
      (Nat.one_le_div_iff (Nat.two_pow_pos h)).mpr hle
    rw [mem_lobeFiber_iff]
    show 2 ^ h * (m / 2 ^ h - 1 + 1) = m
    rw [Nat.sub_add_cancel hq1]
    exact Nat.mul_div_cancel' hdvd
  · intro h₁ hh₁ h₂ hh₂ heq
    exact congrArg Prod.fst heq
  · rintro ⟨h, r⟩ hp
    rw [mem_lobeFiber_iff] at hp
    have hdvd : 2 ^ h ∣ m := ⟨r + 1, hp.symm⟩
    have hh : h ≤ padicValNat 2 m := (hdvd_iff h).mp hdvd
    have hq : m / 2 ^ h = r + 1 := by
      rw [← hp, Nat.mul_div_cancel_left _ (Nat.two_pow_pos h)]
    refine ⟨h, Finset.mem_range.mpr (Nat.lt_succ_of_le hh), ?_⟩
    have hr : m / 2 ^ h - 1 = r := by omega
    rw [hr]
