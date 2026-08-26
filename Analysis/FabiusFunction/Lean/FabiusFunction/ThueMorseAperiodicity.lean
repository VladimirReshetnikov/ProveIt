import FabiusFunction.ThueMorseValuation

/-!
# Aperiodicity of the Thue--Morse sequence

The signed Thue--Morse sequence is not eventually periodic.  This is the
elementary combinatorial heart of the atlas's words chapter: the proof
needs only two exact identities of the corpus, block concatenation and
dyadic reflection.

The argument follows the atlas.  First, an eventual period upgrades to a
global one: adding `2^m` to the index only flips every sign, so a
periodicity valid beyond `2^m` reflects back to the whole sequence.
Second, a global period `p` is impossible: reflection in dyadic blocks
gives `ε(2^m - p) = (-1)^m ε(p-1)`, while periodicity forces this to be
`ε(2^m) = -1` for every large `m` — and the right side changes sign
between consecutive `m`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The sign at a power of two: a single one-bit gives `ε(2^m) = -1`. -/
@[simp] theorem thueMorseSign_two_pow (m : ℕ) :
    thueMorseSign (2 ^ m) = -1 := by
  have h := binaryWeight_add_pow_two m 0 (by positivity)
  rw [Nat.add_zero] at h
  rw [thueMorseSign, h]
  simp [binaryWeight]

/-- Adding a full block length flips every Thue--Morse sign. -/
theorem thueMorseSign_two_pow_add (m x : ℕ) (hx : x < 2 ^ m) :
    thueMorseSign (2 ^ m + x) = -thueMorseSign x := by
  have h := thueMorseSign_block_concat m 1 x hx
  rw [one_mul] at h
  rw [h, show thueMorseSign 1 = -1 by simp [thueMorseSign, binaryWeight]]
  ring

/-- An eventual period of the signed Thue--Morse sequence is a global
period: the block-flip identity transports periodicity from beyond any
threshold back to the whole sequence. -/
theorem thueMorseSign_period_of_eventually (p N : ℕ)
    (h : ∀ n, N ≤ n → thueMorseSign (n + p) = thueMorseSign n) :
    ∀ r, thueMorseSign (r + p) = thueMorseSign r := by
  intro r
  obtain ⟨m, hm⟩ : ∃ m, N ≤ 2 ^ m ∧ r + p < 2 ^ m := by
    refine ⟨N + r + p, ?_, ?_⟩
    · exact le_of_lt (lt_of_le_of_lt (by omega : N ≤ N + r + p)
        Nat.lt_two_pow_self)
    · calc r + p ≤ N + r + p := by omega
        _ < 2 ^ (N + r + p) := Nat.lt_two_pow_self
  obtain ⟨hmN, hmr⟩ := hm
  have hper := h (2 ^ m + r) (le_trans hmN (by omega))
  rw [show 2 ^ m + r + p = 2 ^ m + (r + p) by ring,
    thueMorseSign_two_pow_add m (r + p) hmr,
    thueMorseSign_two_pow_add m r (by omega)] at hper
  have := neg_injective hper
  exact this

/-- **Aperiodicity.**  The signed Thue--Morse sequence is not eventually
periodic: no positive period is valid from any threshold on. -/
theorem thueMorseSign_not_eventually_periodic :
    ¬ ∃ p N : ℕ, 0 < p ∧
      ∀ n, N ≤ n → thueMorseSign (n + p) = thueMorseSign n := by
  rintro ⟨p, N, hp, h⟩
  have hglobal := thueMorseSign_period_of_eventually p N h
  -- Reflection identity: for every `m` with `p ≤ 2^m`,
  -- `-1 = ε(2^m) = ε(2^m - p) = (-1)^m ε(p-1)`.
  have key : ∀ m : ℕ, p ≤ 2 ^ m →
      (-1 : ℤ) ^ m * thueMorseSign (p - 1) = -1 := by
    intro m hm
    have hper : thueMorseSign (2 ^ m - p + p) = thueMorseSign (2 ^ m - p) :=
      hglobal (2 ^ m - p)
    rw [show 2 ^ m - p + p = 2 ^ m by omega] at hper
    have hrefl := thueMorseSign_dyadic_complement m (p - 1)
      (by have := Nat.one_le_two_pow (n := m); omega)
    rw [show 2 ^ m - 1 - (p - 1) = 2 ^ m - p by omega] at hrefl
    rw [← hper, thueMorseSign_two_pow] at hrefl
    exact hrefl.symm
  -- The right side flips between consecutive block levels.
  obtain ⟨m, hm⟩ : ∃ m, p ≤ 2 ^ m :=
    ⟨p, le_of_lt Nat.lt_two_pow_self⟩
  have h1 := key m hm
  have h2 := key (m + 1) (le_trans hm (Nat.pow_le_pow_right (by omega) (by omega)))
  rw [pow_succ] at h2
  nlinarith [h1, h2]

end Fabius
