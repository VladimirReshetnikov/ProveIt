import FabiusFunction.ThueMorseValuation
import FabiusFunction.ThueMorseOverlapFree

/-!
# Aperiodicity of the Thue--Morse sequence

The signed Thue--Morse sequence is not eventually periodic.  This is the
elementary combinatorial heart of the atlas's words chapter.

Aperiodicity is now a corollary of the strictly stronger overlap-freeness
proved in `ThueMorseOverlapFree`, through the general word-combinatorial
implication `not_eventually_periodic_of_overlap_free`, valid over any
alphabet: an eventual period `p ≥ 1` from a threshold `N` on turns the
window `f(N), …, f(N + 2p)` into an overlap of period `p`, because every
index `N + j` with `j ≤ p` already lies past the threshold.  Here that
implication is instantiated at `thueMorseSign`.

The file also keeps the dyadic block-flip identities on which the earlier
self-contained proof of aperiodicity ran, and which remain useful on
their own:

* `thueMorseSign_two_pow` — a single one-bit gives `ε(2^m) = -1`.
* `thueMorseSign_two_pow_add` — adding a full block length flips every
  sign: `ε(2^m + x) = -ε(x)` for `x < 2^m`.
* `thueMorseSign_period_of_eventually` — an eventual period is already a
  global one: the block-flip identity reflects a periodicity valid beyond
  any threshold back to the whole sequence.
* `thueMorseSign_not_eventually_periodic` — the theorem, deduced from
  `thueMorseSign_overlap_free`.
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
periodic: no positive period is valid from any threshold on.  This is the
specialization to `thueMorseSign` of the general implication
`not_eventually_periodic_of_overlap_free`, fed with Thue's theorem
`thueMorseSign_overlap_free`. -/
theorem thueMorseSign_not_eventually_periodic :
    ¬ ∃ p N : ℕ, 0 < p ∧
      ∀ n, N ≤ n → thueMorseSign (n + p) = thueMorseSign n :=
  not_eventually_periodic_of_overlap_free thueMorseSign
    thueMorseSign_overlap_free

end Fabius
