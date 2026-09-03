import Mathlib.Data.Nat.Choose.Lucas
import FabiusFunction.ParityCharacterKernel

/-!
# The parity of `C(h, k)` is periodic in `h`, and the Pascal sign character is 2-automatic

Lucas's theorem at the prime `2` says `C(h, k) ≡ C(h mod 2, k mod 2) · C(h/2, k/2)
(mod 2)`.  Iterating it `m` times, once `k < 2^m` the top factor is `C(·, 0) = 1`
and only the low `m` binary digits of `h` matter:

`C(h, k) mod 2 = C(h mod 2^m, k) mod 2`   whenever `k < 2^m`.

So `h ↦ C(h, k) mod 2` is periodic with period `2^m` — a statement about binomial
coefficients alone, proved here for every `h`, `k`, `m` with `k < 2^m`.

For the Pascal–Rvachev hierarchy this is the missing combinatorial input: the
weights `a_h = C(h, r-1)` of `Φ_r` have an (eventually) periodic parity word,
and `finite_twoKernel_parityCharacter_iff` turns that into finiteness of the
`2`-kernel of the sign character `ε_r`, i.e. `ε_r` is a 2-automatic sequence.
The Thue–Morse sign is the case `r = 1`.
-/

set_option autoImplicit false

namespace PascalParity

/-- **Lucas mod 2, iterated.**  For `k < 2^m`, the parity of `C(h, k)` depends
only on `h mod 2^m`. -/
theorem choose_mod_two_eq_mod_two_pow (m : ℕ) :
    ∀ h k : ℕ, k < 2 ^ m → h.choose k % 2 = (h % 2 ^ m).choose k % 2 := by
  induction m with
  | zero =>
    intro h k hk
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    simp
  | succ m ih =>
    intro h k hk
    -- Lucas at `p = 2`, for `h` and for `h' = h mod 2^(m+1)`
    have hL : h.choose k ≡ (h % 2).choose (k % 2) * (h / 2).choose (k / 2) [MOD 2] :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2)
    have hL' : (h % 2 ^ (m + 1)).choose k ≡
        ((h % 2 ^ (m + 1)) % 2).choose (k % 2) *
          ((h % 2 ^ (m + 1)) / 2).choose (k / 2) [MOD 2] :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2)
    -- the low bit and the shifted residue of `h'` agree with those of `h`
    have hbit : (h % 2 ^ (m + 1)) % 2 = h % 2 :=
      Nat.mod_mod_of_dvd h (dvd_pow_self 2 (Nat.succ_ne_zero m))
    have hshift : (h % 2 ^ (m + 1)) / 2 = (h / 2) % 2 ^ m := by
      rw [pow_succ, mul_comm]
      exact Nat.mod_mul_right_div_self h 2 (2 ^ m)
    -- the induction hypothesis on the shifted residue
    have hk2 : k / 2 < 2 ^ m := by
      rw [Nat.div_lt_iff_lt_mul two_pos, ← pow_succ]
      exact hk
    have hih : (h / 2).choose (k / 2) % 2 = ((h / 2) % 2 ^ m).choose (k / 2) % 2 :=
      ih (h / 2) (k / 2) hk2
    -- assemble
    have hmain : h.choose k ≡ (h % 2 ^ (m + 1)).choose k [MOD 2] := by
      refine hL.trans (Nat.ModEq.trans ?_ hL'.symm)
      rw [hbit, hshift]
      exact Nat.ModEq.mul_left _ hih
    exact hmain

/-- **Periodicity of the parity of binomial coefficients**: for `k < 2^m`,
`C(h + 2^m, k) ≡ C(h, k) (mod 2)`. -/
theorem choose_add_two_pow_mod_two (h k m : ℕ) (hk : k < 2 ^ m) :
    (h + 2 ^ m).choose k % 2 = h.choose k % 2 := by
  rw [choose_mod_two_eq_mod_two_pow m (h + 2 ^ m) k hk,
    choose_mod_two_eq_mod_two_pow m h k hk, Nat.add_mod_right]

end PascalParity

namespace Fabius

/-- **The Pascal parity word is periodic.**  For the weights `a_h = C(h, k)`,
the word `h ↦ a_h mod 2` is periodic with period `2^m` for any `m` with
`k < 2^m` — here `m = k` — so in particular it is eventually periodic.  (The
minimal period is `2^⌈log₂(k+1)⌉`; only the existence of a period is needed
downstream.) -/
theorem eventuallyPeriodic_parityWord_choose (k : ℕ) :
    EventuallyPeriodic (parityWord fun h => h.choose k) :=
  ⟨0, 2 ^ k, by positivity, fun h _ =>
    PascalParity.choose_add_two_pow_mod_two h k k Nat.lt_two_pow_self⟩

/-- **The Pascal sign character is 2-automatic**: for the weights
`a_h = C(h, k)`, the `2`-kernel of the sign character `ε` is finite.  With
Lean's index `k = r - 1` this is the volume's `ε_r`; the Thue–Morse sign is
`k = 0`. -/
theorem finite_twoKernel_parityCharacter_choose (k : ℕ) :
    (twoKernel (parityCharacter fun h => h.choose k)).Finite :=
  (finite_twoKernel_parityCharacter_iff _).mpr (eventuallyPeriodic_parityWord_choose k)

end Fabius
