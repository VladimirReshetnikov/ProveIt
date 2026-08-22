import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# Binary-to-ternary radix shadows

This module formalizes the finite digit core of the radix-shadow construction. Re-evaluating
the canonical binary digits of a natural number at base three preserves the index of the first
differing digit. Equivalently, congruence modulo `2 ^ r` is transported exactly to congruence
modulo `3 ^ r`.

The construction is not claimed to be an isometry for the standard normalized `p`-adic
metrics: those metrics assign the unequal distances `2 ^ (-r)` and `3 ^ (-r)` to a common
valuation index `r`.
-/

namespace LeanProofs.TwoBaseIntegerExponent.RadixShadow

/-- Re-evaluate the canonical base-`source` digits of `n` at base `target`. -/
def reinterpret (source target n : ℕ) : ℕ :=
  Nat.ofDigits target (Nat.digits source n)

/-- The binary-to-ternary radix shadow. -/
def phi (n : ℕ) : ℕ := reinterpret 2 3 n

private theorem ofDigits_eq_of_ofDigits_eq
    {source target : ℕ} (hsource : 1 < source) {L K : List ℕ}
    (hL : ∀ x ∈ L, x < source) (hK : ∀ x ∈ K, x < source)
    (h : Nat.ofDigits source L = Nat.ofDigits source K) :
    Nat.ofDigits target L = Nat.ofDigits target K := by
  let l := max L.length K.length
  let L' := L ++ List.replicate (l - L.length) 0
  let K' := K ++ List.replicate (l - K.length) 0
  have hLlen : L'.length = l := by
    simp only [L', List.length_append, List.length_replicate]
    omega
  have hKlen : K'.length = l := by
    simp only [K', List.length_append, List.length_replicate]
    omega
  have hLdigits : ∀ x ∈ L', x < source := by
    intro x hx
    simp only [L', List.mem_append, List.mem_replicate] at hx
    rcases hx with hx | ⟨_, rfl⟩
    · exact hL x hx
    · omega
  have hKdigits : ∀ x ∈ K', x < source := by
    intro x hx
    simp only [K', List.mem_append, List.mem_replicate] at hx
    rcases hx with hx | ⟨_, rfl⟩
    · exact hK x hx
    · omega
  have hpadded : Nat.ofDigits source L' = Nat.ofDigits source K' := by
    simpa only [L', K', Nat.ofDigits_append_replicate_zero] using h
  have hlists : L' = K' :=
    Nat.injOn_ofDigits hsource l ⟨hLlen, hLdigits⟩ ⟨hKlen, hKdigits⟩ hpadded
  have htarget := congrArg (Nat.ofDigits target) hlists
  simpa only [L', K', Nat.ofDigits_append_replicate_zero] using htarget

private theorem binaryPrefix_eval_two_eq_iff_three (m n r : ℕ) :
    Nat.ofDigits 2 ((Nat.digits 2 m).take r) =
        Nat.ofDigits 2 ((Nat.digits 2 n).take r) ↔
      Nat.ofDigits 3 ((Nat.digits 2 m).take r) =
        Nat.ofDigits 3 ((Nat.digits 2 n).take r) := by
  have hm2 : ∀ x ∈ (Nat.digits 2 m).take r, x < 2 := by
    intro x hx
    exact Nat.digits_lt_base (by norm_num) (List.mem_of_mem_take hx)
  have hn2 : ∀ x ∈ (Nat.digits 2 n).take r, x < 2 := by
    intro x hx
    exact Nat.digits_lt_base (by norm_num) (List.mem_of_mem_take hx)
  constructor
  · exact ofDigits_eq_of_ofDigits_eq (by norm_num) hm2 hn2
  · apply ofDigits_eq_of_ofDigits_eq (source := 3) (target := 2) (by norm_num)
    · intro x hx
      exact lt_trans (hm2 x hx) (by norm_num)
    · intro x hx
      exact lt_trans (hn2 x hx) (by norm_num)

/-- The binary-to-ternary radix shadow is injective. -/
theorem phi_injective : Function.Injective phi := by
  intro m n h
  have hm3 : ∀ x ∈ Nat.digits 2 m, x < 3 := by
    intro x hx
    exact lt_trans (Nat.digits_lt_base (by norm_num) hx) (by norm_num)
  have hn3 : ∀ x ∈ Nat.digits 2 n, x < 3 := by
    intro x hx
    exact lt_trans (Nat.digits_lt_base (by norm_num) hx) (by norm_num)
  have hthree : Nat.ofDigits 3 (Nat.digits 2 m) = Nat.ofDigits 3 (Nat.digits 2 n) := by
    simpa only [phi, reinterpret] using h
  have htwo := ofDigits_eq_of_ofDigits_eq (source := 3) (target := 2)
    (by norm_num) hm3 hn3 hthree
  simpa only [Nat.ofDigits_digits] using htwo

/-- Two naturals have the same low `r` binary digits exactly when their radix shadows have
the same low `r` ternary digits. -/
theorem phi_modEq_pow_iff (m n r : ℕ) :
    m ≡ n [MOD 2 ^ r] ↔ phi m ≡ phi n [MOD 3 ^ r] := by
  change m % 2 ^ r = n % 2 ^ r ↔ phi m % 3 ^ r = phi n % 3 ^ r
  rw [Nat.self_mod_pow_eq_ofDigits_take r m (by norm_num),
    Nat.self_mod_pow_eq_ofDigits_take r n (by norm_num)]
  change Nat.ofDigits 2 ((Nat.digits 2 m).take r) =
      Nat.ofDigits 2 ((Nat.digits 2 n).take r) ↔
    Nat.ofDigits 3 (Nat.digits 2 m) % 3 ^ r =
      Nat.ofDigits 3 (Nat.digits 2 n) % 3 ^ r
  rw [Nat.ofDigits_mod_pow_eq_ofDigits_take r (by norm_num) (Nat.digits 2 m),
    Nat.ofDigits_mod_pow_eq_ofDigits_take r (by norm_num) (Nat.digits 2 n)]
  · exact binaryPrefix_eval_two_eq_iff_three m n r
  · intro x hx
    exact lt_trans (Nat.digits_lt_base (by norm_num) hx) (by norm_num)
  · intro x hx
    exact lt_trans (Nat.digits_lt_base (by norm_num) hx) (by norm_num)

/-- Divisibility-index form of `phi_modEq_pow_iff`, with subtraction performed in `ℤ`. -/
theorem three_pow_dvd_phi_sub_iff_two_pow_dvd_sub (m n r : ℕ) :
    ((3 ^ r : ℕ) : ℤ) ∣ (phi m : ℤ) - phi n ↔
      ((2 ^ r : ℕ) : ℤ) ∣ (m : ℤ) - n := by
  simpa only [Nat.modEq_iff_dvd] using (phi_modEq_pow_iff n m r).symm

/-- Exact equality of the first-differing-digit index, stated with integer `p`-adic
valuations. -/
theorem padicValInt_phi_sub_eq {m n : ℕ} (h : m ≠ n) :
    padicValInt 3 ((phi m : ℤ) - phi n) = padicValInt 2 ((m : ℤ) - n) := by
  have hinput : (m : ℤ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
  have hshadow : (phi m : ℤ) - phi n ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast (phi_injective.ne h)
  apply le_antisymm
  · let v := padicValInt 3 ((phi m : ℤ) - phi n)
    have hthree : ((3 ^ v : ℕ) : ℤ) ∣ (phi m : ℤ) - phi n := by
      simpa using (padicValInt_dvd ((phi m : ℤ) - phi n) :
        (3 : ℤ) ^ v ∣ (phi m : ℤ) - phi n)
    have htwo : ((2 ^ v : ℕ) : ℤ) ∣ (m : ℤ) - n :=
      (three_pow_dvd_phi_sub_iff_two_pow_dvd_sub m n v).mp hthree
    exact ((padicValInt_dvd_iff_of_ne_one (p := 2) (by norm_num) v
      ((m : ℤ) - n)).mp (by simpa using htwo)).resolve_left hinput
  · let v := padicValInt 2 ((m : ℤ) - n)
    have htwo : ((2 ^ v : ℕ) : ℤ) ∣ (m : ℤ) - n := by
      simpa using (padicValInt_dvd ((m : ℤ) - n) :
        (2 : ℤ) ^ v ∣ (m : ℤ) - n)
    have hthree : ((3 ^ v : ℕ) : ℤ) ∣ (phi m : ℤ) - phi n :=
      (three_pow_dvd_phi_sub_iff_two_pow_dvd_sub m n v).mpr htwo
    exact ((padicValInt_dvd_iff_of_ne_one (p := 3) (by norm_num) v
      ((phi m : ℤ) - phi n)).mp (by simpa using hthree)).resolve_left hshadow

end LeanProofs.TwoBaseIntegerExponent.RadixShadow
