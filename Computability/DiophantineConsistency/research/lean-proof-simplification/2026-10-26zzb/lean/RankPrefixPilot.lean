import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.NormNum

/-! A direct signed-rank projection. The bitwise implication is old machinery;
this theorem removes the natural packing-range and beta/repunit hypotheses
from the rank-residue conclusion. -/
namespace RankPrefixPilot

set_option Elab.async false
set_option maxRecDepth 10000

/-- Exact copied definition of NativeRankVariation.windowRank over integers. -/
def windowRank (q C F MC MF J : ℤ) : ℤ :=
  (q * (q - F) - C) * (q ^ 2 - 1) + (MC + q * MF) * J

/-- Existing low-mask arithmetic, isolated here to make the pilot standalone. -/
lemma low_prefix_zero {A M k : ℕ}
    (hmask : A &&& M = 0) (hprefix : M % 2^k = 2^k - 1) :
    A % 2^k = 0 := by
  have h := congrArg (fun z : ℕ => z % 2^k) hmask
  rw [Nat.and_mod_two_pow, hprefix] at h
  simpa only [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod, Nat.zero_mod] using h

/-- The signed rank is fixed modulo a saturated low-mask prefix, even when
F and MF are arbitrary signed integers and no packing-range bound is known. -/
theorem rank_prefix {q C MC J k : ℕ} (F MF : ℤ)
    (hC : 0 < C) (hq : 2^k ∣ q)
    (hmask : (C-1) &&& (MC*J+1) = 0)
    (hprefix : (MC*J+1) % 2^k = 2^k - 1) :
    (windowRank q C F MC MF J : ZMod (2^k)) = -1 := by
  have hp : 1 ≤ 2^k := Nat.one_le_two_pow
  have hqz : (q : ZMod (2^k)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hq
  have hcmod := low_prefix_zero hmask hprefix
  have hcz : ((C-1 : ℕ) : ZMod (2^k)) = 0 := by
    rw [← ZMod.natCast_mod (C-1) (2^k), hcmod, Nat.cast_zero]
  have hc1 : (C : ZMod (2^k)) = 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ C), Nat.cast_one] at hcz
    exact sub_eq_zero.mp hcz
  have hmz : ((MC*J+1 : ℕ) : ZMod (2^k)) = -1 := by
    rw [← ZMod.natCast_mod (MC*J+1) (2^k), hprefix,
      Nat.cast_sub hp, Nat.cast_one, ZMod.natCast_self, zero_sub]
  have hsum : 1 + (MC : ZMod (2^k)) * J = -1 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, add_comm] using hmz
  simp only [windowRank, Int.cast_add, Int.cast_mul, Int.cast_sub,
    Int.cast_pow, Int.cast_one, Int.cast_natCast]
  simpa [hqz, hc1] using hsum

/-- The ordinary residue statement for any natural number identified with
that integer rank; no positivity proof for the polynomial is required here. -/
theorem rank_prefix_nat {q C MC J k R : ℕ} (F MF : ℤ)
    (hC : 0 < C) (hq : 2^k ∣ q)
    (hmask : (C-1) &&& (MC*J+1) = 0)
    (hprefix : (MC*J+1) % 2^k = 2^k - 1)
    (hR : (R : ℤ) = windowRank q C F MC MF J) :
    R % 2^k = 2^k - 1 := by
  have h := rank_prefix F MF hC hq hmask hprefix
  rw [← hR, Int.cast_natCast] at h
  have hp : 1 ≤ 2^k := Nat.one_le_two_pow
  have hm : ((2^k - 1 : ℕ) : ZMod (2^k)) = -1 := by
    rw [Nat.cast_sub hp, Nat.cast_one, ZMod.natCast_self, zero_sub]
  have he := (ZMod.natCast_eq_natCast_iff' R (2^k-1) (2^k)).mp (h.trans hm.symm)
  rwa [Nat.mod_eq_of_lt (by omega : 2^k-1 < 2^k)] at he

-- Explicit stress point outside the old C+F<q domain.
example : windowRank 4 1 100 2 (-7) 1 = -5801 := by norm_num [windowRank]
example : (windowRank 4 1 100 2 (-7) 1 : ZMod 4) = -1 := by
  exact rank_prefix 100 (-7) (k:=2) (by decide) (by decide) (by decide) (by decide)

#print axioms low_prefix_zero
#print axioms rank_prefix
#print axioms rank_prefix_nat
end RankPrefixPilot
