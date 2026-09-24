import Diophantine.Paper1980.System100
import Diophantine.Paper1980.TernaryMask

/-!
# Bootstrap bounds of the 100-operation system and the kernel conclusions

`EXPLORATION_STATE_TOP_DOUBLED_GRID.md`, §2.  From positivity and the outer
equations alone: `R ≥ 8·Zon + 9` (the paid grid width), `q ≥ W = R³`, the packed
register is positive so `q¹² ≤ 2r`, and `r < q¹²`.  These are the hypotheses of the
base-three kernel (`kernel3_sound`) at the scale `D₀ = q¹²`, which yields `U = 3^J`,
`q` a power of three and `q¹² ∣ C(2r, r)`; the unit-two mask then gives the ternary
digits of `r` (unit `2`, others nonzero), and subtracting the repunit shows that the
packed word `P = 2r + 1 − q¹²` is twice a Boolean ternary word with unit digit `1`.
-/

namespace Jones1980

open Ternary

section Bounds

variable {C : ROM100}
  {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
  (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hS : Sys100 C x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)

include hP hS

/-- The grid width: `R ≥ 8·Zon + 9`. -/
theorem R_ge100 (hB : 9 ≤ C.B0) : 8 * C.Zon + 9 ≤ R := by
  have h4 := hS.E4
  have hz := hP.z
  have h1 : 8 * (C.Zon + z) ≤ (C.B0 - 1) * (C.Zon + z) := Nat.mul_le_mul_right _ (by omega)
  omega

theorem W_le_q100 : W ≤ q := by rw [hS.E1]; exact Nat.le_mul_of_pos_right _ hP.v

theorem R_cube_le_q100 : R ^ 3 ≤ q := by rw [← hS.E19]; exact W_le_q100 hP hS

theorem R_le_q100 : R ≤ q := le_trans (Nat.le_self_pow (by norm_num) R) (R_cube_le_q100 hP hS)

theorem q_ge100 (hZ : 81 ≤ C.Zon) (hB : 9 ≤ C.B0) : 657 ≤ q := by
  have := R_ge100 hP hS hB
  have := R_le_q100 hP hS
  omega

/-- The packed register is positive, so `q¹² ≤ 2r`. -/
theorem r_lower100 : q ^ 12 ≤ 2 * r := by
  have h8 := hS.E8
  have hJ := hP.J
  have hKm := hP.Km
  have h1 : 1 ≤ J * (Km + q ^ 2 * (D + q ^ 2 * (A0 + q ^ 2 * (A1 + q ^ 2 * (PV + q ^ 2 * PC))))) :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  omega

theorem r_lt100 : r < q ^ 12 := by have := hS.E20; have := hP.β; omega

/-- The kernel conclusions: `q` is a power of three, `q¹² ∣ C(2r, r)`, `U = 3^(2r+1)`. -/
theorem kernel_out100 (hZ : 81 ≤ C.Zon) (hB : 9 ≤ C.B0) :
    (∃ e, 1 ≤ e ∧ q = 3 ^ e) ∧ q ^ 12 ∣ (2 * r).choose r ∧ w * q ^ 12 = 3 ^ (2 * r + 1) := by
  have hA : 1 < a + 3 := by omega
  have hPp : 1 < 2 * (w * q ^ 12 * (s * q ^ 12) ^ 2) + 1 := by
    have : 0 < w * q ^ 12 * (s * q ^ 12) ^ 2 := by
      have := hP.kernel.w; have := hP.kernel.s; have := hP.q; positivity
    omega
  have hq := q_ge100 hP hS hZ hB
  have hD0 : 81 ≤ q ^ 12 := le_trans (by omega) (Nat.le_self_pow (by norm_num) q)
  have hr27 : 27 ≤ r := by have := r_lower100 hP hS; omega
  have hr2 : r < 2 * q ^ 12 := by have := r_lt100 hP hS; omega
  have out := kernel3_sound hP.kernel hS.kernel hD0 hr27 hr2 hA hPp
  refine ⟨?_, out.central, out.U_eq⟩
  have h1 : q ∣ 3 ^ (2 * r + 1) := by
    rw [← out.U_eq]; exact Dvd.intro_left (w * q ^ 11) (by ring)
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
  refine ⟨e, ?_, he⟩
  rcases Nat.eq_zero_or_pos e with h0 | h0
  · rw [h0, pow_zero] at he; omega
  · exact h0

/-- The masks: with `q = 3^e`, the ternary digits of `r` below `12e` are nonzero with unit
digit `2`, and the packed word is `2(r − rep(12e))` with `r − rep(12e)` Boolean of unit `1`. -/
theorem mask100 (hZ : 81 ≤ C.Zon) (hB : 9 ≤ C.B0) :
    ∃ e, 1 ≤ e ∧ q = 3 ^ e ∧ q ^ 12 = 3 ^ (12 * e) ∧
      r % 3 = 2 ∧ (∀ i, 1 ≤ i → i < 12 * e → r / 3 ^ i % 3 ≠ 0) ∧
      rep (12 * e) ≤ r ∧ 2 * (r - rep (12 * e)) + q ^ 12 = 2 * r + 1 ∧
      (r - rep (12 * e)) % 3 = 1 ∧ ∀ i, (r - rep (12 * e)) / 3 ^ i % 3 ≤ 1 := by
  obtain ⟨⟨e, he1, he⟩, hcentral, -⟩ := kernel_out100 hP hS hZ hB
  have hq12 : q ^ 12 = 3 ^ (12 * e) := by rw [he, ← pow_mul, mul_comm]
  have hr := r_lt100 hP hS
  rw [hq12] at hcentral hr
  have hN : 1 ≤ 12 * e := by omega
  obtain ⟨h0, hd⟩ := (ternary_mask hN hr).1 hcentral
  obtain ⟨hle, h1, hb⟩ := sub_rep hN hr h0 hd
  refine ⟨e, he1, he, hq12, h0, hd, hle, ?_, h1, hb⟩
  have := two_mul_rep_add_one (12 * e)
  rw [hq12]; omega

end Bounds

end Jones1980
