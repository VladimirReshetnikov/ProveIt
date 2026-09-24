import Diophantine.Paper1980.Bounds100
import Diophantine.Paper1980.RowSum

/-!
# The twelve doubled fields of the 100-operation counter system

`EXPLORATION_STATE_TOP_DOUBLED_GRID.md`, §§3–5.  The packed word expands in base `q` as
the twelve conceptual fields

    K⁺, K⁻, H − D, D, t − A₀, A₀, t − A₁, A₁, zH − V, V, SH − C, C,

(the first one because `K⁺ + K⁻ = H`).  Once the six complements are nonnegative — the
content of §§3–4, which rests on the compiled ROM's trit structure — every field is below
`q`, so the expansion *is* the base-`q` chunk decomposition, with no carry anywhere.  The
packed word is twice the Boolean word `r − rep(12e)`, so each field is twice a Boolean
ternary word below `rep e`: exactly the doubled coordinates of the note's §5.

`Nonneg100` collects the six nonnegativity statements; `fields100` is the decoding.
-/

namespace Jones1980

open Ternary

/-! ### Chunks of a doubled Boolean word -/

namespace Ternary

/-- Doubling a Boolean word doubles every base-`3^n` remainder and quotient. -/
theorem two_mul_div {B n : ℕ} (hB : Bool3 B) : 2 * B / 3 ^ n = 2 * (B / 3 ^ n) := by
  have hlt : 2 * (B % 3 ^ n) < 3 ^ n := by
    have h1 := hB.mod_le_rep n
    have h2 := two_mul_rep_add_one n
    omega
  conv_lhs => rw [← Nat.div_add_mod B (3 ^ n)]
  rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hlt,
    add_zero]

/-- Doubling a Boolean word doubles every base-`3^e` chunk. -/
theorem two_mul_chunk {B e k : ℕ} (hB : Bool3 B) :
    2 * B / 3 ^ (e * k) % 3 ^ e = 2 * (B / 3 ^ (e * k) % 3 ^ e) := by
  rw [two_mul_div hB]
  have hY : Bool3 (B / 3 ^ (e * k)) := hB.div_pow _
  have hlt : 2 * (B / 3 ^ (e * k) % 3 ^ e) < 3 ^ e := by
    have h1 := hY.mod_le_rep e
    have h2 := two_mul_rep_add_one e
    omega
  conv_lhs => rw [← Nat.div_add_mod (B / 3 ^ (e * k)) (3 ^ e)]
  rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

end Ternary

/-- The Horner expansion of the packed word into the twelve conceptual fields. -/
theorem horner_identity (q J Kp Km H D t A0 A1 PV PC z S : ℤ)
    (hq : q = J + 1) (hKp : Kp = H - Km) :
    Kp + q * (Km + q * ((H - D) + q * (D + q * ((t - A0) + q * (A0 + q * ((t - A1) +
        q * (A1 + q * ((z * H - PV) + q * (PV + q * ((S * H - PC) + q * PC))))))))))
      = J * (Km + q ^ 2 * (D + q ^ 2 * (A0 + q ^ 2 * (A1 + q ^ 2 * (PV + q ^ 2 * PC)))))
        + (q ^ 2 + 1) * (H + q ^ 4 * t) + q ^ 8 * (H * (z + q ^ 2 * S)) := by
  subst hq; subst hKp; ring

/-- The nonnegativity of the six complements: the conclusion of §§3–4. -/
structure Nonneg100 (C : ROM100) (H D t A0 A1 PV PC z : ℕ) : Prop where
  D_le : D ≤ H
  A0_le : A0 ≤ t
  A1_le : A1 ≤ t
  PV_le : PV ≤ z * H
  PC_le : PC ≤ C.S * H

section Fields

variable {C : ROM100}
  {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
  {e m u : ℕ}
  (hOk : C.Ok)
  (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hS : Sys100 C x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hG : Geometry100 H R q e m u)
  (hN : Nonneg100 C H D t A0 A1 PV PC z)

include hOk hP hS

/-- `H < q`. -/
theorem H_lt_q : H < q := by
  have hhd := head_eq100 hOk hP hS
  have hR := R_big hOk hP hS
  have hZ := hOk.Zon_ge
  have hq := hP.q
  have h1 : H * 656 ≤ H * (R - 1) := Nat.mul_le_mul_left _ (by omega)
  omega

include hN

/-- `3 t < q`, once the zero complement is nonnegative. -/
theorem t_small : 3 * t < q := by
  have h5 := hS.E5
  have hhd := head_eq100 hOk hP hS
  have hq := hP.q
  have hR := R_big hOk hP hS
  have hZ := hOk.Zon_ge
  have hDH := hN.D_le
  -- `6 t = D (R − 3) ≤ H (R − 3) < H (R − 1) = 2(q − 1)`
  have e1 : D * (R - 3) = D * R - D * 3 := by rw [Nat.mul_sub]
  have e2 : D * 3 = 3 * D := by ring
  have e3 : D * 3 ≤ D * R := Nat.mul_le_mul_left _ (by omega)
  have h1 : 6 * t = D * (R - 3) := by omega
  have h2 : D * (R - 3) ≤ H * (R - 3) := Nat.mul_le_mul_right _ hDH
  have h3 : H * (R - 3) ≤ H * (R - 1) := Nat.mul_le_mul_left _ (by omega)
  omega

end Fields

/-! ### Doubled fields -/

/-- `X` is twice a Boolean ternary word below the repunit of `e` digits. -/
def Doubled (e X : ℕ) : Prop := ∃ b, Bool3 b ∧ b ≤ rep e ∧ X = 2 * b

theorem doubled_of_mod {e B : ℕ} (hB : Bool3 B) : Doubled e (2 * (B % 3 ^ e)) :=
  ⟨B % 3 ^ e, hB.mod_pow e, hB.mod_le_rep e, rfl⟩

/-- Peeling the lowest base-`3^e` chunk of a doubled Boolean word. -/
theorem doubled_step {e B a P' : ℕ} (hB : Bool3 B) (ha : a < 3 ^ e)
    (h : 2 * B = a + 3 ^ e * P') : a = 2 * (B % 3 ^ e) ∧ P' = 2 * (B / 3 ^ e) := by
  have hlt : 2 * (B % 3 ^ e) < 3 ^ e := by
    have h1 := hB.mod_le_rep e
    have h2 := two_mul_rep_add_one e
    omega
  have h2 : 2 * B = 2 * (B % 3 ^ e) + 3 ^ e * (2 * (B / 3 ^ e)) := by
    conv_lhs => rw [← Nat.div_add_mod B (3 ^ e)]
    ring
  have heq : a + 3 ^ e * P' = 2 * (B % 3 ^ e) + 3 ^ e * (2 * (B / 3 ^ e)) := by rw [← h, h2]
  have ha' : a = 2 * (B % 3 ^ e) := by
    have e1 : (a + 3 ^ e * P') % 3 ^ e = a := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
    have e2 : (2 * (B % 3 ^ e) + 3 ^ e * (2 * (B / 3 ^ e))) % 3 ^ e = 2 * (B % 3 ^ e) := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    rw [heq] at e1
    omega
  refine ⟨ha', ?_⟩
  have hmul : 3 ^ e * P' = 3 ^ e * (2 * (B / 3 ^ e)) := by omega
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hmul

/-- The top chunk of a doubled Boolean word. -/
theorem doubled_last {e B a : ℕ} (hB : Bool3 B) (ha : a < 3 ^ e) (h : 2 * B = a) :
    Doubled e a := by
  have hlt : B < 3 ^ e := by omega
  refine ⟨B, hB, ?_, by omega⟩
  have hm := hB.mod_le_rep e
  rwa [Nat.mod_eq_of_lt hlt] at hm

section Decode

variable {C : ROM100}
  {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
  {e m u : ℕ}
  (hOk : C.Ok)
  (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hS : Sys100 C x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hG : Geometry100 H R q e m u)
  (hN : Nonneg100 C H D t A0 A1 PV PC z)

include hOk hP hS hG hN

set_option maxHeartbeats 1000000 in
/-- **The twelve fields.**  Each conceptual field is twice a Boolean ternary word below
`rep e`, so every supplied coordinate of the counter block is even and the halved words are
the raw coordinates of the note's §5. -/
theorem fields100 :
    Doubled e Kp ∧ Doubled e Km ∧ Doubled e (H - D) ∧ Doubled e D ∧
    Doubled e (t - A0) ∧ Doubled e A0 ∧ Doubled e (t - A1) ∧ Doubled e A1 ∧
    Doubled e (z * H - PV) ∧ Doubled e PV ∧ Doubled e (C.S * H - PC) ∧ Doubled e PC := by
  -- the Boolean packed word
  obtain ⟨e', -, hqe', -, -, -, hrep, hP2, -, hBb⟩ := mask100 hP hS hOk.Zon_ge hOk.B0_ge
  have hee : e' = e := by
    apply Nat.pow_right_injective (by norm_num : 2 ≤ 3)
    show (3 : ℕ) ^ e' = 3 ^ e
    rw [← hqe', ← hG.hq]
  subst hee
  have hq3 : q = 3 ^ e' := hqe'
  have hBw : Bool3 (r - rep (12 * e')) := hBb
  -- `P = 2 B`
  have h8 := hS.E8
  have hPw : 2 * (r - rep (12 * e'))
      = J * (Km + q ^ 2 * (D + q ^ 2 * (A0 + q ^ 2 * (A1 + q ^ 2 * (PV + q ^ 2 * PC)))))
        + (q ^ 2 + 1) * (H + q ^ 4 * t) + q ^ 8 * (H * (z + q ^ 2 * C.S)) := by omega
  -- the field bounds
  have hKmH : Km ≤ H := by have := hS.E3; omega
  have hKpH : Kp ≤ H := by have := hS.E3; omega
  have hHq := H_lt_q hOk hP hS
  have htq := t_small hOk hP hS hN
  have hAq := track_small hOk hP hS
  have hzq := zH_small hOk hP hS
  have hSq := SH_small hOk hP hS
  have hDle := hN.D_le
  have hA0le := hN.A0_le
  have hA1le := hN.A1_le
  have hPVle := hN.PV_le
  have hPCle := hN.PC_le
  -- the Horner expansion
  have hqZ : (q : ℤ) = (J : ℤ) + 1 := by exact_mod_cast hS.E0
  have hKpZ : (Kp : ℤ) = (H : ℤ) - (Km : ℤ) := by
    have h3 : ((Kp + Km : ℕ) : ℤ) = (H : ℤ) := by exact_mod_cast hS.E3
    push_cast at h3
    linarith
  have hid := horner_identity (q : ℤ) (J : ℤ) (Kp : ℤ) (Km : ℤ) (H : ℤ) (D : ℤ) (t : ℤ)
    (A0 : ℤ) (A1 : ℤ) (PV : ℤ) (PC : ℤ) (z : ℤ) (C.S : ℤ) hqZ hKpZ
  have hHorner : 2 * (r - rep (12 * e'))
      = Kp + q * (Km + q * ((H - D) + q * (D + q * ((t - A0) + q * (A0 + q * ((t - A1)
        + q * (A1 + q * ((z * H - PV) + q * (PV + q * ((C.S * H - PC) + q * PC)))))))))) := by
    rw [hPw]
    zify [hN.D_le, hN.A0_le, hN.A1_le, hN.PV_le, hN.PC_le]
    push_cast
    linarith [hid]
  -- peel the twelve chunks
  rw [hq3] at hHorner
  obtain ⟨f0, r0⟩ := doubled_step hBw (by rw [← hq3]; omega) hHorner
  obtain ⟨f1, r1⟩ := doubled_step (hBw.div_pow e') (by rw [← hq3]; omega) r0.symm
  obtain ⟨f2, r2⟩ := doubled_step ((hBw.div_pow e').div_pow e') (by rw [← hq3]; omega) r1.symm
  obtain ⟨f3, r3⟩ := doubled_step (((hBw.div_pow e').div_pow e').div_pow e')
    (by rw [← hq3]; omega) r2.symm
  obtain ⟨f4, r4⟩ := doubled_step ((((hBw.div_pow e').div_pow e').div_pow e').div_pow e')
    (by rw [← hq3]; omega) r3.symm
  obtain ⟨f5, r5⟩ := doubled_step (((((hBw.div_pow e').div_pow e').div_pow e').div_pow e').div_pow e')
    (by rw [← hq3]; omega) r4.symm
  obtain ⟨f6, r6⟩ := doubled_step
    ((((((hBw.div_pow e').div_pow e').div_pow e').div_pow e').div_pow e').div_pow e')
    (by rw [← hq3]; omega) r5.symm
  obtain ⟨f7, r7⟩ := doubled_step
    (((((((hBw.div_pow e').div_pow e').div_pow e').div_pow e').div_pow e').div_pow e').div_pow e')
    (by rw [← hq3]; omega) r6.symm
  obtain ⟨f8, r8⟩ := doubled_step
    ((((((((hBw.div_pow e').div_pow e').div_pow e').div_pow e').div_pow e').div_pow e').div_pow
      e').div_pow e') (by rw [← hq3]; omega) r7.symm
  obtain ⟨f9, r9⟩ := doubled_step
    (((((((((hBw.div_pow e').div_pow e').div_pow e').div_pow e').div_pow e').div_pow e').div_pow
      e').div_pow e').div_pow e') (by rw [← hq3]; omega) r8.symm
  obtain ⟨f10, r10⟩ := doubled_step
    ((((((((((hBw.div_pow e').div_pow e').div_pow e').div_pow e').div_pow e').div_pow
      e').div_pow e').div_pow e').div_pow e').div_pow e') (by rw [← hq3]; omega) r9.symm
  have f11 := doubled_last (e := e') (a := PC)
    (((((((((((hBw.div_pow e').div_pow e').div_pow e').div_pow e').div_pow e').div_pow
      e').div_pow e').div_pow e').div_pow e').div_pow e').div_pow e')
    (by rw [← hq3]; omega) r10.symm
  exact ⟨f0 ▸ doubled_of_mod hBw, f1 ▸ doubled_of_mod (hBw.div_pow e'),
    f2 ▸ doubled_of_mod ((hBw.div_pow e').div_pow e'),
    f3 ▸ doubled_of_mod (((hBw.div_pow e').div_pow e').div_pow e'),
    f4 ▸ doubled_of_mod ((((hBw.div_pow e').div_pow e').div_pow e').div_pow e'),
    f5 ▸ doubled_of_mod (((((hBw.div_pow e').div_pow e').div_pow e').div_pow e').div_pow e'),
    f6 ▸ doubled_of_mod
      ((((((hBw.div_pow e').div_pow e').div_pow e').div_pow e').div_pow e').div_pow e'),
    f7 ▸ doubled_of_mod
      (((((((hBw.div_pow e').div_pow e').div_pow e').div_pow e').div_pow e').div_pow e').div_pow e'),
    f8 ▸ doubled_of_mod
      ((((((((hBw.div_pow e').div_pow e').div_pow e').div_pow e').div_pow e').div_pow
        e').div_pow e').div_pow e'),
    f9 ▸ doubled_of_mod
      (((((((((hBw.div_pow e').div_pow e').div_pow e').div_pow e').div_pow e').div_pow
        e').div_pow e').div_pow e').div_pow e'),
    f10 ▸ doubled_of_mod
      ((((((((((hBw.div_pow e').div_pow e').div_pow e').div_pow e').div_pow e').div_pow
        e').div_pow e').div_pow e').div_pow e').div_pow e'),
    f11⟩

end Decode

end Jones1980
