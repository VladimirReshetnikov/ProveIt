import Diophantine.Paper1980.CounterComplete100
import Diophantine.Paper1980.TagWitness

/-!
# Assembling a solution of the 100-operation counter certificate

`EXPLORATION_STATE_TOP_DOUBLED_GRID.md`, §6: *"All twelve resulting fields remain 0/2 words
below q, and the first field has unit trit 2.  Their concatenation is positive and below
L=q^12.  Define freshly r=(L+P-1)/2, beta=L-r>0. ...  Since q is odd, the undoubled packed word
is even ...  Also (q^12-1)/2 is even.  Therefore r is even.  The same unit-two ternary mask
theorem supplies central divisibility, and the general 43-operation positive Pell converse
supplies all its positive witnesses at this new r."*

`assemble100` is that paragraph.  It takes the halves of the twelve fields,

    k⁺, k⁻, h − d, d, t/2 − a₀, a₀, t/2 − a₁, a₁, z h − v, v, S h − c, c,

Boolean and below `q = 3^e`, the first with unit digit `1`, `h` even, and the outer equations
in halved form, and produces a positive solution of `Sys100`.  The packed index is
`r = P/2 + rep(12e)`, where `P/2` is the concatenation of the halves.
-/

namespace Jones1980

open Ternary

set_option maxHeartbeats 4000000 in
/-- **The positive converse assembly** of the 100-operation system. -/
theorem assemble100 {C : ROM100} {x q e W v R h tt kp km dd ddb a0 b0 a1 b1 pv pvb pc pcb z α : ℕ}
    (hq : q = 3 ^ e) (he : 1 ≤ e)
    (hx : 0 < x) (hW : 0 < W) (hv : 0 < v) (hR : 0 < R) (hh : 0 < h) (htt : 0 < tt)
    (hkp : 0 < kp) (hkm : 0 < km) (hdd : 0 < dd) (ha0 : 0 < a0) (ha1 : 0 < a1) (hpv : 0 < pv)
    (hpc : 0 < pc) (hz : 0 < z) (hα : 0 < α)
    (E1 : q = W * v) (E2 : h * R = h + (q - 1)) (E4 : (C.B0 - 1) * (C.Zon + z) + 1 = R)
    (E5 : 6 * tt + 3 * dd = dd * R) (E6 : W * (a0 + a1 + kp) + 2 * x = a0 + a1 + W * km)
    (E7 : 4 * x + α = R) (E19 : W = R ^ 3)
    (E21 : R * C.K * pc = C.g * pc + C.g * C.I * (q - 1) + R * (pv + C.hs * kp + C.hz * dd))
    (sK : kp + km = h) (sD : ddb + dd = h) (sA0 : b0 + a0 = tt) (sA1 : b1 + a1 = tt)
    (sV : pvb + pv = z * h) (sC : pcb + pc = C.S * h)
    (b1' : Bool3 kp) (b2 : Bool3 km) (b3 : Bool3 ddb) (b4 : Bool3 dd) (b5 : Bool3 b0)
    (b6 : Bool3 a0) (b7 : Bool3 b1) (b8 : Bool3 a1) (b9 : Bool3 pvb) (b10 : Bool3 pv)
    (b11 : Bool3 pcb) (b12 : Bool3 pc)
    (l1 : kp < q) (l2 : km < q) (l3 : ddb < q) (l4 : dd < q) (l5 : b0 < q) (l6 : a0 < q)
    (l7 : b1 < q) (l8 : a1 < q) (l9 : pvb < q) (l10 : pv < q) (l11 : pcb < q) (l12 : pc < q)
    (hunit : kp % 3 = 1) (hpar : 2 ∣ h) :
    Solvable100 C x := by
  have hq0 : 0 < q := by rw [hq]; positivity
  have hq3 : 3 ≤ q := by
    rw [hq]
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he
  -- the halved packed word
  obtain ⟨Ph, hPh⟩ : ∃ P, P = kp + q * (km + q * (ddb + q * (dd + q * (b0 + q * (a0 + q * (b1 +
      q * (a1 + q * (pvb + q * (pv + q * (pcb + q * pc)))))))))) := ⟨_, rfl⟩
  have hPb : Bool3 Ph := by
    rw [hPh, hq]
    refine bool3_chunk_cons b1' (hq ▸ l1) ?_
    refine bool3_chunk_cons b2 (hq ▸ l2) ?_
    refine bool3_chunk_cons b3 (hq ▸ l3) ?_
    refine bool3_chunk_cons b4 (hq ▸ l4) ?_
    refine bool3_chunk_cons b5 (hq ▸ l5) ?_
    refine bool3_chunk_cons b6 (hq ▸ l6) ?_
    refine bool3_chunk_cons b7 (hq ▸ l7) ?_
    refine bool3_chunk_cons b8 (hq ▸ l8) ?_
    refine bool3_chunk_cons b9 (hq ▸ l9) ?_
    refine bool3_chunk_cons b10 (hq ▸ l10) ?_
    exact bool3_chunk_cons b11 (hq ▸ l11) b12
  have hPlt : Ph < 3 ^ (12 * e) := by
    rw [hPh, hq]
    have h12 : pc < 3 ^ (1 * e) := by rw [one_mul, ← hq]; exact l12
    have h11 := chunk_cons_lt (hq ▸ l11) h12
    have h10 := chunk_cons_lt (hq ▸ l10) h11
    have h9 := chunk_cons_lt (hq ▸ l9) h10
    have h8 := chunk_cons_lt (hq ▸ l8) h9
    have h7 := chunk_cons_lt (hq ▸ l7) h8
    have h6 := chunk_cons_lt (hq ▸ l6) h7
    have h5 := chunk_cons_lt (hq ▸ l5) h6
    have h4 := chunk_cons_lt (hq ▸ l4) h5
    have h3 := chunk_cons_lt (hq ▸ l3) h4
    have h2 := chunk_cons_lt (hq ▸ l2) h3
    have h1 := chunk_cons_lt (hq ▸ l1) h2
    simpa using h1
  have hPrep : Ph ≤ rep (12 * e) := hPb.le_rep hPlt
  -- the index
  obtain ⟨r, hrdef⟩ : ∃ r, r = Ph + rep (12 * e) := ⟨_, rfl⟩
  have hrep12 : 2 * rep (12 * e) + 1 = 3 ^ (12 * e) := two_mul_rep_add_one _
  have hq12 : q ^ 12 = 3 ^ (12 * e) := by rw [hq, ← pow_mul, mul_comm]
  have hrlt : r < 3 ^ (12 * e) := by omega
  have h312 : (531441 : ℕ) ≤ 3 ^ (12 * e) := by
    calc (531441 : ℕ) = 3 ^ 12 := by norm_num
      _ ≤ 3 ^ (12 * e) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hr2 : 2 ≤ r := by omega
  have hβ : 0 < q ^ 12 - r := by omega
  -- the mask of `r`
  obtain ⟨q', hq'⟩ : (3 : ℕ) ∣ q := by rw [hq]; exact dvd_pow_self 3 (by omega)
  have hP0 : Ph % 3 = 1 := by
    rw [hPh, hq', Nat.mul_assoc, Nat.add_mul_mod_self_left]
    exact hunit
  have hr0 : r % 3 = 2 := by
    have := dg_add_rep hPb hPlt 0 (by omega)
    rw [dg_zero_pos, dg_zero_pos] at this
    rw [hrdef]
    omega
  have hrd : ∀ i, 1 ≤ i → i < 12 * e → r / 3 ^ i % 3 ≠ 0 := by
    intro i _ hi
    have := dg_add_rep hPb hPlt i hi
    unfold dg at this
    rw [hrdef]
    omega
  have hcentral : 3 ^ (12 * e) ∣ (2 * r).choose r :=
    (ternary_mask (by omega) hrlt).2 ⟨hr0, hrd⟩
  -- the parity of `r`
  have hq2 : q % 2 = 1 := by rw [hq]; exact pow_three_mod_two e
  have hpk : ∀ a b b' : ℕ, b ≡ b' [MOD 2] → a + q * b ≡ a + b' [MOD 2] := fun a b b' hb =>
    (horner_modEq hq2 a b).trans (Nat.ModEq.add_left a hb)
  have hPmod : Ph ≡ kp + (km + (ddb + (dd + (b0 + (a0 + (b1 + (a1 + (pvb + (pv + (pcb + pc))))))))))
      [MOD 2] := by
    rw [hPh]
    exact hpk _ _ _ (hpk _ _ _ (hpk _ _ _ (hpk _ _ _ (hpk _ _ _ (hpk _ _ _ (hpk _ _ _ (hpk _ _ _
      (hpk _ _ _ (hpk _ _ _ (horner_modEq hq2 _ _))))))))))
  have hreven : 2 ∣ r := by
    have hrep : rep (12 * e) % 2 = 0 := by rw [rep_parity]; omega
    obtain ⟨h', hh'⟩ := hpar
    unfold Nat.ModEq at hPmod
    have hS : (C.S * h) % 2 = 0 := by rw [hh', Nat.mul_left_comm, Nat.mul_mod_right]
    have hZ : (z * h) % 2 = 0 := by rw [hh', Nat.mul_left_comm, Nat.mul_mod_right]
    omega
  have hD₀r : 3 ^ (12 * e) < r ^ 2 := by
    have h1 : 3 ^ (12 * e) ≤ 3 * r := by omega
    have h2 : 4 * r ≤ r * r := Nat.mul_le_mul (show 4 ≤ r by omega) (le_refl r)
    have h3 : r * r = r ^ 2 := (sq r).symm
    omega
  obtain ⟨a, c, d, f, hh2, i, j, k, o, s, w, τ, η, ζ, γ, y, hKP, hK⟩ :=
    kernel3_witnesses (D₀ := 3 ^ (12 * e)) rfl hr2 hreven hD₀r hcentral
  rw [← hq12] at hK
  -- the packed index equation
  have E8 : 2 * r + 1 = q ^ 12 + ((q - 1) * (2 * km + q ^ 2 * (2 * dd + q ^ 2 * (2 * a0 +
      q ^ 2 * (2 * a1 + q ^ 2 * (2 * pv + q ^ 2 * (2 * pc)))))) + (q ^ 2 + 1) * (2 * h +
      q ^ 4 * (2 * tt)) + q ^ 8 * (2 * h * (z + q ^ 2 * C.S))) := by
    have hrZ : ((2 * r + 1 : ℕ) : ℤ) = ((q ^ 12 + ((q - 1) * (2 * km + q ^ 2 * (2 * dd + q ^ 2 *
        (2 * a0 + q ^ 2 * (2 * a1 + q ^ 2 * (2 * pv + q ^ 2 * (2 * pc)))))) + (q ^ 2 + 1) *
        (2 * h + q ^ 4 * (2 * tt)) + q ^ 8 * (2 * h * (z + q ^ 2 * C.S))) : ℕ) : ℤ) := by
      have hrep12Z : 2 * (rep (12 * e) : ℤ) + 1 = (q : ℤ) ^ 12 := by
        have h' : ((2 * rep (12 * e) + 1 : ℕ) : ℤ) = ((q ^ 12 : ℕ) : ℤ) := by rw [hrep12, hq12]
        push_cast at h'
        exact h'
      have hsK : (kp : ℤ) + km = h := by exact_mod_cast sK
      have hsD : (ddb : ℤ) + dd = h := by exact_mod_cast sD
      have hsA0 : (b0 : ℤ) + a0 = tt := by exact_mod_cast sA0
      have hsA1 : (b1 : ℤ) + a1 = tt := by exact_mod_cast sA1
      have hsV : (pvb : ℤ) + pv = z * h := by exact_mod_cast sV
      have hsC : (pcb : ℤ) + pc = C.S * h := by exact_mod_cast sC
      rw [hrdef, hPh]
      push_cast [Nat.cast_sub (show 1 ≤ q by omega)]
      linear_combination (2 : ℤ) * hsK + hrep12Z + 2 * (q : ℤ) ^ 2 * hsD
        + 2 * (q : ℤ) ^ 4 * hsA0 + 2 * (q : ℤ) ^ 6 * hsA1 + 2 * (q : ℤ) ^ 8 * hsV
        + 2 * (q : ℤ) ^ 10 * hsC
    exact_mod_cast hrZ
  refine ⟨q, q - 1, W, 2 * h, v, 2 * tt, 2 * a0, 2 * a1, 2 * kp, 2 * km, 2 * dd, α, R, 2 * pc,
    2 * pv, q ^ 12 - r, z, r, a, c, d, f, hh2, i, j, k, o, s, w, τ, η, ζ, γ, y, ?_, ?_⟩
  · exact
      { x := hx, q := hq0, J := by omega, W := hW, H := by omega, v := hv, t := by omega,
        A0 := by omega, A1 := by omega, Kp := by omega, Km := by omega, D := by omega,
        α := hα, R := hR, PC := by omega, PV := by omega, β := hβ, z := hz, r := by omega,
        kernel := hKP }
  · exact
      { E0 := by omega
        E1 := E1
        E2 := by rw [Nat.mul_assoc, E2]; ring
        E3 := by omega
        E4 := E4
        E5 := by linarith
        E6 := by linarith
        E7 := E7
        E8 := E8
        kernel := hK
        E19 := E19
        E20 := by omega
        E21 := by
          calc R * C.K * (2 * pc) = 2 * (R * C.K * pc) := by ring
            _ = _ := by rw [E21]; ring }

end Jones1980
