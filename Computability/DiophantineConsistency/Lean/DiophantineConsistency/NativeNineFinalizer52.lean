import DiophantineConsistency.NativeNineRatio52
import DiophantineConsistency.RatioMarginFinalizer

/-! # The literal package-52 finalizer on its actual Jones ratio registers -/

namespace DiophantineConsistency.NativeNineRatio52

open Jones1982

namespace NewVars

def k (v : NewVars) (R N b g cap : ℕ) : ℤ :=
  let u := v.base R N b g cap
  v.i * u.J * u.C

def V0 (v : NewVars) (R N b g cap : ℕ) : ℤ :=
  let u := v.base R N b g cap
  u.P * u.K

def V1 (v : NewVars) (R N b g cap : ℕ) : ℤ :=
  let u := v.base R N b g cap
  v.k R N b g cap * (8 * u.D ^ 2 - 4 * u.D - 1) * u.Gp * v.Hnew R N b g cap

/-- The exact polynomial F9, with no hidden quotient offsets. -/
def finalValue (v : NewVars) (R N b g cap n : ℕ) : ℤ :=
  let u := v.base R N b g cap
  MarginFinalizer.value ((u.P ^ 2 - 1) * u.K ^ 2 + 1)
    (u.D * u.F * v.Inew R N b g cap) (v.V0 R N b g cap)
      (v.V1 R N b g cap) u.J u.Q (v.margin R N b g cap) n

end NewVars

theorem finalValue_eq (v : NewVars) (R N b g cap n : ℕ) :
    let u := v.base R N b g cap
    let omega := u.J * v.margin R N b g cap
    let theta := u.J * (n : ℤ) + u.Q - omega * (v.V0 R N b g cap + v.V1 R N b g cap)
    v.finalValue R N b g cap n =
      (theta ^ 2 - omega ^ 2 *
        (((u.P ^ 2 - 1) * u.K ^ 2 + 1) + 64 * (u.D * u.F * v.Inew R N b g cap))) ^ 2 -
        256 * omega ^ 4 * ((u.P ^ 2 - 1) * u.K ^ 2 + 1) * (u.D * u.F * v.Inew R N b g cap) :=
  MarginFinalizer.value_eq _ _ _ _ _ _ _ _

/-- All majorant and conditional-separation hypotheses hold for the actual
ratio registers, solely from the original primitive range assumptions. -/
theorem exists_finalValue_zero_iff_conditions {R N b g cap : ℕ} (v : NewVars)
    (hR : 8 ≤ R) (hN : 8 ≤ N) (hb : 0 < b) (hcap : 0 < cap)
    (hs : 0 < v.s) (hw : 0 < v.w) (hi : 0 < v.i) :
    (∃ n : ℕ, v.finalValue R N b g cap n = 0) ↔ v.Conditions R N b g cap := by
  let u := v.base R N b g cap
  have hRZ : 8 ≤ (R : ℤ) := by exact_mod_cast hR
  have hNZ : 8 ≤ (N : ℤ) := by exact_mod_cast hN
  have hbZ : 0 < (b : ℤ) := by exact_mod_cast hb
  have hsZ : 1 ≤ (v.s : ℤ) := by exact_mod_cast hs
  have hwZ : 0 < (v.w : ℤ) := by exact_mod_cast hw
  have hiZ : 1 ≤ (v.i : ℤ) := by exact_mod_cast hi
  obtain ⟨hB, hBC, hF⟩ := register_bounds (g := g) (cap := cap) v hR hN hb hs hw
  have hC0 : 0 < u.C := hB.trans hBC
  have hC : 1 ≤ u.C := by omega
  have hY : 2 ≤ u.Y := by
    change 2 ≤ (N : ℤ) ^ 2 * v.s
    have hN2 : 64 ≤ (N : ℤ) ^ 2 := by nlinarith only [hNZ]
    have hmul := mul_le_mul_of_nonneg_left hsZ (sq_nonneg (N : ℤ))
    nlinarith only [hN2, hmul]
  have hM : 0 < u.M := by
    change 0 < (R : ℤ) * u.Y
    exact mul_pos (by omega) (by omega)
  have hU : 0 < u.U := by
    change 0 < (N : ℤ) ^ 2 * (v.w : ℤ)
    exact mul_pos (sq_pos_of_pos (by omega)) hwZ
  have hP : 0 < u.P := by
    change 0 < 2 * u.M ^ 2 * u.U
    positivity
  have hA : 2 ≤ u.A := by
    have hsz := (Nine.sizes_nat hR hN hs hw).2
    change 2 ≤ (Nine.Vars.ofNat R N b g cap v.h v.s v.w v.phi v.i 0).A
    rw [Nine.cA]
    exact_mod_cast hsz
  have hK : 2 ≤ u.K := by
    change 2 ≤ (R : ℤ) + 1 + (v.h : ℤ) * (u.P - 1)
    have hmul := mul_nonneg (Int.natCast_nonneg v.h) (show 0 ≤ u.P - 1 by omega)
    linarith only [hRZ, hmul]
  have hJ : 3 ≤ u.J := by change 3 ≤ 4 * u.A - 5; omega
  have hJ0 : 0 < u.J := by omega
  have hD : 0 < u.D := by
    change 0 < (u.A ^ 2 - 1) * u.C ^ 2 + 1
    have hAm : 0 ≤ u.A ^ 2 - 1 := by nlinarith only [hA]
    nlinarith only [mul_nonneg hAm (sq_nonneg u.C)]
  have hE0 : 0 < u.E := by
    change 0 < (v.i : ℤ) * u.J * u.D * u.C ^ 2
    exact mul_pos (mul_pos (mul_pos (by omega) hJ0) hD) (sq_pos_of_pos hC0)
  have hE : 1 ≤ u.E := by omega
  have hH : 1 ≤ v.Hnew R N b g cap := by
    change 1 ≤ u.C + u.F * (u.B' + (v.j : ℤ) * u.C)
    have hBj : 0 < u.B' + (v.j : ℤ) * u.C :=
      add_pos_of_pos_of_nonneg hB (mul_nonneg (Int.natCast_nonneg v.j) (le_of_lt hC0))
    have hprod := mul_pos hF hBj
    linarith only [hC, hprod]
  have hk : 3 ≤ v.k R N b g cap := by
    change 3 ≤ (v.i : ℤ) * u.J * u.C
    have hIJ : u.J ≤ (v.i : ℤ) * u.J := by
      nlinarith only [mul_nonneg (show 0 ≤ (v.i : ℤ) - 1 by omega) (le_of_lt hJ0)]
    have hIJC : (v.i : ℤ) * u.J ≤ (v.i : ℤ) * u.J * u.C := by
      have hIJ0 : 0 ≤ (v.i : ℤ) * u.J := by positivity
      nlinarith only [mul_nonneg hIJ0 (show 0 ≤ u.C - 1 by omega)]
    linarith only [hJ, hIJ, hIJC]
  have hW : 0 < u.W := by change 0 < (b : ℤ) * v.w; exact mul_pos hbZ hwZ
  have hWC : u.W < u.C := by
    change (b : ℤ) * v.w < 2 * (R : ℤ) + 1 + (b : ℤ) * v.w + v.phi
    nlinarith only [hRZ, Int.natCast_nonneg v.phi]
  have hPA : u.P < u.A ^ 2 := by
    change 2 * u.M ^ 2 * u.U < (u.M * (u.U + 1)) ^ 2
    exact MarginSeparation.ratio_P_lt_A_sq hM
  have hEeq : u.E = v.k R N b g cap * u.D * u.C := by
    change (v.i : ℤ) * u.J * u.D * u.C ^ 2 = ((v.i : ℤ) * u.J * u.C) * u.D * u.C
    ring
  have hmeq : v.margin R N b g cap =
      (u.K ^ 2 - 4 * (u.C - u.K * u.Y) ^ 2) * (cap : ℤ) - 8 * (g : ℤ) * u.K ^ 2 := by
    change u.K ^ 2 * (cap : ℤ) - 4 * (u.C - u.K * u.Y) ^ 2 * (cap : ℤ) -
      8 * (g : ℤ) * u.K ^ 2 = _
    ring
  exact RatioMarginFinalizer.exists_value_zero_iff hP hK hA hC hE hH hk hW hWC
    hJ0 hY (by exact_mod_cast hcap) (Int.natCast_nonneg g) hPA rfl hEeq rfl rfl rfl rfl hmeq

/-- The actual F9 yields exactly the existing numerical ratio conclusion. -/
theorem finalizer_sound {R N b g cap : ℕ} (v : NewVars)
    (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b ≤ R) (hb : 0 < b) (hbN : b ≤ N)
    (hcap : 0 < cap) (hh : 0 < v.h) (hs : 0 < v.s) (hw : 0 < v.w) (hi : 0 < v.i)
    (hz : ∃ n : ℕ, v.finalValue R N b g cap n = 0) :
    N ^ 2 ∣ (2 * R).choose R ∧ (∃ k, b = 2 ^ k) ∧ 8 * g < cap :=
  ratio_sound_new v hR hN hbR hb hbN hcap hh hs hw hi
    ((exists_finalValue_zero_iff_conditions v hR hN hb hcap hs hw hi).mp hz)

/-- The existing strong completeness bound constructs an actual F9 zero. -/
theorem finalizer_complete {R N b g cap : ℕ}
    (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b ≤ R) (hb : 0 < b) (hbN : b ≤ N)
    (hgcap : 32 * g < cap) (hdvd : N ^ 2 ∣ (2 * R).choose R)
    (hpow : ∃ k, b = 2 ^ k) :
    ∃ v : NewVars, 0 < v.h ∧ 0 < v.s ∧ 0 < v.w ∧ 0 < v.i ∧
      ∃ n : ℕ, v.finalValue R N b g cap n = 0 := by
  obtain ⟨v, hh, hs, hw, hi, hc⟩ := ratio_complete_new hR hN hbR hb hbN hgcap hdvd hpow
  have hcap : 0 < cap := by omega
  exact ⟨v, hh, hs, hw, hi,
    (exists_finalValue_zero_iff_conditions v hR hN hb hcap hs hw hi).mpr hc⟩

end DiophantineConsistency.NativeNineRatio52
