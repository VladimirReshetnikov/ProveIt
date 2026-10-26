import Diophantine.Paper1980.PellHalf90
import DiophantineConsistency.ThirteenCarrierSoundness

/-!
# Fresh private Pell witnesses for the thirteen-coordinate carrier

The outer rank and its Pell ordinate are fixed. The strong seed is chosen
afresh with an ordinate divisible by b*c². No compatibility with an existing
parent's private coordinates is assumed. The only transport hypotheses are
G>0 and b∣G. Native production of the outer data is a separate theorem.
-/

namespace DiophantineConsistency.ThirteenFreshSeed

open Diophantine Pell Jones1980

/-- The two congruences produce the literal quotient without a CRT premise. -/
theorem quotient_exists {c f V R : ℤ} (hc : 0 < c) (hf : 0 < f)
    (hV : 0 < V) (hR : 0 < R) (hfv : f ^ 2 ∣ V + c)
    (hcv : c ∣ V + R) (hcf : c ∣ f ^ 2 - 1) :
    ∃ T : ℤ, 0 < T ∧ V = f ^ 2 * (c * T - R) - c := by
  obtain ⟨o, ho⟩ := hfv
  have hf2 : 0 < f ^ 2 := pow_pos hf _
  have ho0 : 0 < o := by
    have : 0 < f ^ 2 * o := by rw [← ho]; omega
    exact pos_of_mul_pos_right this hf2.le
  have hd : c ∣ o + R := by
    have h := dvd_add (dvd_sub hcv (dvd_mul_of_dvd_left hcf o)) (dvd_refl c)
    have he : V + R - (f ^ 2 - 1) * o + c = o + R := by
      linear_combination ho
    rwa [he] at h
  obtain ⟨T, hT⟩ := hd
  have hT0 : 0 < T := by
    have : 0 < c * T := by rw [← hT]; omega
    exact pos_of_mul_pos_right this hc.le
  exact ⟨T, hT0, by linear_combination ho + f ^ 2 * hT⟩

/-- The independent m coordinate is positive, including for a negative signed ordinate. -/
theorem carrier_exists {b G V y : ℤ} (hb : 0 < b) (hG : 0 < G)
    (hV : 0 < V) (hsmall : -2 * V < y) (hd : b ∣ G)
    (hy : 4 * b ∣ y - 1) :
    ∃ m : ℤ, 0 < m ∧ y = 1 + 4 * (b * (m - V ^ 2 * G) - G) := by
  obtain ⟨g, hg⟩ := hd
  obtain ⟨e, he⟩ := hy
  have hg0 : 0 < g := by
    have : 0 < b * g := by rwa [← hg]
    exact pos_of_mul_pos_right this hb.le
  let m := e + (1 + b * V ^ 2) * g
  have hm : 4 * b * m = y - 1 + 4 * b * (1 + b * V ^ 2) * g := by
    dsimp [m]
    linear_combination -he
  have hVs : V ≤ V ^ 2 := by nlinarith
  have hbVs : V ^ 2 ≤ b * V ^ 2 := by
    have := mul_nonneg (show 0 ≤ b - 1 by omega) (sq_nonneg V)
    nlinarith only [this]
  have hcoef : 4 * (1 + V) ≤ 4 * b * (1 + b * V ^ 2) := by
    have := mul_nonneg (show 0 ≤ b - 1 by omega)
      (show 0 ≤ 1 + b * V ^ 2 by positivity)
    nlinarith only [this, hVs, hbVs]
  have hgcoef : 4 * b * (1 + b * V ^ 2) ≤ 4 * b * (1 + b * V ^ 2) * g := by
    have := mul_nonneg (show 0 ≤ g - 1 by omega)
      (show 0 ≤ 4 * b * (1 + b * V ^ 2) by positivity)
    nlinarith only [this]
  have hm0 : 0 < m := by
    have hprod : 0 < 4 * b * m := by linarith
    exact pos_of_mul_pos_right hprod (by positivity)
  refine ⟨m, hm0, ?_⟩
  dsimp [m]
  rw [hg]
  linear_combination he

/-- A fresh strong seed and an auxiliary pair at any rank congruent to 3 modulo 4.
The returned signed ordinate is negative; it is not an independent unknown. -/
theorem auxiliary_exists (A R b : ℕ) (hA : 1 < A) (hb : 0 < b)
    (hR : R % 4 = 3) :
    let c : ℤ := yn hA R
    let delta : ℤ := (A : ℤ) ^ 2 - 1
    ∃ f i T V y : ℤ,
      0 < f ∧ 0 < i ∧ 0 < T ∧ 0 < V ∧ y < 0 ∧
      f ^ 2 - delta * ((b : ℤ) * i * c ^ 2) ^ 2 = 1 ∧
      V = f ^ 2 * (c * T - R) - c ∧
      (delta * ((b : ℤ) * i * c ^ 2)) ^ 2 * (V ^ 2 - y ^ 2) + y ^ 2 = 1 ∧
      4 * (b : ℤ) ∣ y - 1 ∧ -2 * V < y := by
  let c : ℕ := yn hA R
  have hR0 : 0 < R := by omega
  have hc : 0 < c := JSWW1976.ψ_pos_of_pos hA hR0
  obtain ⟨t, ht, hdt⟩ := Diophantine.exists_dvd_yn hA (show 0 < b * c ^ 2 by positivity)
  obtain ⟨i, hi⟩ := hdt
  have hI : 0 < yn hA t := JSWW1976.ψ_pos_of_pos hA ht
  have hi0 : 0 < i := by
    by_contra h
    have : i = 0 := by omega
    rw [this, mul_zero] at hi
    omega
  let f : ℤ := xn hA t
  let delta : ℤ := (A : ℤ) ^ 2 - 1
  have hf : 0 < f := by
    dsimp [f]
    exact_mod_cast xn_pos' hA t
  have hAA : 1 ≤ A * A := by nlinarith
  have hIc : (yn hA t : ℤ) = (b : ℤ) * i * (c : ℤ) ^ 2 := by
    have h := congrArg (fun x : ℕ => (x : ℤ)) hi
    push_cast at h
    nlinarith only [h]
  have hp : f ^ 2 - delta * (yn hA t : ℤ) ^ 2 = 1 := by
    simpa only [f, delta, xz, yz, dz_val, az, pow_two, mul_assoc] using pell_eqz hA t
  let S : ℕ := (A * A - 1) * yn hA t
  have hS : 1 < S := by
    have hD : 2 ≤ A * A - 1 := by
      have : 4 ≤ A * A := by nlinarith
      omega
    dsimp [S]
    nlinarith
  have hSz : (S : ℤ) = delta * (yn hA t : ℤ) := by
    dsimp [S, delta]
    push_cast [Nat.cast_sub hAA]
    ring
  have hSsq : (S : ℤ) ^ 2 = delta * (f ^ 2 - 1) := by
    rw [hSz]
    linear_combination -delta * hp
  obtain ⟨j, hj⟩ : ∃ j : ℕ, R = 2 * j + 1 := ⟨R / 2, by omega⟩
  have hjodd : Odd j := ⟨j / 2, by omega⟩
  let V : ℤ := Qh j ((S : ℤ) ^ 2)
  let y : ℤ := -(yn hS R : ℤ)
  have hx : (xn hS R : ℤ) = S * V := by
    rw [xn_eq_xr hS, hj]
    exact xr_odd_eq (S : ℤ) j
  have hV : 0 < V := by
    have hx0 : (0 : ℤ) < xn hS R := by exact_mod_cast xn_pos' hS R
    rw [hx] at hx0
    exact pos_of_mul_pos_right hx0 (by positivity)
  have hy : y < 0 := by
    have := JSWW1976.ψ_pos_of_pos hS hR0
    dsimp [y]
    exact neg_neg_of_pos (by exact_mod_cast this)
  have hnorm : (S : ℤ) ^ 2 * V ^ 2 - ((S : ℤ) ^ 2 - 1) * y ^ 2 = 1 := by
    have h := pell_eqz hS R
    simp only [xz, yz, dz_val, az, hx] at h
    dsimp [y]
    nlinarith only [h]
  have hRf : (S : ℤ) ^ 2 ≡ 1 - (A : ℤ) ^ 2 [ZMOD f ^ 2] := by
    rw [Int.modEq_iff_dvd, hSsq]
    refine ⟨-delta, ?_⟩
    dsimp [delta]
    ring
  have hfv : f ^ 2 ∣ V + (c : ℤ) := by
    have h := Qh_modEq hRf j
    rw [Qh_eval_one_sub_sq, ← yn_eq_yr hA, ← hj, hjodd.neg_one_pow] at h
    have hh : V ≡ -(c : ℤ) [ZMOD f ^ 2] := by simpa [V, c] using h
    have := Int.modEq_iff_dvd.mp hh.symm
    simpa using this
  have hcS : (c : ℤ) ∣ (S : ℤ) ^ 2 := by
    rw [hSz, hIc]
    exact ⟨delta ^ 2 * (b : ℤ) ^ 2 * i ^ 2 * (c : ℤ) ^ 3, by ring⟩
  have hcv : (c : ℤ) ∣ V + (R : ℤ) := by
    have h := Qh_modEq hcS.modEq_zero_int j
    rw [Qh_eval_zero, hjodd.neg_one_pow] at h
    have hh : V ≡ -(R : ℤ) [ZMOD c] := by
      dsimp [V]
      rw [hj]
      push_cast
      simpa using h
    simpa using Int.modEq_iff_dvd.mp hh.symm
  have hcf : (c : ℤ) ∣ f ^ 2 - 1 := by
    refine ⟨delta * (b : ℤ) ^ 2 * i ^ 2 * (c : ℤ) ^ 3, ?_⟩
    rw [hIc] at hp
    nlinarith only [hp]
  obtain ⟨T, hT, hVT⟩ := quotient_exists (by exact_mod_cast hc) hf hV
    (by exact_mod_cast hR0) hfv hcv hcf
  have hyres : y ≡ 1 [ZMOD 4 * (S : ℤ) ^ 2] := by
    have h := SignedPellResidue.odd_ordinate_modEq (S : ℤ) j
    rw [hjodd.neg_one_pow, ← yn_eq_yr hS, ← hj] at h
    simpa [y] using h.neg
  have hbS : 4 * (b : ℤ) ∣ 4 * (S : ℤ) ^ 2 := by
    rw [hSz, hIc]
    exact ⟨delta ^ 2 * b * i ^ 2 * (c : ℤ) ^ 4, by ring⟩
  have hydiv : 4 * (b : ℤ) ∣ y - 1 :=
    hbS.trans (Int.modEq_iff_dvd.mp hyres.symm)
  have hsmall := (ThirteenCarrierSoundness.auxiliary_estimates
    (by exact_mod_cast (show 2 ≤ S by omega) : (2 : ℤ) ≤ S) hnorm).2
  rw [abs_of_neg hy, abs_of_pos hV] at hsmall
  refine ⟨f, i, T, V, y, hf, by exact_mod_cast hi0, hT, hV, hy, ?_, hVT, ?_, hydiv, by omega⟩
  · change f ^ 2 - delta * ((b : ℤ) * i * (c : ℤ) ^ 2) ^ 2 = 1
    rw [← hIc]
    exact hp
  · rw [← hIc, ← hSz]
    nlinarith only [hnorm]

/-- The four positive private inputs, with both literal thirteen-variable norms.
This is a constructive arithmetic existence theorem, not a native equivalence premise. -/
theorem fresh_private_seed (A R b : ℕ) (hA : 1 < A) (hb : 0 < b)
    (hR : R % 4 = 3) (G : ℤ) (hG : 0 < G) (hd : (b : ℤ) ∣ G) :
    let c : ℤ := yn hA R
    let delta : ℤ := (A : ℤ) ^ 2 - 1
    ∃ f i T m : ℤ, 0 < f ∧ 0 < i ∧ 0 < T ∧ 0 < m ∧
      let S := delta * ((b : ℤ) * i * c ^ 2)
      let V := f ^ 2 * (c * T - R) - c
      let y := 1 + 4 * ((b : ℤ) * (m - V ^ 2 * G) - G)
      f ^ 2 - delta * ((b : ℤ) * i * c ^ 2) ^ 2 = 1 ∧
        S ^ 2 * (V ^ 2 - y ^ 2) + y ^ 2 = 1 ∧ y < 0 := by
  obtain ⟨f, i, T, V, y, hf, hi, hT, hV, hy, hz, hVT, hu, hdiv, hsmall⟩ :=
    auxiliary_exists A R b hA hb hR
  obtain ⟨m, hm, hym⟩ := carrier_exists (by exact_mod_cast hb) hG hV hsmall hd hdiv
  refine ⟨f, i, T, m, hf, hi, hT, hm, hz, ?_, ?_⟩
  · rw [← hVT, ← hym]
    exact hu
  · rw [← hVT, ← hym]
    exact hy

end DiophantineConsistency.ThirteenFreshSeed

#print axioms DiophantineConsistency.ThirteenFreshSeed.auxiliary_exists
#print axioms DiophantineConsistency.ThirteenFreshSeed.fresh_private_seed
