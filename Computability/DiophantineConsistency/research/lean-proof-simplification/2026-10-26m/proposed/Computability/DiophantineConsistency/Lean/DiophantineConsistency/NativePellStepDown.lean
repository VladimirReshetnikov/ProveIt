import Diophantine.Paper1980.PellHalf90
import DiophantineConsistency.SignedPellResidue

/-!
# Signed auxiliary Pell step-down for the native minus-sign block

The main Pell classification and its bootstrap are explicit hypotheses here.
The auxiliary coordinate may have either sign; no odd-rank hypothesis or
positivity-restoring substitution is used.
-/

namespace DiophantineConsistency.NativePellStepDown

open Diophantine Pell Jones1980

/-- Auxiliary Pell classification yields the two possible main-index residues.
The hypotheses on `u` are invariant under replacing `u` by `-u`. -/
theorem index_residues {A c f I J p m y u : ℕ}
    (hA : 1 < A) (hp : 0 < p) (hcp : c = yn hA p)
    (hf : f = xn hA m) (hpm : 2 * p ≤ m) (hcm : c ∣ m)
    (hI1 : 1 < I) (hcI₀ : c ∣ I)
    (hIsq : (I : ℤ) ^ 2 = ((A : ℤ) ^ 2 - 1) * ((f : ℤ) ^ 2 - 1))
    (hy : 0 < y)
    (haux : ((I : ℤ) * u) ^ 2 = 1 + ((I : ℤ) ^ 2 - 1) * y ^ 2)
    (hu_sq : (u : ℤ) ^ 2 ≡ (c : ℤ) ^ 2 [ZMOD f])
    (hu_J : (u : ℤ) ≡ J [ZMOD c] ∨ (u : ℤ) ≡ -(J : ℤ) [ZMOD c]) :
    (c : ℤ) ∣ (J : ℤ) - p ∨ (c : ℤ) ∣ (J : ℤ) + p := by
  -- the Pell pair `(I u, y)` for the parameter `I`
  have hI2 : 1 ≤ I ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hpell : (I * u) ^ 2 = 1 + (I ^ 2 - 1) * y ^ 2 := by
    have : (((I * u) ^ 2 : ℕ) : ℤ) = ((1 + (I ^ 2 - 1) * y ^ 2 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hI2]; exact haux
    exact_mod_cast this
  obtain ⟨s, hIu, hys⟩ := eq_pell_of_sq hI1 hpell
  have hIZ0 : (I : ℤ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hsodd : Odd s := SignedPellResidue.odd_index_of_base_dvd hI1
    (by rw [← hIu]; exact dvd_mul_right I u)
  obtain ⟨h, hs⟩ := hsodd
  -- `u = Q_h(I²)`
  have hu_eq : (u : ℤ) = Qh h ((I : ℤ) ^ 2) := by
    have e1 : (xn hI1 s : ℤ) = I * Qh h ((I : ℤ) ^ 2) := by
      rw [xn_eq_xr hI1, hs]; exact xr_odd_eq (I : ℤ) h
    have e2 : (xn hI1 s : ℤ) = I * u := by rw [← hIu]; push_cast; ring
    exact mul_left_cancel₀ hIZ0 (e2.symm.trans e1)
  -- `I² ≡ 1 − A² (mod f)`
  have hIf : (I : ℤ) ^ 2 ≡ 1 - (A : ℤ) ^ 2 [ZMOD f] := by
    rw [Int.modEq_iff_dvd, hIsq]
    exact ⟨-((A : ℤ) ^ 2 - 1) * f, by ring⟩
  have hu_f : (u : ℤ) ≡ (-1) ^ h * yn hA s [ZMOD f] := by
    have := Qh_modEq hIf h
    rw [Qh_eval_one_sub_sq, ← yn_eq_yr hA, ← hs, ← hu_eq] at this
    exact this
  -- `ψ_A(s)² ≡ ψ_A(p)² (mod f)` and the step-down
  have hsq : (yn hA s : ℤ) ^ 2 ≡ (yn hA p : ℤ) ^ 2 [ZMOD f] := by
    have h1 := hu_f.pow 2
    have e : ((-1 : ℤ) ^ h * yn hA s) ^ 2 = (yn hA s : ℤ) ^ 2 := by
      rw [mul_pow, ← pow_mul, mul_comm h 2, pow_mul]; simp
    rw [e] at h1
    exact h1.symm.trans (by simpa only [hcp] using hu_sq)
  have hstep : (xn hA m : ℤ) ∣ (xn hA (2 * s) : ℤ) - xn hA (2 * p) := by
    rw [← hf, xn_two_mul_eq_yn hA s, xn_two_mul_eq_yn hA p]
    have := (Int.modEq_iff_dvd.1 hsq.symm)
    obtain ⟨k, hk⟩ := this
    exact ⟨2 * ((A : ℤ) ^ 2 - 1) * k, by linear_combination 2 * ((A : ℤ) ^ 2 - 1) * hk⟩
  have hsp := step_down hA hp hpm (Or.inl hstep)
  have hcmZ : (c : ℤ) ∣ m := by exact_mod_cast hcm
  have hsp' : (c : ℤ) ∣ (s : ℤ) - p ∨ (c : ℤ) ∣ (s : ℤ) + p := by
    rcases hsp with hh | hh
    · exact Or.inl (dvd_trans hcmZ hh)
    · exact Or.inr (dvd_trans hcmZ hh)
  -- `u ≡ (−1)^h s (mod c)` and `u ≡ J (mod c)`
  have hcI : (c : ℤ) ∣ (I : ℤ) ^ 2 := by
    exact dvd_pow (by exact_mod_cast hcI₀) (by decide : 2 ≠ 0)
  have hu_cc : (u : ℤ) ≡ (-1) ^ h * s [ZMOD c] := by
    have h0 : (I : ℤ) ^ 2 ≡ 0 [ZMOD c] := (Int.modEq_zero_iff_dvd).2 hcI
    have := Qh_modEq h0 h
    rw [Qh_eval_zero, ← hu_eq] at this
    rw [hs]; push_cast; exact this
  exact SignedModEq.iff_dvd_sub_or_add.mp
    (((SignedModEq.symm hu_J).trans
      (SignedModEq.of_sign_mul hu_cc (neg_one_pow_eq_or ℤ h))).trans
      (SignedModEq.iff_dvd_sub_or_add.mpr hsp'))

/-- The same index residues for a signed auxiliary coordinate with the native
minus-sign congruences. -/
theorem signed_index_residues {A c f I J p m y : ℕ} {V : ℤ}
    (hA : 1 < A) (hp : 0 < p) (hcp : c = yn hA p)
    (hf : f = xn hA m) (hpm : 2 * p ≤ m) (hcm : c ∣ m)
    (hI1 : 1 < I) (hcI : c ∣ I)
    (hIsq : (I : ℤ) ^ 2 = ((A : ℤ) ^ 2 - 1) * ((f : ℤ) ^ 2 - 1))
    (hy : 0 < y)
    (haux : (I : ℤ) ^ 2 * V ^ 2 - ((I : ℤ) ^ 2 - 1) * (y : ℤ) ^ 2 = 1)
    (hVf : V ≡ -(c : ℤ) [ZMOD f]) (hVJ : V ≡ -(J : ℤ) [ZMOD c]) :
    (c : ℤ) ∣ (J : ℤ) - p ∨ (c : ℤ) ∣ (J : ℤ) + p := by
  have hvsq : (V.natAbs : ℤ) ^ 2 = V ^ 2 := by
    rcases Int.natAbs_eq V with h | h <;> rw [h] <;> simp
  have hvaux : ((I : ℤ) * V.natAbs) ^ 2 =
      1 + ((I : ℤ) ^ 2 - 1) * (y : ℤ) ^ 2 := by
    rw [mul_pow, hvsq]
    linear_combination haux
  have hvf : (V.natAbs : ℤ) ^ 2 ≡ (c : ℤ) ^ 2 [ZMOD f] := by
    have h := hVf.pow 2
    simpa only [neg_sq, ← hvsq] using h
  have hvJ : SignedModEq c (V.natAbs : ℤ) J :=
    (SignedModEq.natAbs c V).symm.trans (Or.inr hVJ)
  exact index_residues hA hp hcp hf hpm hcm hI1 hcI hIsq hy hvaux hvf hvJ

/-- Half-modulus bounds remove both sign and nonzero-multiple ambiguity. -/
theorem eq_of_residues {c J p : ℕ} (hp : 0 < p) (hJ : 0 < J)
    (hpc : 2 * p < c) (hJc : 2 * J < c)
    (hres : (c : ℤ) ∣ (J : ℤ) - p ∨ (c : ℤ) ∣ (J : ℤ) + p) : p = J := by
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
  have hJZ : (0 : ℤ) < J := by exact_mod_cast hJ
  have hpcZ : (2 : ℤ) * p < c := by exact_mod_cast hpc
  have hJcZ : (2 : ℤ) * J < c := by exact_mod_cast hJc
  rcases hres with h | h
  · have hzero : (J : ℤ) - p = 0 :=
      Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    exact_mod_cast (show (p : ℤ) = J by omega)
  · have hzero : (J : ℤ) + p = 0 :=
      Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    omega

/-- The native minus-sign block recovers the main index.  In particular `V`,
`j` and `o` need not be positive.  Main classification and half-modulus bounds
are explicit prerequisites rather than conclusions of this theorem. -/
theorem source_index {A c f I J p m y : ℕ} {V j o : ℤ}
    (hA : 1 < A) (hp : 0 < p) (hJ : 0 < J)
    (hcp : c = yn hA p) (hf : f = xn hA m)
    (hpm : 2 * p ≤ m) (hcm : c ∣ m)
    (hpc : 2 * p < c) (hJc : 2 * J < c)
    (hI1 : 1 < I) (hcI : c ∣ I)
    (hIsq : (I : ℤ) ^ 2 = ((A : ℤ) ^ 2 - 1) * ((f : ℤ) ^ 2 - 1))
    (hy : 0 < y)
    (haux : (I : ℤ) ^ 2 * V ^ 2 - ((I : ℤ) ^ 2 - 1) * (y : ℤ) ^ 2 = 1)
    (hVj : V = j * c - J) (hVo : V = o * f - c) : p = J := by
  apply eq_of_residues hp hJ hpc hJc
  apply signed_index_residues hA hp hcp hf hpm hcm hI1 hcI hIsq hy haux
  · rw [Int.modEq_iff_dvd, hVo]
    exact ⟨-o, by ring⟩
  · rw [Int.modEq_iff_dvd, hVj]
    exact ⟨-j, by ring⟩

/-- The existing relaxed strong-norm theorem supplies the auxiliary main
sequence data.  The unresolved native main-index classification and bootstrap
are precisely the explicit `hcp`, `hbig`, `hpc`, and `hJc` premises. -/
theorem source_index_of_strong {A c f i J p y : ℕ} {V j o : ℤ}
    (hA : 1 < A) (hp : 0 < p) (hJ : 0 < J)
    (hcp : c = yn hA p) (hi : 0 < i) (hf0 : 0 < f)
    (hbig : A * (A ^ 2 - 1) ^ 2 < c)
    (hpc : 2 * p < c) (hJc : 2 * J < c)
    (hnorm : (i * c ^ 2) ^ 2 = (A ^ 2 - 1) * (f ^ 2 - 1))
    (hy : 0 < y)
    (haux : ((i * c ^ 2 : ℕ) : ℤ) ^ 2 * V ^ 2 -
      (((i * c ^ 2 : ℕ) : ℤ) ^ 2 - 1) * (y : ℤ) ^ 2 = 1)
    (hVj : V = j * c - J) (hVo : V = o * f - c) : p = J := by
  obtain ⟨m, hf, _, hcm, hR⟩ := relaxed_aux hA hp hcp hi hf0 hnorm hbig
  have hIc : c ≤ i * c ^ 2 := by
    have hmul : c ^ 2 ≤ i * c ^ 2 := Nat.le_mul_of_pos_left _ hi
    have hc2 : c ≤ c ^ 2 := by nlinarith
    omega
  have hI1 : 1 < i * c ^ 2 := by omega
  have hm0 : 0 < m := by
    by_contra hm
    have hm : m = 0 := by omega
    rw [hm, yn_zero, mul_zero] at hR
    omega
  have hcmle : c ≤ m := Nat.le_of_dvd hm0 hcm
  have hpm : 2 * p ≤ m := by omega
  have hcI : c ∣ i * c ^ 2 := ⟨i * c, by ring⟩
  have hA2 : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hf2 : 1 ≤ f ^ 2 := Nat.one_le_pow _ _ hf0
  have hIsq : ((i * c ^ 2 : ℕ) : ℤ) ^ 2 =
      ((A : ℤ) ^ 2 - 1) * ((f : ℤ) ^ 2 - 1) := by
    have h := congrArg (fun t : ℕ => (t : ℤ)) hnorm
    push_cast [Nat.cast_sub hA2, Nat.cast_sub hf2] at h ⊢
    exact h
  exact source_index hA hp hJ hcp hf hpm hcm hpc hJc hI1 hcI hIsq hy haux hVj hVo

/-- Quotient restoration is sound once the strong rank recovery has supplied
`c ∣ f²-1`; no cancellation of the Pell discriminant is used. -/
theorem quotient_dvd {c f o J : ℤ}
    (hcf : c ∣ f ^ 2 - 1) (hV : c ∣ o * f + J) : c ∣ o + J * f := by
  have h₁ : c ∣ (o * f + J) * f := dvd_mul_of_dvd_left hV f
  have h₂ : c ∣ o * (f ^ 2 - 1) := dvd_mul_of_dvd_right hcf o
  have heq : o + J * f = (o * f + J) * f - o * (f ^ 2 - 1) := by ring
  rw [heq]
  exact dvd_sub h₁ h₂

/-- Substituting the restored quotient exactly reproduces the original
minus-sign auxiliary coordinate. -/
theorem quotient_identity {c f o J T : ℤ} (hT : c * T = o + J * f) :
    c * (T * f - 1) - J * f ^ 2 = o * f - c := by
  linear_combination f * hT

end DiophantineConsistency.NativePellStepDown
