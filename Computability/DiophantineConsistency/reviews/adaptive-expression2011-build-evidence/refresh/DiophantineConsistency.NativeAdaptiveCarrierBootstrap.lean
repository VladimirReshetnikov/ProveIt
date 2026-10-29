import DiophantineConsistency.NativePellBootstrap

/-! Signed first-carrier integrality and positivity, before source restoration.
The expressions are the literal A0 cut of the unrestricted-J adaptive graph.
No sign of Z or its integral quotient is assumed. -/

namespace DiophantineConsistency.NativeAdaptiveCarrierBootstrap

set_option Elab.async false

def firstZ (q ell k r Y Bt : ℤ) : ℤ :=
  (q ^ 3 * (q - 1)) * (ell + k + r) + (q - 1) * Y -
    q ^ 3 * ((q - 1) * k + 1) * Bt

def firstA0 (q ell k r Y Bt : ℤ) : ℤ :=
  firstZ q ell k r Y Bt ^ 2 -
    (q ^ 3 * (q - 1)) ^ 2 * (ell * (ell + k) + 1)

/-- The signed first carrier supplies positive quotient witnesses. Its Pell
root may have either sign, so only its absolute value is bounded. -/
theorem first_carrier_integral_positive {q ell k r Y Bt : ℤ}
    (hq : 1 < q) (hell : 0 < ell) (hk : 0 < k)
    (hr : 0 < r) (hY : 0 < Y)
    (h0 : firstA0 q ell k r Y Bt = 0) :
    ∃ s b tau : ℤ,
      0 < s ∧ 0 < b ∧
      Y = q ^ 3 * s ∧ Bt = (q - 1) * b ∧
      firstZ q ell k r Y Bt = (q ^ 3 * (q - 1)) * tau ∧
      tau ^ 2 = ell * (ell + k) + 1 ∧
      tau = ell + k + r + s - ((q - 1) * k + 1) * b ∧
      0 < |tau| ∧ |tau| < ell + k := by
  let M := q ^ 3 * (q - 1)
  let Z := firstZ q ell k r Y Bt
  let W := (q - 1) * k + 1
  have hq3 : 0 < q ^ 3 := pow_pos (by omega) _
  have hM : 0 < M := mul_pos hq3 (by omega)
  have hnorm : Z ^ 2 = M ^ 2 * (ell * (ell + k) + 1) := by
    change Z ^ 2 - M ^ 2 * (ell * (ell + k) + 1) = 0 at h0
    exact sub_eq_zero.mp h0
  have hdiv : M ∣ Z :=
    (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨ell * (ell + k) + 1, hnorm⟩
  obtain ⟨tau, htau⟩ := hdiv
  have hqY : q ^ 3 ∣ (q - 1) * Y := by
    refine ⟨(q - 1) * (tau - ell - k - r) + W * Bt, ?_⟩
    dsimp [Z, M, W, firstZ] at htau ⊢
    linear_combination htau
  obtain ⟨d, hd⟩ := hqY
  have hYdiv : q ^ 3 ∣ Y := by
    refine ⟨Y - (q ^ 2 + q + 1) * d, ?_⟩
    linear_combination -(q ^ 2 + q + 1) * hd
  have hBtdiv : q - 1 ∣ Bt := by
    refine ⟨q ^ 3 * (ell + k + r - tau) + Y -
      (q ^ 2 + q + 1 + q ^ 3 * k) * Bt, ?_⟩
    dsimp [Z, M, firstZ] at htau ⊢
    linear_combination -htau
  obtain ⟨s, hs⟩ := hYdiv
  obtain ⟨b, hb⟩ := hBtdiv
  have hspos : 0 < s := (mul_pos_iff_of_pos_left hq3).mp (by rwa [← hs])
  have htauNorm : tau ^ 2 = ell * (ell + k) + 1 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hM.ne')
    calc
      M ^ 2 * tau ^ 2 = Z ^ 2 := by rw [← mul_pow, ← htau]
      _ = M ^ 2 * (ell * (ell + k) + 1) := hnorm
  have htauEq : tau = ell + k + r + s - W * b := by
    apply mul_left_cancel₀ hM.ne'
    calc
      M * tau = Z := htau.symm
      _ = M * (ell + k + r + s - W * b) := by
        dsimp [Z, M, W, firstZ]
        rw [hs, hb]
        ring
  have htauNe : tau ≠ 0 := by
    intro hz
    have hprod : 0 < ell * (ell + k) := mul_pos hell (by omega)
    rw [hz] at htauNorm
    nlinarith
  have habspos : 0 < |tau| := abs_pos.mpr htauNe
  have hellk : 1 ≤ ell * k := by
    have h := mul_nonneg (show 0 ≤ ell - 1 by omega) (show 0 ≤ k - 1 by omega)
    nlinarith
  have hksq : 1 ≤ k ^ 2 := by nlinarith
  have hsq : tau ^ 2 < (ell + k) ^ 2 := by nlinarith [htauNorm]
  have habslt : |tau| < ell + k :=
    abs_lt_of_sq_lt_sq hsq (by omega : 0 ≤ ell + k)
  have hbpos : 0 < b := by
    by_contra h
    have hbnon : b ≤ 0 := by omega
    have hW : 0 ≤ W := by dsimp [W]; positivity
    have hWb : W * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hW hbnon
    have ht : tau < ell + k := (le_abs_self tau).trans_lt habslt
    linarith
  exact ⟨s, b, tau, hspos, hbpos, hs, hb, htau, htauNorm, htauEq, habspos, habslt⟩

/-- The actual positive transport polynomial forces a positive gap. -/
theorem transport_positive {q K X F alpha Bt : ℤ}
    (hq : 0 < q) (hK : 0 ≤ K) (hX : 0 < X) (hF : 0 < F)
    (hBt : Bt = (q * K + X) * (q - F - alpha) - q * F)
    (hpos : 0 < Bt) : 0 < q - F - alpha := by
  have hcoef : 0 < q * K + X := add_pos_of_nonneg_of_pos (mul_nonneg hq.le hK) hX
  by_contra h
  have hgap : q - F - alpha ≤ 0 := by omega
  have hprod := mul_nonpos_of_nonneg_of_nonpos hcoef.le hgap
  have hqF : 0 < q * F := mul_pos hq hF
  linarith

/-- Cast the positive parameters and the absolute value of a signed root
into the existing first-norm classification. No sign of tau is discarded. -/
theorem classify_signed_first_norm {Q k tau : ℤ}
    (hQ : 0 < Q) (hk : 0 < k)
    (hnorm : tau ^ 2 = 1 + Q * (Q + 1) * k ^ 2) :
    ∃ n : ℕ, 0 < n ∧
      |tau| = (Pell.xn (by omega : 1 < 2 * Q.toNat + 1) n : ℤ) ∧
      k = 2 * (Pell.yn (by omega : 1 < 2 * Q.toNat + 1) n : ℤ) := by
  have hQc : (Q.toNat : ℤ) = Q := Int.toNat_of_nonneg hQ.le
  have hkc : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk.le
  have hQn : 0 < Q.toNat := by omega
  have hkn : 0 < k.toNat := by omega
  have hnormZ : (tau.natAbs : ℤ) ^ 2 =
      1 + (Q.toNat : ℤ) * (Q.toNat + 1) * (k.toNat : ℤ) ^ 2 := by
    simpa only [hQc, hkc, Int.natCast_natAbs, sq_abs] using hnorm
  have hnormN : tau.natAbs ^ 2 = 1 + Q.toNat * (Q.toNat + 1) * k.toNat ^ 2 := by
    exact_mod_cast hnormZ
  obtain ⟨n, hn, ht, hknorm⟩ := NativePellBootstrap.first_norm_classification hQn hkn hnormN
  refine ⟨n, hn, ?_, ?_⟩
  · have hz := congrArg (fun z : ℕ => (z : ℤ)) ht
    simpa only [Int.natCast_natAbs] using hz
  · have hz := congrArg (fun z : ℕ => (z : ℤ)) hknorm
    simpa only [Nat.cast_mul, Nat.cast_ofNat, hkc] using hz

end DiophantineConsistency.NativeAdaptiveCarrierBootstrap
