import ExponentialIdentities.TwoBaseIntegerExponent.AlgebraicIntegerDeterminant
import ExponentialIdentities.TwoBaseIntegerExponent.AlgebraicOutputBridge
import ExponentialIdentities.TwoBaseIntegerExponent.RationalBaseThird
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Algebraic powers at positive rational auxiliary bases

Under integral powers at `2` and `3`, the six-exponentials determinant extends from
rational auxiliary outputs to arbitrary algebraic outputs.  For a nonintegral exponent,
the positive rational bases with algebraic `x`-th power are exactly the `2,3`-units.

The interpolation grid, denominator clearing, conjugate bounds, and determinant
bookkeeping are private.  The public API exposes the algebraic-output rigidity theorem
and its exact arithmetic classification consequences.
-/

open scoped NumberField

noncomputable section

namespace LeanProofs.TwoBaseIntegerExponent

variable {K : Type*} [Field K] [NumberField K]

private abbrev ARowBox (n : ℕ) :=
  Fin (n * n) × Fin (n * n) × Fin (n * n)

private abbrev AColBox (n : ℕ) :=
  Fin ((n * n) * n) × Fin ((n * n) * n)

private theorem card_aRowBox (n : ℕ) : Fintype.card (ARowBox n) = n ^ 6 := by
  simp [ARowBox]
  ring

private theorem card_aColBox (n : ℕ) : Fintype.card (AColBox n) = n ^ 6 := by
  simp [AColBox]
  ring

private def aRowRat (q : ℚ) {n : ℕ} (i : ARowBox n) : ℚ :=
  2 ^ (i.1 : ℕ) * 3 ^ (i.2.1 : ℕ) * q ^ (i.2.2 : ℕ)

private def aRowArg (q : ℚ) {n : ℕ} (i : ARowBox n) : ℝ :=
  Real.log (aRowRat q i : ℝ)

private def aColArg {n : ℕ} (x : ℝ) (j : AColBox n) : ℝ :=
  (j.1 : ℝ) + (j.2 : ℝ) * x

private theorem aRowRat_pos {q : ℚ} (hq : 0 < q)
    {n : ℕ} (i : ARowBox n) : 0 < aRowRat q i := by
  unfold aRowRat
  positivity

private theorem aRowRat_injective {q : ℚ} {n : ℕ}
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ (2 : ℚ) ^ u.1 * (3 : ℚ) ^ u.2.1 * q ^ u.2.2)) :
    Function.Injective (@aRowRat q n) := by
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
  have huv : ((i : ℕ), (j : ℕ), (k : ℕ)) =
      ((i' : ℕ), (j' : ℕ), (k' : ℕ)) := hmono h
  simp only [Prod.mk.injEq] at huv
  exact Prod.ext (Fin.ext huv.1) (Prod.ext (Fin.ext huv.2.1) (Fin.ext huv.2.2))

private theorem aRowArg_injective {q : ℚ} (hq : 0 < q)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ (2 : ℚ) ^ u.1 * (3 : ℚ) ^ u.2.1 * q ^ u.2.2))
    (n : ℕ) : Function.Injective (@aRowArg q n) := by
  intro i j h
  apply aRowRat_injective hmono
  have hcast : (aRowRat q i : ℝ) = (aRowRat q j : ℝ) :=
    Real.log_injOn_pos
      (show 0 < (aRowRat q i : ℝ) by exact_mod_cast aRowRat_pos hq i)
      (show 0 < (aRowRat q j : ℝ) by exact_mod_cast aRowRat_pos hq j) h
  exact Rat.cast_injective hcast

private theorem aColArg_injective {x : ℝ} (hx : Irrational x) (n : ℕ) :
    Function.Injective (@aColArg n x) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have huv : ((i : ℕ), (j : ℕ)) = ((i' : ℕ), (j' : ℕ)) :=
    LeanProofs.IntegerExponent.Irrational.injective_nat_add_mul hx h
  simp only [Prod.mk.injEq] at huv
  exact Prod.ext (Fin.ext huv.1) (Fin.ext huv.2)

private theorem aRowArg_eq {q : ℚ} (hq : 0 < q)
    {n : ℕ} (i : ARowBox n) :
    aRowArg q i =
      ((i.1 : ℕ) : ℝ) * Real.log 2 +
      ((i.2.1 : ℕ) : ℝ) * Real.log 3 +
      ((i.2.2 : ℕ) : ℝ) * Real.log (q : ℝ) := by
  simp only [aRowArg, aRowRat, Rat.cast_mul, Rat.cast_pow]
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow]
  norm_num

private theorem abs_aRowArg_le {q : ℚ} (hq : 0 < q)
    {n : ℕ} (i : ARowBox n) :
    |aRowArg q i| ≤
      (n * n : ℕ) * (|Real.log 2| + |Real.log 3| + |Real.log (q : ℝ)|) := by
  have hu2 : ((i.1 : ℕ) : ℝ) ≤ (n * n : ℕ) := by exact_mod_cast i.1.isLt.le
  have hu3 : ((i.2.1 : ℕ) : ℝ) ≤ (n * n : ℕ) := by
    exact_mod_cast i.2.1.isLt.le
  have huq : ((i.2.2 : ℕ) : ℝ) ≤ (n * n : ℕ) := by
    exact_mod_cast i.2.2.isLt.le
  have habs2 : |((i.1 : ℕ) : ℝ)| = ((i.1 : ℕ) : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg _)
  have habs3 : |((i.2.1 : ℕ) : ℝ)| = ((i.2.1 : ℕ) : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg _)
  have habsq : |((i.2.2 : ℕ) : ℝ)| = ((i.2.2 : ℕ) : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg _)
  rw [aRowArg_eq hq]
  calc
    |((i.1 : ℕ) : ℝ) * Real.log 2 +
        ((i.2.1 : ℕ) : ℝ) * Real.log 3 +
        ((i.2.2 : ℕ) : ℝ) * Real.log (q : ℝ)| ≤
      |((i.1 : ℕ) : ℝ) * Real.log 2| +
        |((i.2.1 : ℕ) : ℝ) * Real.log 3| +
        |((i.2.2 : ℕ) : ℝ) * Real.log (q : ℝ)| := by
      exact (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ = ((i.1 : ℕ) : ℝ) * |Real.log 2| +
        ((i.2.1 : ℕ) : ℝ) * |Real.log 3| +
        ((i.2.2 : ℕ) : ℝ) * |Real.log (q : ℝ)| := by
      rw [abs_mul, abs_mul, abs_mul, habs2, habs3, habsq]
    _ ≤ ((n * n : ℕ) : ℝ) * |Real.log 2| +
        ((n * n : ℕ) : ℝ) * |Real.log 3| +
        ((n * n : ℕ) : ℝ) * |Real.log (q : ℝ)| := by gcongr
    _ = (n * n : ℕ) *
        (|Real.log 2| + |Real.log 3| + |Real.log (q : ℝ)|) := by ring

private theorem abs_aColArg_le {n : ℕ} {x : ℝ} (j : AColBox n) :
    |aColArg x j| ≤ ((n * n) * n : ℕ) * (1 + |x|) := by
  have hv0 : ((j.1 : ℕ) : ℝ) ≤ ((n * n) * n : ℕ) := by
    exact_mod_cast j.1.isLt.le
  have hv1 : ((j.2 : ℕ) : ℝ) ≤ ((n * n) * n : ℕ) := by
    exact_mod_cast j.2.isLt.le
  have habs0 : |((j.1 : ℕ) : ℝ)| = ((j.1 : ℕ) : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg _)
  have habs1 : |((j.2 : ℕ) : ℝ)| = ((j.2 : ℕ) : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg _)
  dsimp only [aColArg]
  calc
    |(j.1 : ℝ) + (j.2 : ℝ) * x| ≤ |(j.1 : ℝ)| + |(j.2 : ℝ) * x| := abs_add_le _ _
    _ = (j.1 : ℝ) + (j.2 : ℝ) * |x| := by rw [abs_mul, habs0, habs1]
    _ ≤ (((n * n) * n : ℕ) : ℝ) + (((n * n) * n : ℕ) : ℝ) * |x| := by gcongr
    _ = ((n * n) * n : ℕ) * (1 + |x|) := by ring

private theorem abs_aRowArg_mul_aColArg_le {q : ℚ} (hq : 0 < q)
    {n D : ℕ} {x : ℝ}
    (hD : (|Real.log 2| + |Real.log 3| + |Real.log (q : ℝ)|) *
      (1 + |x|) ≤ D)
    (i : ARowBox n) (j : AColBox n) :
    |aRowArg q i * aColArg x j| ≤ (D * n ^ 5 : ℕ) := by
  rw [abs_mul]
  calc
    |aRowArg q i| * |aColArg x j| ≤
        (((n * n : ℕ) : ℝ) *
          (|Real.log 2| + |Real.log 3| + |Real.log (q : ℝ)|)) *
        (((n * n) * n : ℕ) * (1 + |x|)) :=
      mul_le_mul (abs_aRowArg_le hq i) (abs_aColArg_le j)
        (abs_nonneg _) (by positivity)
    _ = ((n ^ 5 : ℕ) : ℝ) *
        ((|Real.log 2| + |Real.log 3| + |Real.log (q : ℝ)|) * (1 + |x|)) := by
      push_cast
      ring
    _ ≤ ((n ^ 5 : ℕ) : ℝ) * D :=
      mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg _)
    _ = (D * n ^ 5 : ℕ) := by
      push_cast
      ring

private theorem coordinate_mul_le {n : ℕ}
    (u : Fin (n * n)) (v : Fin ((n * n) * n)) :
    (u : ℕ) * (v : ℕ) ≤ n ^ 5 := by
  calc
    (u : ℕ) * (v : ℕ) ≤ (n * n) * ((n * n) * n) :=
      Nat.mul_le_mul u.isLt.le v.isLt.le
    _ = n ^ 5 := by ring

/-- The algebraic form of one rational-base grid entry after expanding the exponential. -/
private def rawEntry (q : ℚ) (alpha : K) (M2 M3 : ℤ)
    (u2 u3 uq v0 v1 : ℕ) : K :=
  (2 : K) ^ (u2 * v0) *
    (3 : K) ^ (u3 * v0) *
    (q : K) ^ (uq * v0) *
    (M2 : K) ^ (u2 * v1) *
    (M3 : K) ^ (u3 * v1) *
    alpha ^ (uq * v1)

private theorem exp_log_mul_nat_add_eq {R : ℚ} (hR : 0 < R)
    {x : ℝ} (v0 v1 : ℕ) :
    Real.exp (Real.log (R : ℝ) * ((v0 : ℝ) + (v1 : ℝ) * x)) =
      (R : ℝ) ^ v0 * ((R : ℝ) ^ x) ^ v1 := by
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  rw [← Real.rpow_def_of_pos hRR]
  rw [Real.rpow_add hRR, Real.rpow_natCast]
  rw [show (v1 : ℝ) * x = x * (v1 : ℝ) by ring]
  rw [Real.rpow_mul_natCast hRR.le]

private theorem aRow_rpow_eq {q : ℚ} (hq : 0 < q)
    {x : ℝ} {M2 M3 : ℤ}
    (h2 : (M2 : ℝ) = (2 : ℝ) ^ x)
    (h3 : (M3 : ℝ) = (3 : ℝ) ^ x)
    {n : ℕ} (i : ARowBox n) :
    ((aRowRat q i : ℚ) : ℝ) ^ x =
      (M2 : ℝ) ^ (i.1 : ℕ) * (M3 : ℝ) ^ (i.2.1 : ℕ) *
        ((q : ℝ) ^ x) ^ (i.2.2 : ℕ) := by
  simp only [aRowRat, Rat.cast_mul, Rat.cast_pow]
  norm_num only [Rat.cast_ofNat]
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity)]
  rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) x (i.1 : ℕ),
    ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3) x (i.2.1 : ℕ),
    ← Real.rpow_pow_comm (by exact_mod_cast hq.le) x (i.2.2 : ℕ)]
  rw [← h2, ← h3]

private theorem exp_aRowArg_mul_aColArg_real {q : ℚ} (hq : 0 < q)
    {x : ℝ} {M2 M3 : ℤ}
    (h2 : (M2 : ℝ) = (2 : ℝ) ^ x)
    (h3 : (M3 : ℝ) = (3 : ℝ) ^ x)
    {n : ℕ} (i : ARowBox n) (j : AColBox n) :
    Real.exp (aRowArg q i * aColArg x j) =
      (2 : ℝ) ^ ((i.1 : ℕ) * (j.1 : ℕ)) *
      (3 : ℝ) ^ ((i.2.1 : ℕ) * (j.1 : ℕ)) *
      (q : ℝ) ^ ((i.2.2 : ℕ) * (j.1 : ℕ)) *
      (M2 : ℝ) ^ ((i.1 : ℕ) * (j.2 : ℕ)) *
      (M3 : ℝ) ^ ((i.2.1 : ℕ) * (j.2 : ℕ)) *
      ((q : ℝ) ^ x) ^ ((i.2.2 : ℕ) * (j.2 : ℕ)) := by
  rw [aRowArg, aColArg, exp_log_mul_nat_add_eq (aRowRat_pos hq i)]
  rw [aRow_rpow_eq hq h2 h3 i]
  simp only [aRowRat, Rat.cast_mul, Rat.cast_pow, mul_pow, ← pow_mul]
  ring

private theorem map_rawEntry_eq_exp
    (q : ℚ) (alpha : K) (sigma : K →+* ℂ) (M2 M3 : ℤ)
    {x : ℝ} (hq : 0 < q)
    (h2 : (M2 : ℝ) = (2 : ℝ) ^ x)
    (h3 : (M3 : ℝ) = (3 : ℝ) ^ x)
    (halpha : sigma alpha = (((q : ℝ) ^ x : ℝ) : ℂ))
    {n : ℕ} (i : ARowBox n) (j : AColBox n) :
    sigma (rawEntry q alpha M2 M3
      (i.1 : ℕ) (i.2.1 : ℕ) (i.2.2 : ℕ) (j.1 : ℕ) (j.2 : ℕ)) =
      (Real.exp (aRowArg q i * aColArg x j) : ℂ) := by
  rw [exp_aRowArg_mul_aColArg_real hq h2 h3]
  simp only [rawEntry, map_mul, map_pow, map_ofNat, map_intCast, halpha]
  have hqmap : sigma (q : K) = (q : ℂ) := by
    exact map_ratCast sigma q
  rw [hqmap]
  push_cast
  ring

/-- A rational power becomes integral after multiplying by a sufficiently large
power of its reduced denominator. -/
private theorem isIntegral_den_pow_mul_rat_pow (q : ℚ) {e L : ℕ} (hle : e ≤ L) :
    IsIntegral ℤ ((q.den : K) ^ L * (q : K) ^ e) := by
  let z : ℤ := q.num ^ e * (q.den : ℤ) ^ (L - e)
  have hz : (z : K) = (q.den : K) ^ L * (q : K) ^ e := by
    dsimp only [z]
    rw [Rat.cast_def]
    push_cast
    rw [div_pow, show L = e + (L - e) by omega, pow_add]
    have hden : (q.den : K) ≠ 0 := by exact_mod_cast q.den_nz
    field_simp
    rw [Nat.add_sub_cancel_left]
  rw [← hz]
  exact isIntegral_intCast z

/-- If `m • alpha` is an algebraic integer, then `m^L * alpha^e` is integral
for every `e ≤ L`. -/
private theorem isIntegral_nat_pow_mul_pow_of_nsmul
    {alpha : K} {m e L : ℕ} {z : NumberField.RingOfIntegers K}
    (hle : e ≤ L) (hz : m • alpha = (z : K)) :
    IsIntegral ℤ ((m : K) ^ L * alpha ^ e) := by
  have hmul : (m : K) * alpha = (z : K) := by
    simpa [nsmul_eq_mul] using hz
  have heq : (m : K) ^ L * alpha ^ e =
      (z : K) ^ e * (m : K) ^ (L - e) := by
    rw [show L = e + (L - e) by omega, pow_add]
    rw [mul_assoc, mul_comm ((m : K) ^ (L - e)), ← mul_assoc]
    rw [← mul_pow, hmul]
    rw [Nat.add_sub_cancel_left]
  rw [heq]
  exact z.property.pow e |>.mul ((isIntegral_natCast (B := K) m).pow (L - e))

/-- A common factor `(q.den * m)^L` clears one expanded entry.  This is the
entry-level algebraic-integer replacement for the rational denominator lemma. -/
private theorem isIntegral_common_scale_mul_rawEntry
    (q : ℚ) (alpha : K) (M2 M3 : ℤ) (m L u2 u3 uq v0 v1 : ℕ)
    {z : NumberField.RingOfIntegers K}
    (hq0 : uq * v0 ≤ L) (ha0 : uq * v1 ≤ L)
    (hz : m • alpha = (z : K)) :
    IsIntegral ℤ
      (((q.den * m : ℕ) : K) ^ L *
        rawEntry q alpha M2 M3 u2 u3 uq v0 v1) := by
  have hq : IsIntegral ℤ ((q.den : K) ^ L * (q : K) ^ (uq * v0)) :=
    isIntegral_den_pow_mul_rat_pow q hq0
  have ha : IsIntegral ℤ ((m : K) ^ L * alpha ^ (uq * v1)) :=
    isIntegral_nat_pow_mul_pow_of_nsmul ha0 hz
  have h2 : IsIntegral ℤ ((2 : K) ^ (u2 * v0)) :=
    (isIntegral_natCast (B := K) 2).pow _
  have h3 : IsIntegral ℤ ((3 : K) ^ (u3 * v0)) :=
    (isIntegral_natCast (B := K) 3).pow _
  have hM2 : IsIntegral ℤ ((M2 : K) ^ (u2 * v1)) :=
    (isIntegral_intCast (B := K) M2).pow _
  have hM3 : IsIntegral ℤ ((M3 : K) ^ (u3 * v1)) :=
    (isIntegral_intCast (B := K) M3).pow _
  have heq :
      (((q.den * m : ℕ) : K) ^ L *
          rawEntry q alpha M2 M3 u2 u3 uq v0 v1) =
        (2 : K) ^ (u2 * v0) *
          ((3 : K) ^ (u3 * v0) *
            (((q.den : K) ^ L * (q : K) ^ (uq * v0)) *
              ((M2 : K) ^ (u2 * v1) *
                ((M3 : K) ^ (u3 * v1) *
                  ((m : K) ^ L * alpha ^ (uq * v1)))))) := by
    simp only [rawEntry, Nat.cast_mul, mul_pow]
    ring
  rw [heq]
  exact h2.mul (h3.mul (hq.mul (hM2.mul (hM3.mul ha))))

/-- Two complementary powers of quantities bounded by `T` are bounded by `T^L`. -/
private theorem norm_pow_mul_complementary_pow_le
    {a b : ℂ} {T : ℝ} {e L : ℕ} (hT : 1 ≤ T)
    (ha : ‖a‖ ≤ T) (hb : ‖b‖ ≤ T) (he : e ≤ L) :
    ‖a ^ e * b ^ (L - e)‖ ≤ T ^ L := by
  rw [norm_mul, norm_pow, norm_pow]
  calc
    ‖a‖ ^ e * ‖b‖ ^ (L - e) ≤ T ^ e * T ^ (L - e) := by
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ha _)
        (pow_le_pow_left₀ (norm_nonneg _) hb _) (pow_nonneg (norm_nonneg _) _)
        (pow_nonneg (le_trans (norm_nonneg _) hb) _)
    _ = T ^ (e + (L - e)) := (pow_add T e (L - e)).symm
    _ = T ^ L := by rw [Nat.add_sub_of_le he]

/-- One power with exponent at most `L` is bounded by `T^L` when `T ≥ 1`. -/
private theorem norm_pow_le_uniform_pow
    {a : ℂ} {T : ℝ} {e L : ℕ} (hT : 1 ≤ T)
    (ha : ‖a‖ ≤ T) (he : e ≤ L) :
    ‖a ^ e‖ ≤ T ^ L := by
  rw [norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _) ha e).trans (pow_le_pow_right₀ hT he)

/-- Six-factor norm bound kept abstract so chosen grouped factors are not expanded. -/
private theorem norm_embedding_six_mul_le (tau : K →+* ℂ)
    (a b c d e f : K) {U : ℝ} (hU : 0 ≤ U)
    (ha : ‖tau a‖ ≤ U) (hb : ‖tau b‖ ≤ U) (hc : ‖tau c‖ ≤ U)
    (hd : ‖tau d‖ ≤ U) (he : ‖tau e‖ ≤ U) (hf : ‖tau f‖ ≤ U) :
    ‖tau (a * (b * (c * (d * (e * f)))))‖ ≤ U ^ 6 := by
  simp only [map_mul, norm_mul]
  calc
    ‖tau a‖ * (‖tau b‖ * (‖tau c‖ * (‖tau d‖ * (‖tau e‖ * ‖tau f‖)))) ≤
        U * (U * (U * (U * (U * U)))) := by gcongr
    _ = U ^ 6 := by ring

/-- Exact six-group conjugate bound for a cleared rational-base grid entry.

The groups are `2`, `3`, the denominator-cleared rational base, the two integral
outputs, and the denominator-cleared algebraic output. -/
private theorem norm_embedding_common_scale_mul_rawEntry_le
    (q : ℚ) (alpha : K) (M2 M3 : ℤ) (m L u2 u3 uq v0 v1 : ℕ)
    {z : NumberField.RingOfIntegers K} (tau : K →+* ℂ) {T : ℝ}
    (hT : 1 ≤ T)
    (h2T : ‖(2 : ℂ)‖ ≤ T) (h3T : ‖(3 : ℂ)‖ ≤ T)
    (hqnumT : ‖(q.num : ℂ)‖ ≤ T) (hqdenT : ‖(q.den : ℂ)‖ ≤ T)
    (hM2T : ‖(M2 : ℂ)‖ ≤ T) (hM3T : ‖(M3 : ℂ)‖ ≤ T)
    (hmT : ‖(m : ℂ)‖ ≤ T) (hzT : ‖tau (z : K)‖ ≤ T)
    (h2e : u2 * v0 ≤ L) (h3e : u3 * v0 ≤ L)
    (hqe : uq * v0 ≤ L) (hM2e : u2 * v1 ≤ L)
    (hM3e : u3 * v1 ≤ L) (hae : uq * v1 ≤ L)
    (hz : m • alpha = (z : K)) :
    ‖tau ((((q.den * m : ℕ) : K) ^ L *
        rawEntry q alpha M2 M3 u2 u3 uq v0 v1))‖ ≤ T ^ (6 * L) := by
  have hqEq : (q.den : K) ^ L * (q : K) ^ (uq * v0) =
      (q.num : K) ^ (uq * v0) * (q.den : K) ^ (L - uq * v0) := by
    rw [Rat.cast_def, div_pow, show L = uq * v0 + (L - uq * v0) by omega, pow_add]
    have hden : (q.den : K) ≠ 0 := by exact_mod_cast q.den_nz
    field_simp
    rw [Nat.add_sub_cancel_left]
    ring
  have hmul : (m : K) * alpha = (z : K) := by
    simpa [nsmul_eq_mul] using hz
  have haEq : (m : K) ^ L * alpha ^ (uq * v1) =
      (z : K) ^ (uq * v1) * (m : K) ^ (L - uq * v1) := by
    rw [show L = uq * v1 + (L - uq * v1) by omega, pow_add]
    rw [mul_assoc, mul_comm ((m : K) ^ (L - uq * v1)), ← mul_assoc]
    rw [← mul_pow, hmul, Nat.add_sub_cancel_left]
  have g2 : ‖(2 : ℂ) ^ (u2 * v0)‖ ≤ T ^ L :=
    norm_pow_le_uniform_pow hT h2T h2e
  have g3 : ‖(3 : ℂ) ^ (u3 * v0)‖ ≤ T ^ L :=
    norm_pow_le_uniform_pow hT h3T h3e
  have gq : ‖tau ((q.den : K) ^ L * (q : K) ^ (uq * v0))‖ ≤ T ^ L := by
    rw [hqEq, map_mul, map_pow, map_pow]
    simpa only [map_intCast, map_natCast] using
      (norm_pow_mul_complementary_pow_le hT hqnumT hqdenT hqe)
  have gM2 : ‖(M2 : ℂ) ^ (u2 * v1)‖ ≤ T ^ L :=
    norm_pow_le_uniform_pow hT hM2T hM2e
  have gM3 : ‖(M3 : ℂ) ^ (u3 * v1)‖ ≤ T ^ L :=
    norm_pow_le_uniform_pow hT hM3T hM3e
  have ga : ‖tau ((m : K) ^ L * alpha ^ (uq * v1))‖ ≤ T ^ L := by
    rw [haEq, map_mul, map_pow, map_pow]
    simpa only [map_natCast] using
      (norm_pow_mul_complementary_pow_le hT hzT hmT hae)
  have hentry :
      (((q.den * m : ℕ) : K) ^ L *
          rawEntry q alpha M2 M3 u2 u3 uq v0 v1) =
        (2 : K) ^ (u2 * v0) *
          ((3 : K) ^ (u3 * v0) *
            (((q.den : K) ^ L * (q : K) ^ (uq * v0)) *
              ((M2 : K) ^ (u2 * v1) *
                ((M3 : K) ^ (u3 * v1) *
                  ((m : K) ^ L * alpha ^ (uq * v1)))))) := by
    simp only [rawEntry, Nat.cast_mul, mul_pow]
    ring
  rw [hentry]
  have htau2 : tau (2 : K) = (2 : ℂ) := by
    exact map_ofNat tau 2
  have htau3 : tau (3 : K) = (3 : ℂ) := by
    exact map_ofNat tau 3
  have g2' : ‖tau ((2 : K) ^ (u2 * v0))‖ ≤ T ^ L := by
    simpa only [map_pow, htau2] using g2
  have g3' : ‖tau ((3 : K) ^ (u3 * v0))‖ ≤ T ^ L := by
    simpa only [map_pow, htau3] using g3
  have gM2' : ‖tau ((M2 : K) ^ (u2 * v1))‖ ≤ T ^ L := by
    simpa only [map_pow, map_intCast] using gM2
  have gM3' : ‖tau ((M3 : K) ^ (u3 * v1))‖ ≤ T ^ L := by
    simpa only [map_pow, map_intCast] using gM3
  calc
    _ ≤ (T ^ L) ^ 6 :=
      norm_embedding_six_mul_le tau _ _ _ _ _ _ (pow_nonneg (by linarith) _)
        g2' g3' gq gM2' gM3' ga
    _ = T ^ (6 * L) := by rw [← pow_mul]; congr 1; ring

private def clearedEntry
    (q : ℚ) (alpha : K) (M2 M3 : ℤ) (m L u2 u3 uq v0 v1 : ℕ)
    (hq0 : uq * v0 ≤ L) (ha0 : uq * v1 ≤ L)
    (z : NumberField.RingOfIntegers K)
    (hz : m • alpha = (z : K)) : NumberField.RingOfIntegers K :=
  ⟨((q.den * m : ℕ) : K) ^ L * rawEntry q alpha M2 M3 u2 u3 uq v0 v1,
    isIntegral_common_scale_mul_rawEntry q alpha M2 M3 m L u2 u3 uq v0 v1
      hq0 ha0 hz⟩

private theorem map_clearedEntry_eq_scale_exp
    (q : ℚ) (alpha : K) (sigma : K →+* ℂ) (M2 M3 : ℤ)
    {x : ℝ} (hq : 0 < q)
    (h2 : (M2 : ℝ) = (2 : ℝ) ^ x)
    (h3 : (M3 : ℝ) = (3 : ℝ) ^ x)
    (halpha : sigma alpha = (((q : ℝ) ^ x : ℝ) : ℂ))
    {n m : ℕ} (i : ARowBox n) (j : AColBox n)
    (h0 : (i.2.2 : ℕ) * (j.1 : ℕ) ≤ n ^ 5)
    (h1 : (i.2.2 : ℕ) * (j.2 : ℕ) ≤ n ^ 5)
    (z : NumberField.RingOfIntegers K) (hz : m • alpha = (z : K)) :
    sigma ((clearedEntry q alpha M2 M3 m (n ^ 5)
      (i.1 : ℕ) (i.2.1 : ℕ) (i.2.2 : ℕ) (j.1 : ℕ) (j.2 : ℕ)
      h0 h1 z hz : NumberField.RingOfIntegers K) : K) =
      ((q.den * m : ℕ) : ℂ) ^ (n ^ 5) *
        (Real.exp (aRowArg q i * aColArg x j) : ℂ) := by
  change sigma ((((q.den * m : ℕ) : K) ^ (n ^ 5)) *
      rawEntry q alpha M2 M3 (i.1 : ℕ) (i.2.1 : ℕ) (i.2.2 : ℕ)
        (j.1 : ℕ) (j.2 : ℕ)) = _
  rw [map_mul, map_pow, map_natCast,
    map_rawEntry_eq_exp q alpha sigma M2 M3 hq h2 h3 halpha i j]

private theorem real_det_loss_eq (n T degree : ℕ) :
    ((n ^ 6).factorial • ((((T : ℝ) ^ (6 * n ^ 5)) ^ (n ^ 6))) : ℝ) ^
        (degree - 1) =
      ((((n ^ 6).factorial * T ^ (6 * n ^ 11)) ^ (degree - 1) : ℕ) : ℝ) := by
  simp only [nsmul_eq_mul]
  push_cast
  rw [← pow_mul]
  congr 2
  · congr 1
    ring

/-- The rational clearing factor and the full conjugate/degree loss combine into
one base raised to `n^11`, exactly matching the existing numerical margin API. -/
private theorem combined_algebraic_loss_le_uniform_power
    (n T degree B : ℕ) (hn : 2 ≤ n) :
    B ^ (n ^ 11) *
        (((n ^ 6).factorial * T ^ (6 * n ^ 11)) ^ (degree - 1)) ≤
      (B * (2 * T ^ 6) ^ (degree - 1)) ^ (n ^ 11) := by
  have hloss := LeanProofs.IntegerExponent.algebraic_det_loss_le_uniform_power
    n T degree hn
  calc
    B ^ (n ^ 11) *
          (((n ^ 6).factorial * T ^ (6 * n ^ 11)) ^ (degree - 1)) ≤
        B ^ (n ^ 11) * ((2 * T ^ 6) ^ (degree - 1)) ^ (n ^ 11) :=
      Nat.mul_le_mul_left _ hloss
    _ = (B * (2 * T ^ 6) ^ (degree - 1)) ^ (n ^ 11) := by
      exact (mul_pow B ((2 * T ^ 6) ^ (degree - 1)) (n ^ 11)).symm

/-- Glue from a scaled matrix over `𝓞 K` to the selected complex analytic matrix.
This is the direct entry point to `AlgebraicIntegerDeterminant`. -/
private theorem one_div_entry_bound_le_scaled_norm_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Z : Matrix ι ι (NumberField.RingOfIntegers K)) (hdet : Z.det ≠ 0)
    (A : Matrix ι ι ℂ) (sigma : K →+* ℂ) (Q : ℕ) {E : ℝ}
    (hmap : ∀ i j, sigma (Z i j : K) = (Q : ℂ) * A i j)
    (hentry : ∀ (tau : K →+* ℂ) i j, ‖tau (Z i j : K)‖ ≤ E) :
    1 / ((Fintype.card ι).factorial • E ^ Fintype.card ι) ^
          (Module.finrank ℚ K - 1) ≤
      (Q : ℝ) ^ Fintype.card ι * ‖A.det‖ := by
  have hlower := LeanProofs.IntegerExponent.one_div_conjugate_entry_bound_le_norm_det
    Z hdet sigma hentry
  have hmatrix : (fun i j ↦ sigma (Z i j : K)) = (Q : ℂ) • A := by
    ext i j
    simpa only [Matrix.smul_apply, smul_eq_mul] using hmap i j
  rw [hmatrix, Matrix.det_smul, norm_mul, norm_pow] at hlower
  simpa using hlower

set_option maxHeartbeats 3000000 in
private theorem not_irrational_of_two_three_q_rpow_scaledAlgebraicInteger_of_monomial_injective
    {q : ℚ} (hq : 0 < q)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦
        (2 : ℚ) ^ u.1 * (3 : ℚ) ^ u.2.1 * q ^ u.2.2))
    {x : ℝ}
    (hTwo : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (hThree : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (alpha : K) (scale : ℕ) (hscale : 0 < scale)
    (zalpha : NumberField.RingOfIntegers K)
    (hclear : scale • alpha = (zalpha : K))
    (sigma : K →+* ℂ)
    (hqPow : sigma alpha = (((q : ℝ) ^ x : ℝ) : ℂ)) :
    ¬ Irrational x := by
  classical
  intro hxirr
  obtain ⟨zTwo, hzTwo⟩ := hTwo
  obtain ⟨zThree, hzThree⟩ := hThree
  let kernelScale : ℝ :=
    (|Real.log 2| + |Real.log 3| + |Real.log (q : ℝ)|) * (1 + |x|)
  obtain ⟨D, hD⟩ := exists_nat_ge kernelScale

  let conjugateScale : ℝ :=
    2 + 3 + |(q.num : ℝ)| + (q.den : ℝ) + |(zTwo : ℝ)| +
      |(zThree : ℝ)| + (scale : ℝ) + NumberField.house (zalpha : K)
  obtain ⟨T, hT⟩ := exists_nat_ge conjugateScale
  have hqnumNonneg : 0 ≤ |(q.num : ℝ)| := abs_nonneg _
  have hqdenNonneg : 0 ≤ (q.den : ℝ) := Nat.cast_nonneg _
  have hzTwoNonneg : 0 ≤ |(zTwo : ℝ)| := abs_nonneg _
  have hzThreeNonneg : 0 ≤ |(zThree : ℝ)| := abs_nonneg _
  have hscaleNonneg : 0 ≤ (scale : ℝ) := Nat.cast_nonneg _
  have hhouseNonneg : 0 ≤ NumberField.house (zalpha : K) :=
    NumberField.house_nonneg _
  have hTTwo : (2 : ℝ) ≤ T := by
    dsimp only [conjugateScale] at hT
    nlinarith
  have hTThree : (3 : ℝ) ≤ T := by
    dsimp only [conjugateScale] at hT
    nlinarith
  have hTqnum : |(q.num : ℝ)| ≤ T := by
    dsimp only [conjugateScale] at hT
    nlinarith
  have hTqden : (q.den : ℝ) ≤ T := by
    dsimp only [conjugateScale] at hT
    nlinarith
  have hTzTwo : |(zTwo : ℝ)| ≤ T := by
    dsimp only [conjugateScale] at hT
    nlinarith
  have hTzThree : |(zThree : ℝ)| ≤ T := by
    dsimp only [conjugateScale] at hT
    nlinarith
  have hTscale : (scale : ℝ) ≤ T := by
    dsimp only [conjugateScale] at hT
    nlinarith
  have hTalpha : NumberField.house (zalpha : K) ≤ T := by
    dsimp only [conjugateScale] at hT
    nlinarith
  have hTOne : (1 : ℝ) ≤ T := le_trans (by norm_num) hTTwo

  let B : ℕ := q.den * scale
  have hBpos : 0 < B := by
    dsimp only [B]
    exact Nat.mul_pos q.den_pos hscale
  let degree : ℕ := Module.finrank ℚ K
  let b : ℕ := B * (2 * T ^ 6) ^ (degree - 1)
  let N : ℕ := 192 * D + 2 * b + 3
  let n : ℕ := 2 * N
  let m : ℕ := n ^ 6
  let r : ℕ := 32 * N ^ 6
  let C : ℕ := D * n ^ 5
  let s : ℕ := n ^ 11
  let E : ℝ := (T : ℝ) ^ (6 * n ^ 5)
  let Q : ℕ := B ^ (n ^ 5)

  have hDN : 192 * D ≤ N := by
    dsimp only [N]
    omega
  have hNpos : 0 < N := by
    dsimp only [N]
    omega
  have hnTwo : 2 ≤ n := by
    dsimp only [n]
    omega
  have hm : m = 2 * r := by
    dsimp only [m, r, n]
    ring
  have hr : 2 < r := by
    have hpow : 0 < N ^ 6 := pow_pos hNpos _
    dsimp only [r]
    omega
  have hCr : 192 * C ≤ r := by
    calc
      192 * C = (192 * D) * (32 * N ^ 5) := by
        dsimp only [C, n]
        ring
      _ ≤ N * (32 * N ^ 5) := Nat.mul_le_mul_right _ hDN
      _ = r := by
        dsimp only [r]
        ring
  have hmargin : b * s + 2 * r < r * r := by
    have hbN : 32 * b + 1 < 16 * N := by
      dsimp only [N]
      omega
    have hN5pos : 0 < N ^ 5 := pow_pos hNpos _
    have hstep : 32 * b * N ^ 5 + 1 < 16 * N * N ^ 5 := by
      calc
        32 * b * N ^ 5 + 1 ≤ (32 * b + 1) * N ^ 5 := by nlinarith
        _ < (16 * N) * N ^ 5 := Nat.mul_lt_mul_of_pos_right hbN hN5pos
        _ = 16 * N * N ^ 5 := rfl
    have hpositive : 0 < 64 * N ^ 6 := by positivity
    have hscaled := Nat.mul_lt_mul_of_pos_right hstep hpositive
    change b * (2 * N) ^ 11 + 2 * (32 * N ^ 6) <
      (32 * N ^ 6) * (32 * N ^ 6)
    calc
      b * (2 * N) ^ 11 + 2 * (32 * N ^ 6) =
          (32 * b * N ^ 5 + 1) * (64 * N ^ 6) := by ring
      _ < (16 * N * N ^ 5) * (64 * N ^ 6) := hscaled
      _ = (32 * N ^ 6) * (32 * N ^ 6) := by ring
  have hrm : r ≤ m := by omega
  obtain ⟨hsmall, hnumeric⟩ :=
    LeanProofs.IntegerExponent.exponential_det_numeric_bound_with_denominator
      C m r b s hm hr hCr hmargin

  have hrowcard : Fintype.card (ARowBox n) = m := by rw [card_aRowBox]
  have hcolcard : Fintype.card (AColBox n) = m := by rw [card_aColBox]
  let erow : Fin m ≃ ARowBox n := (Fintype.equivFinOfCardEq hrowcard).symm
  let ecol : Fin m ≃ AColBox n := (Fintype.equivFinOfCardEq hcolcard).symm
  let row : Fin m → ℝ := fun i ↦ aRowArg q (erow i)
  let col : Fin m → ℝ := fun j ↦ aColArg x (ecol j)
  let A : Matrix (Fin m) (Fin m) ℝ := fun i j ↦ Real.exp (row i * col j)
  let AO : Matrix (Fin m) (Fin m) (NumberField.RingOfIntegers K) := fun i j ↦
    clearedEntry q alpha zTwo zThree scale (n ^ 5)
      ((erow i).1 : ℕ) ((erow i).2.1 : ℕ) ((erow i).2.2 : ℕ)
      ((ecol j).1 : ℕ) ((ecol j).2 : ℕ)
      (coordinate_mul_le (erow i).2.2 (ecol j).1)
      (coordinate_mul_le (erow i).2.2 (ecol j).2) zalpha hclear

  have hrow : Function.Injective row :=
    (aRowArg_injective hq hmono n).comp erow.injective
  have hcol : Function.Injective col :=
    (aColArg_injective hxirr n).comp ecol.injective
  have hAne : A.det ≠ 0 :=
    LeanProofs.IntegerExponent.det_exp_mul_ne_zero_of_injective row col hrow hcol
  have hentryMap : ∀ i j,
      sigma ((AO i j : NumberField.RingOfIntegers K) : K) =
        (Q : ℂ) * (A i j : ℂ) := by
    intro i j
    simpa only [AO, Q, B, A, row, col, Nat.cast_pow, Nat.cast_mul] using
      (map_clearedEntry_eq_scale_exp q alpha sigma zTwo zThree hq hzTwo hzThree
        hqPow (erow i) (ecol j)
        (coordinate_mul_le (erow i).2.2 (ecol j).1)
        (coordinate_mul_le (erow i).2.2 (ecol j).2) zalpha hclear)
  let f : NumberField.RingOfIntegers K →+* ℂ :=
    sigma.comp (algebraMap (NumberField.RingOfIntegers K) K)
  have hmatrixMap : f.mapMatrix AO = (Q : ℂ) • A.map Complex.ofReal := by
    ext i j
    change sigma ((AO i j : NumberField.RingOfIntegers K) : K) =
      (Q : ℂ) * (A i j : ℂ)
    simpa only [Matrix.smul_apply, smul_eq_mul] using hentryMap i j
  have hdetOfReal : Matrix.det (A.map Complex.ofReal) = (A.det : ℂ) := by
    have hmatrix : Complex.ofRealHom.mapMatrix A = A.map Complex.ofReal := by
      ext i j
      rfl
    calc
      Matrix.det (A.map Complex.ofReal) =
          Matrix.det (Complex.ofRealHom.mapMatrix A) := by rw [hmatrix]
      _ = Complex.ofRealHom A.det := (Complex.ofRealHom.map_det A).symm
      _ = (A.det : ℂ) := rfl
  have hdetMap : f AO.det = (Q : ℂ) ^ m * (A.det : ℂ) := by
    calc
      f AO.det = Matrix.det (f.mapMatrix AO) := f.map_det AO
      _ = Matrix.det ((Q : ℂ) • A.map Complex.ofReal) := by rw [hmatrixMap]
      _ = (Q : ℂ) ^ m * Matrix.det (A.map Complex.ofReal) := by
        rw [Matrix.det_smul, Fintype.card_fin]
      _ = (Q : ℂ) ^ m * (A.det : ℂ) := by rw [hdetOfReal]
  have hAOdet : AO.det ≠ 0 := by
    intro hzero
    have hQne : (Q : ℂ) ≠ 0 := by
      exact_mod_cast (pow_ne_zero (n ^ 5) (Nat.ne_of_gt hBpos))
    have hAdetC : (A.det : ℂ) ≠ 0 := by exact_mod_cast hAne
    have hprod : (Q : ℂ) ^ m * (A.det : ℂ) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hQne) hAdetC
    apply hprod
    rw [← hdetMap, hzero, map_zero]

  have hentryBound : ∀ (tau : K →+* ℂ) i j,
      ‖tau ((AO i j : NumberField.RingOfIntegers K) : K)‖ ≤ E := by
    intro tau i j
    have hztau : ‖tau (zalpha : K)‖ ≤ (T : ℝ) :=
      (NumberField.norm_embedding_le_house (zalpha : K) tau).trans hTalpha
    have h2norm : ‖(2 : ℂ)‖ ≤ (T : ℝ) := by
      calc
        ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
        _ ≤ (T : ℝ) := hTTwo
    have h3norm : ‖(3 : ℂ)‖ ≤ (T : ℝ) := by
      calc
        ‖(3 : ℂ)‖ = (3 : ℝ) := by norm_num
        _ ≤ (T : ℝ) := hTThree
    have hqnumNorm : ‖(q.num : ℂ)‖ ≤ (T : ℝ) := by
      rw [Complex.norm_intCast]
      exact hTqnum
    have hqdenNorm : ‖(q.den : ℂ)‖ ≤ (T : ℝ) := by
      rw [Complex.norm_natCast]
      exact hTqden
    have hzTwoNorm : ‖(zTwo : ℂ)‖ ≤ (T : ℝ) := by
      rw [Complex.norm_intCast]
      exact hTzTwo
    have hzThreeNorm : ‖(zThree : ℂ)‖ ≤ (T : ℝ) := by
      rw [Complex.norm_intCast]
      exact hTzThree
    have hscaleNorm : ‖(scale : ℂ)‖ ≤ (T : ℝ) := by
      rw [Complex.norm_natCast]
      exact hTscale
    change ‖tau ((((q.den * scale : ℕ) : K) ^ (n ^ 5)) *
      rawEntry q alpha zTwo zThree ((erow i).1 : ℕ) ((erow i).2.1 : ℕ)
        ((erow i).2.2 : ℕ) ((ecol j).1 : ℕ) ((ecol j).2 : ℕ))‖ ≤ _
    simpa only [E] using
      (norm_embedding_common_scale_mul_rawEntry_le q alpha zTwo zThree scale
        (n ^ 5) ((erow i).1 : ℕ) ((erow i).2.1 : ℕ) ((erow i).2.2 : ℕ)
        ((ecol j).1 : ℕ) ((ecol j).2 : ℕ) tau hTOne h2norm h3norm
        hqnumNorm hqdenNorm hzTwoNorm hzThreeNorm hscaleNorm hztau
        (coordinate_mul_le (erow i).1 (ecol j).1)
        (coordinate_mul_le (erow i).2.1 (ecol j).1)
        (coordinate_mul_le (erow i).2.2 (ecol j).1)
        (coordinate_mul_le (erow i).1 (ecol j).2)
        (coordinate_mul_le (erow i).2.1 (ecol j).2)
        (coordinate_mul_le (erow i).2.2 (ecol j).2) hclear)
  have hlowerRaw :=
    one_div_entry_bound_le_scaled_norm_det AO hAOdet
      (A.map Complex.ofReal) sigma Q hentryMap hentryBound
  have hlower :
      1 / ((m.factorial • E ^ m : ℝ) ^ (degree - 1)) ≤
        (B : ℝ) ^ s * |A.det| := by
    have hpowExp : n ^ 5 * m = s := by
      dsimp only [m, s]
      ring
    have hQpow : (Q : ℝ) ^ m = (B : ℝ) ^ s := by
      calc
        (Q : ℝ) ^ m = ((B : ℝ) ^ (n ^ 5)) ^ m := by
          simp only [Q, Nat.cast_pow]
        _ = (B : ℝ) ^ (n ^ 5 * m) := by rw [pow_mul]
        _ = (B : ℝ) ^ s := by rw [hpowExp]
    have hselectedNorm : ‖Matrix.det (A.map Complex.ofReal)‖ = |A.det| := by
      rw [hdetOfReal, Complex.norm_real, Real.norm_eq_abs]
    simpa only [Fintype.card_fin, degree, hQpow, hselectedNorm] using hlowerRaw

  have hlossNat :
      B ^ s * ((n ^ 6).factorial * T ^ (6 * n ^ 11)) ^ (degree - 1) ≤ b ^ s := by
    simpa only [b, s] using
      (combined_algebraic_loss_le_uniform_power n T degree B hnTwo)
  have hdenEq :
      (m.factorial • E ^ m : ℝ) ^ (degree - 1) =
        (((n ^ 6).factorial * T ^ (6 * n ^ 11)) ^ (degree - 1) : ℕ) := by
    simpa only [m, E] using real_det_loss_eq n T degree
  have hdenLe :
      (B : ℝ) ^ s * (m.factorial • E ^ m : ℝ) ^ (degree - 1) ≤
        (b : ℝ) ^ s := by
    rw [hdenEq]
    exact_mod_cast hlossNat
  have hdenPos : 0 < (m.factorial • E ^ m : ℝ) ^ (degree - 1) := by
    have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hTOne
    dsimp only [E]
    positivity
  have hkernel : ∀ i j, |row i * col j| ≤ (C : ℝ) := by
    intro i j
    change |aRowArg q (erow i) * aColArg x (ecol j)| ≤ (C : ℝ)
    simpa only [C] using
      (abs_aRowArg_mul_aColArg_le hq
        (by simpa only [kernelScale] using hD) (erow i) (ecol j))
  have hupper : |A.det| ≤
      (2 : ℝ) ^ m * (m.factorial : ℝ) * Real.exp (C : ℝ) ^ r *
        (Real.exp (C : ℝ) * (C : ℝ) ^ r / (r.factorial : ℝ)) ^ (m - r) := by
    change |Matrix.det (fun i j ↦ Real.exp (row i * col j))| ≤ _
    exact LeanProofs.IntegerExponent.abs_det_exp_mul_le hrm row col (C : ℝ)
      (Nat.cast_nonneg _) hkernel hsmall
  have hone_le : 1 ≤ (b : ℝ) ^ s * |A.det| := by
    have hone : 1 ≤
        (m.factorial • E ^ m : ℝ) ^ (degree - 1) *
          ((B : ℝ) ^ s * |A.det|) := by
      have h := (div_le_iff₀ hdenPos).mp hlower
      simpa [mul_comm] using h
    calc
      1 ≤ (m.factorial • E ^ m : ℝ) ^ (degree - 1) *
          ((B : ℝ) ^ s * |A.det|) := hone
      _ = ((B : ℝ) ^ s *
          (m.factorial • E ^ m : ℝ) ^ (degree - 1)) * |A.det| := by ring
      _ ≤ (b : ℝ) ^ s * |A.det| :=
        mul_le_mul_of_nonneg_right hdenLe (abs_nonneg _)
  have hscaledUpper : (b : ℝ) ^ s * |A.det| ≤
      (b : ℝ) ^ s *
        ((2 : ℝ) ^ m * (m.factorial : ℝ) * Real.exp (C : ℝ) ^ r *
          (Real.exp (C : ℝ) * ((C : ℝ) ^ r / (r.factorial : ℝ))) ^ (m - r)) := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
    simpa only [mul_div_assoc] using hupper
  have : (1 : ℝ) < 1 :=
    lt_of_le_of_lt (hone_le.trans hscaledUpper) hnumeric
  exact lt_irrefl 1 this

/-- An algebraic `x`-th power at a positive rational base with independent
`2,3,q` monomials forces the exponent to be rational. -/
theorem rational_of_two_three_rat_rpow_algebraic_of_monomial_injective
    {q : ℚ} (hq : 0 < q)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦
        (2 : ℚ) ^ u.1 * (3 : ℚ) ^ u.2.1 * q ^ u.2.2))
    {x : ℝ}
    (hTwo : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (hThree : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (hqPow : IsAlgebraic ℚ ((q : ℝ) ^ x)) :
    x ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  let bridge := LeanProofs.IntegerExponent.AlgebraicOutputBridge.ofRealIsAlgebraic hqPow
  letI : Field bridge.K := bridge.fieldK
  letI : NumberField bridge.K := bridge.numberFieldK
  apply not_not.mp
  exact not_irrational_of_two_three_q_rpow_scaledAlgebraicInteger_of_monomial_injective
    hq hmono hTwo hThree bridge.preimage bridge.denominator
      (Nat.pos_of_ne_zero bridge.denominator_ne_zero) bridge.integer
      bridge.denominator_smul_preimage bridge.embedding bridge.map_preimage

/-- The preceding rational conclusion is integral because `2 ^ x` is an integer. -/
theorem integer_of_two_three_rat_rpow_algebraic_of_monomial_injective
    {q : ℚ} (hq : 0 < q)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦
        (2 : ℚ) ^ u.1 * (3 : ℚ) ^ u.2.1 * q ^ u.2.2))
    {x : ℝ}
    (hTwo : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (hThree : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (hqPow : IsAlgebraic ℚ ((q : ℝ) ^ x)) :
    x ∈ Set.range ((↑) : ℤ → ℝ) := by
  apply LeanProofs.IntegerExponent.integer_of_rational_of_two_rpow_integer
  · exact rational_of_two_three_rat_rpow_algebraic_of_monomial_injective
      hq hmono hTwo hThree hqPow
  · exact hTwo

/-- Exact algebraicity classification for positive rational auxiliary bases under a
hypothetical nonintegral integral-power solution at `2` and `3`. -/
theorem rat_rpow_isAlgebraic_iff_isTwoThreeUnit_of_not_integer
    {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    (hTwo : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (hThree : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    {q : ℚ} (hq : 0 < q) :
    IsAlgebraic ℚ ((q : ℝ) ^ x) ↔ IsTwoThreeUnit q := by
  constructor
  · intro halg
    by_contra hnot
    exact hx (integer_of_two_three_rat_rpow_algebraic_of_monomial_injective
      hq (rational_monomial_injective_of_not_isTwoThreeUnit hq hnot)
      hTwo hThree halg)
  · intro hunit
    obtain ⟨r, hr⟩ :=
      (rat_rpow_rational_iff_isTwoThreeUnit_of_not_integer
        hx hTwo hThree hq).mpr hunit
    rw [← hr]
    exact isAlgebraic_algebraMap r

/-- The easy direction of the desired endpoint: a `2,3`-unit already has rational,
hence algebraic, `x`-th power. -/
theorem rpow_isAlgebraic_of_isTwoThreeUnit
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {q : ℚ} (hq : 0 < q)
    (hunit : IsTwoThreeUnit q) : IsAlgebraic ℚ ((q : ℝ) ^ x) := by
  obtain ⟨r, hr⟩ :=
    (rat_rpow_rational_iff_isTwoThreeUnit_of_not_integer
      hx.2 hx.1.1 hx.1.2 hq).mpr hunit
  rw [← hr]
  exact isAlgebraic_algebraMap r

/-- Predicate-packaged exact algebraicity classification. -/
theorem twoBaseNonintegerSolution_rat_rpow_isAlgebraic_iff_isTwoThreeUnit
    {x : ℝ} (hx : TwoBaseNonintegerSolution x)
    {q : ℚ} (hq : 0 < q) :
    IsAlgebraic ℚ ((q : ℝ) ^ x) ↔ IsTwoThreeUnit q :=
  rat_rpow_isAlgebraic_iff_isTwoThreeUnit_of_not_integer
    hx.2 hx.1.1 hx.1.2 hq

private theorem rat_rpow_isAlgebraic_of_integer
    {x : ℝ} (hx : x ∈ Set.range ((↑) : ℤ → ℝ)) (q : ℚ) :
    IsAlgebraic ℚ ((q : ℝ) ^ x) := by
  obtain ⟨z, rfl⟩ := hx
  rw [Real.rpow_intCast, ← Rat.cast_zpow]
  exact isAlgebraic_algebraMap (q ^ z)

/-- Pointwise classification without a nonintegrality hypothesis: at a positive
rational base, the `x`-th power is algebraic exactly when either the exponent is an
integer or the base is a `2,3`-unit. -/
theorem rat_rpow_isAlgebraic_iff_integer_or_isTwoThreeUnit
    {x : ℝ}
    (hTwo : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (hThree : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    {q : ℚ} (hq : 0 < q) :
    IsAlgebraic ℚ ((q : ℝ) ^ x) ↔
      x ∈ Set.range ((↑) : ℤ → ℝ) ∨ IsTwoThreeUnit q := by
  by_cases hx : x ∈ Set.range ((↑) : ℤ → ℝ)
  · constructor
    · intro _
      exact Or.inl hx
    · intro _
      exact rat_rpow_isAlgebraic_of_integer hx q
  · rw [rat_rpow_isAlgebraic_iff_isTwoThreeUnit_of_not_integer hx hTwo hThree hq,
      or_iff_right hx]

end LeanProofs.TwoBaseIntegerExponent
