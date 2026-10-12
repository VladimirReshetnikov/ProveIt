import GowersSzemeredi.Proofs13AllPrimeModuli
import GowersSzemeredi.Proofs13IntegerSquareExtraction

/-! The square-root and density losses of integer extraction fit within
the printed bounds, at the already verified double-exponential threshold. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem integer_square_width_absorption {n delta e epsilon : Real} {L : Nat}
    (hn : 1 ≤ n) (hd : 0 < delta) (heps : 0 ≤ epsilon)
    (hgap : epsilon ≤ e / 4) (hlarge : 32 ≤ delta * n ^ (e / 4))
    (hL : n ^ e ≤ L) :
    (⌈n ^ epsilon⌉₊ : Real) ≤ delta * Real.sqrt L / 16 := by
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  have hwidth : 1 ≤ n ^ epsilon := Real.one_le_rpow hn heps
  have hceil : (⌈n ^ epsilon⌉₊ : Real) ≤ 2 * n ^ epsilon := by
    have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hn0 epsilon)
    linarith only [h, hwidth]
  have hquarter : n ^ epsilon ≤ n ^ (e / 4) :=
    Real.rpow_le_rpow_of_exponent_le hn hgap
  have hhalf : n ^ (e / 2) = n ^ (e / 4) * n ^ (e / 4) := by
    rw [← Real.rpow_add (by linarith only [hn] : 0 < n)]
    congr 1
    ring
  have hretained : 32 * n ^ epsilon ≤ delta * n ^ (e / 2) := by
    rw [hhalf]
    calc
      _ ≤ (delta * n ^ (e / 4)) * n ^ epsilon :=
        mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hn0 epsilon)
      _ ≤ (delta * n ^ (e / 4)) * n ^ (e / 4) :=
        mul_le_mul_of_nonneg_left hquarter (by positivity)
      _ = _ := by ring
  have hsqrt : n ^ (e / 2) ≤ Real.sqrt L := by
    calc
      _ = Real.sqrt (n ^ e) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0]
        congr 1
        ring
      _ ≤ _ := Real.sqrt_le_sqrt hL
  have h := mul_le_mul_of_nonneg_left hsqrt hd.le
  linarith only [hceil, hretained, h]

theorem power_density_sixteen_loss {b : Real} {k j : Nat}
    (hb : 0 ≤ b) (hbhalf : b ≤ 1 / 2) (hkj : k + 4 ≤ j) :
    b ^ j ≤ b ^ k / 16 := by
  have hb1 : b ≤ 1 := hbhalf.trans (by norm_num)
  have hfour : b ^ (4 : Nat) ≤ 1 / 16 := by
    have h := pow_le_pow_left₀ hb hbhalf 4
    norm_num at h ⊢
    exact h
  calc
    _ ≤ b ^ (k + 4) := pow_le_pow_of_le_one hb hb1 hkj
    _ = b ^ k * b ^ (4 : Nat) := pow_add _ _ _
    _ ≤ b ^ k * (1 / 16) := mul_le_mul_of_nonneg_left hfour (pow_nonneg hb _)
    _ = _ := by ring

private theorem square_budget {A : Real} (hA : 4 ≤ A) :
    A + 2 ≤ 4 * A ^ (2 : Nat) ∧ 4 * A ≤ A ^ (2 : Nat) := by
  constructor <;> nlinarith only [hA]

theorem section13_integer_extraction_parameter_bounds {alpha : Real}
    (ha : 0 < alpha) (hau : alpha ≤ 1023 / 1024) :
    let A := (2 / alpha) ^ ((2 : Nat) ^ 53)
    let e := (1 / 2 : Real) ^ A
    let delta := (alpha / 2) ^ ((2 : Nat) ^ 42)
    (1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 70)) ≤ e / 4 ∧
      positivePowerThreshold 32 delta (e / 4) ≤
        Real.exp (Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 54))) := by
  let x := 2 / alpha
  let A := x ^ ((2 : Nat) ^ 53)
  let e := (1 / 2 : Real) ^ A
  let delta := (alpha / 2) ^ ((2 : Nat) ^ 42)
  have hx : 2 ≤ x := (le_div_iff₀ ha).mpr (by linarith only [hau])
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hx0 : 0 < x := by linarith only [hx]
  have hA32 : 32 ≤ A := by
    calc
      32 = (2 : Real) ^ (5 : Nat) := by norm_num
      _ ≤ x ^ (5 : Nat) := pow_le_pow_left₀ (by norm_num) hx _
      _ ≤ A := pow_le_pow_right₀ hx1 (by norm_num)
  have hA4 : 4 ≤ A := (by norm_num : (4 : Real) ≤ 32).trans hA32
  have hA0 : 0 ≤ A := (by norm_num : (0 : Real) ≤ 32).trans hA32
  have hAexp : A ≤ Real.exp A := by
    exact (le_add_of_nonneg_right (show (0 : Real) ≤ 1 by norm_num)).trans
      (Real.add_one_le_exp A)
  have hX : x ^ ((2 : Nat) ^ 54) = A ^ (2 : Nat) := by
    dsimp [A]
    rw [← pow_mul]
  have htop := section13_printed_top_dominates_threshold ha hau
  change 4 * x ^ ((2 : Nat) ^ 54) ≤ _ at htop
  rw [hX] at htop
  have hgap : A + 2 ≤ (1 / alpha) ^ ((2 : Nat) ^ 70) := by
    exact (square_budget hA4).1.trans htop
  have heps : (1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 70)) ≤ e / 4 := by
    calc
      _ ≤ (1 / 2 : Real) ^ (A + 2) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hgap
      _ = e / 4 := by
        rw [Real.rpow_add (by norm_num : (0 : Real) < 1 / 2)]
        norm_num [e]
        ring
  have hd : 0 < delta := pow_pos (by positivity) _
  have hdeltaI : delta⁻¹ ≤ Real.exp A := by
    have hbase : (alpha / 2)⁻¹ = x := by dsimp [x]; field_simp
    calc
      delta⁻¹ = x ^ ((2 : Nat) ^ 42) := by dsimp [delta]; rw [← inv_pow, hbase]
      _ ≤ A := pow_le_pow_right₀ hx1 (by norm_num)
      _ ≤ _ := hAexp
  have he : 0 < e := Real.rpow_pos_of_pos (by norm_num) _
  have heI : e⁻¹ ≤ Real.exp A := by
    dsimp [e]
    rw [← Real.inv_rpow (by norm_num : (0 : Real) ≤ 1 / 2)]
    norm_num only [one_div, inv_inv]
    exact two_rpow_le_exp hA0
  have hquarterI : (e / 4)⁻¹ ≤ Real.exp (2 * A) := by
    rw [inv_div, div_eq_mul_inv, show 2 * A = A + A by ring, Real.exp_add]
    exact mul_le_mul (hA4.trans hAexp)
      heI (by positivity) (Real.exp_pos _).le
  have hthreshold := positivePowerThreshold_le_double_exp hd (by positivity : 0 ≤ e / 4)
    hA0 (by norm_num : (0 : Real) ≤ 1) (by norm_num : (0 : Real) ≤ 1)
    (by simpa only [one_mul] using hA32.trans hAexp)
    (by simpa only [one_mul] using hdeltaI) hquarterI
  have hinner : 4 * A ≤ x ^ ((2 : Nat) ^ 54) := by
    rw [hX]
    exact (square_budget hA4).2
  refine ⟨heps, ?_⟩
  exact (show positivePowerThreshold 32 delta (e / 4) ≤ Real.exp (Real.exp (4 * A)) by
    norm_num only [show (1 + 1 + 2 : Real) = 4 by norm_num] at hthreshold
    exact hthreshold).trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hinner))

theorem integer_square_raw_length_four {n e epsilon : Real} {L : Nat}
    (hn : 1 ≤ n) (heps : 0 ≤ epsilon) (hgap : epsilon ≤ e / 4)
    (hwidth : 2 < n ^ epsilon) (hL : n ^ e ≤ L) : 4 ≤ L := by
  have hexp : epsilon * 2 ≤ e := by linarith only [heps, hgap]
  have hpower : (n ^ epsilon) ^ (2 : Nat) ≤ (L : Real) := by
    calc
      _ = n ^ (epsilon * 2) := (Real.rpow_mul_natCast (zero_le_one.trans hn) _ 2).symm
      _ ≤ n ^ e := Real.rpow_le_rpow_of_exponent_le hn hexp
      _ ≤ _ := hL
  have hreal : (4 : Real) < L := by nlinarith only [hwidth, hpower]
  have hnat : 4 < L := by exact_mod_cast hreal
  omega

end LeanProofs.GowersSzemeredi
