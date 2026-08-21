import ExponentialIdentities.TwoBaseIntegerExponent.RationalThirdBase

/-!
# Rational six-exponentials for three rational bases

The determinant machinery is private.  The public API only exposes the symmetric theorem
for three positive rational bases and three rational outputs.
-/

open scoped BigOperators Nat

namespace LeanProofs.RationalSixExponentials

open Set
noncomputable section

private abbrev RowBox (n : ℕ) :=
  Fin (n * n) × Fin (n * n) × Fin (n * n)

private abbrev ColBox (n : ℕ) :=
  Fin ((n * n) * n) × Fin ((n * n) * n)

private theorem card_rowBox (n : ℕ) : Fintype.card (RowBox n) = n ^ 6 := by
  simp [RowBox]
  ring

private theorem card_colBox (n : ℕ) : Fintype.card (ColBox n) = n ^ 6 := by
  simp [ColBox]
  ring

private def rowRat (a b c : ℚ) {n : ℕ} (i : RowBox n) : ℚ :=
  a ^ (i.1 : ℕ) * b ^ (i.2.1 : ℕ) * c ^ (i.2.2 : ℕ)

private def rowArg (a b c : ℚ) {n : ℕ} (i : RowBox n) : ℝ :=
  Real.log (rowRat a b c i : ℝ)

private def colArg {n : ℕ} (x : ℝ) (j : ColBox n) : ℝ :=
  (j.1 : ℝ) + (j.2 : ℝ) * x

private theorem rowRat_pos {a b c : ℚ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {n : ℕ} (i : RowBox n) : 0 < rowRat a b c i := by
  unfold rowRat
  positivity

private theorem rowRat_injective {a b c : ℚ} {n : ℕ}
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ a ^ u.1 * b ^ u.2.1 * c ^ u.2.2)) :
    Function.Injective (@rowRat a b c n) := by
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
  have huv : ((i : ℕ), (j : ℕ), (k : ℕ)) =
      ((i' : ℕ), (j' : ℕ), (k' : ℕ)) := hmono h
  simp only [Prod.mk.injEq] at huv
  exact Prod.ext (Fin.ext huv.1) (Prod.ext (Fin.ext huv.2.1) (Fin.ext huv.2.2))

private theorem rowArg_injective {a b c : ℚ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ a ^ u.1 * b ^ u.2.1 * c ^ u.2.2))
    (n : ℕ) : Function.Injective (@rowArg a b c n) := by
  intro i j h
  apply rowRat_injective hmono
  have hcast : (rowRat a b c i : ℝ) = (rowRat a b c j : ℝ) :=
    Real.log_injOn_pos
      (show 0 < (rowRat a b c i : ℝ) by exact_mod_cast rowRat_pos ha hb hc i)
      (show 0 < (rowRat a b c j : ℝ) by exact_mod_cast rowRat_pos ha hb hc j) h
  exact Rat.cast_injective hcast

private theorem colArg_injective {x : ℝ} (hx : Irrational x) (n : ℕ) :
    Function.Injective (@colArg n x) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have huv : ((i : ℕ), (j : ℕ)) = ((i' : ℕ), (j' : ℕ)) :=
    IntegerExponent.Irrational.injective_nat_add_mul hx h
  simp only [Prod.mk.injEq] at huv
  exact Prod.ext (Fin.ext huv.1) (Fin.ext huv.2)

private theorem rowArg_eq {a b c : ℚ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {n : ℕ} (i : RowBox n) :
    rowArg a b c i =
      ((i.1 : ℕ) : ℝ) * Real.log (a : ℝ) +
      ((i.2.1 : ℕ) : ℝ) * Real.log (b : ℝ) +
      ((i.2.2 : ℕ) : ℝ) * Real.log (c : ℝ) := by
  simp only [rowArg, rowRat, Rat.cast_mul, Rat.cast_pow]
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow]

private theorem abs_rowArg_le {a b c : ℚ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {n : ℕ} (i : RowBox n) :
    |rowArg a b c i| ≤
      (n * n : ℕ) *
        (|Real.log (a : ℝ)| + |Real.log (b : ℝ)| + |Real.log (c : ℝ)|) := by
  have hua : ((i.1 : ℕ) : ℝ) ≤ (n * n : ℕ) := by exact_mod_cast i.1.isLt.le
  have hub : ((i.2.1 : ℕ) : ℝ) ≤ (n * n : ℕ) := by
    exact_mod_cast i.2.1.isLt.le
  have huc : ((i.2.2 : ℕ) : ℝ) ≤ (n * n : ℕ) := by
    exact_mod_cast i.2.2.isLt.le
  have habsa : |((i.1 : ℕ) : ℝ)| = ((i.1 : ℕ) : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg _)
  have habsb : |((i.2.1 : ℕ) : ℝ)| = ((i.2.1 : ℕ) : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg _)
  have habsc : |((i.2.2 : ℕ) : ℝ)| = ((i.2.2 : ℕ) : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg _)
  rw [rowArg_eq ha hb hc]
  calc
    |((i.1 : ℕ) : ℝ) * Real.log (a : ℝ) +
        ((i.2.1 : ℕ) : ℝ) * Real.log (b : ℝ) +
        ((i.2.2 : ℕ) : ℝ) * Real.log (c : ℝ)| ≤
      |((i.1 : ℕ) : ℝ) * Real.log (a : ℝ)| +
        |((i.2.1 : ℕ) : ℝ) * Real.log (b : ℝ)| +
        |((i.2.2 : ℕ) : ℝ) * Real.log (c : ℝ)| := by
      exact (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ = ((i.1 : ℕ) : ℝ) * |Real.log (a : ℝ)| +
        ((i.2.1 : ℕ) : ℝ) * |Real.log (b : ℝ)| +
        ((i.2.2 : ℕ) : ℝ) * |Real.log (c : ℝ)| := by
      rw [abs_mul, abs_mul, abs_mul, habsa, habsb, habsc]
    _ ≤ ((n * n : ℕ) : ℝ) * |Real.log (a : ℝ)| +
        ((n * n : ℕ) : ℝ) * |Real.log (b : ℝ)| +
        ((n * n : ℕ) : ℝ) * |Real.log (c : ℝ)| := by
      gcongr
    _ = (n * n : ℕ) *
        (|Real.log (a : ℝ)| + |Real.log (b : ℝ)| +
          |Real.log (c : ℝ)|) := by ring

private theorem abs_colArg_le {n : ℕ} {x : ℝ} (j : ColBox n) :
    |colArg x j| ≤ ((n * n) * n : ℕ) * (1 + |x|) := by
  have hv₀ : ((j.1 : ℕ) : ℝ) ≤ ((n * n) * n : ℕ) := by
    exact_mod_cast j.1.isLt.le
  have hv₁ : ((j.2 : ℕ) : ℝ) ≤ ((n * n) * n : ℕ) := by
    exact_mod_cast j.2.isLt.le
  have habsv₀ : |((j.1 : ℕ) : ℝ)| = ((j.1 : ℕ) : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg _)
  have habsv₁ : |((j.2 : ℕ) : ℝ)| = ((j.2 : ℕ) : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg _)
  dsimp only [colArg]
  calc
    |(j.1 : ℝ) + (j.2 : ℝ) * x| ≤
        |(j.1 : ℝ)| + |(j.2 : ℝ) * x| := abs_add_le _ _
    _ = (j.1 : ℝ) + (j.2 : ℝ) * |x| := by
      rw [abs_mul, habsv₀, habsv₁]
    _ ≤ (((n * n) * n : ℕ) : ℝ) +
        (((n * n) * n : ℕ) : ℝ) * |x| := by gcongr
    _ = ((n * n) * n : ℕ) * (1 + |x|) := by ring

private theorem abs_rowArg_mul_colArg_le {a b c : ℚ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {n D : ℕ} {x : ℝ}
    (hD : (|Real.log (a : ℝ)| + |Real.log (b : ℝ)| +
      |Real.log (c : ℝ)|) * (1 + |x|) ≤ D)
    (i : RowBox n) (j : ColBox n) :
    |rowArg a b c i * colArg x j| ≤ (D * n ^ 5 : ℕ) := by
  rw [abs_mul]
  calc
    |rowArg a b c i| * |colArg x j| ≤
        (((n * n : ℕ) : ℝ) *
          (|Real.log (a : ℝ)| + |Real.log (b : ℝ)| +
            |Real.log (c : ℝ)|)) *
        (((n * n) * n : ℕ) * (1 + |x|)) :=
      mul_le_mul (abs_rowArg_le ha hb hc i) (abs_colArg_le j)
        (abs_nonneg _) (by positivity)
    _ = ((n ^ 5 : ℕ) : ℝ) *
        ((|Real.log (a : ℝ)| + |Real.log (b : ℝ)| +
          |Real.log (c : ℝ)|) * (1 + |x|)) := by
      push_cast
      ring
    _ ≤ ((n ^ 5 : ℕ) : ℝ) * D :=
      mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg _)
    _ = (D * n ^ 5 : ℕ) := by
      push_cast
      ring

private theorem rat_pow_mul_den_pow_mem_intCast {q : ℚ} {e L : ℕ}
    (hle : e ≤ L) :
    (q.den : ℝ) ^ L * (q : ℝ) ^ e ∈ Set.range ((↑) : ℤ → ℝ) := by
  refine ⟨q.num ^ e * (q.den : ℤ) ^ (L - e), ?_⟩
  rw [Rat.cast_def]
  push_cast
  rw [div_pow]
  have hden0R : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  rw [show L = e + (L - e) by omega, pow_add]
  field_simp
  simp

private theorem row_rpow_eq {a b c ra rb rc : ℚ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {x : ℝ}
    (haPow : (ra : ℝ) = (a : ℝ) ^ x)
    (hbPow : (rb : ℝ) = (b : ℝ) ^ x)
    (hcPow : (rc : ℝ) = (c : ℝ) ^ x)
    {n : ℕ} (i : RowBox n) :
    ((rowRat a b c i : ℚ) : ℝ) ^ x =
      (ra : ℝ) ^ (i.1 : ℕ) * (rb : ℝ) ^ (i.2.1 : ℕ) *
        (rc : ℝ) ^ (i.2.2 : ℕ) := by
  simp only [rowRat, Rat.cast_mul, Rat.cast_pow]
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity)]
  rw [← Real.rpow_pow_comm (by exact_mod_cast ha.le) x (i.1 : ℕ),
    ← Real.rpow_pow_comm (by exact_mod_cast hb.le) x (i.2.1 : ℕ),
    ← Real.rpow_pow_comm (by exact_mod_cast hc.le) x (i.2.2 : ℕ)]
  rw [← haPow, ← hbPow, ← hcPow]

private theorem exp_log_mul_nat_add_eq {R : ℚ} (hR : 0 < R)
    {x : ℝ} (v₀ v₁ : ℕ) :
    Real.exp (Real.log (R : ℝ) * ((v₀ : ℝ) + (v₁ : ℝ) * x)) =
      (R : ℝ) ^ v₀ * ((R : ℝ) ^ x) ^ v₁ := by
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  rw [← Real.rpow_def_of_pos hRR]
  rw [Real.rpow_add hRR, Real.rpow_natCast]
  rw [show (v₁ : ℝ) * x = x * (v₁ : ℝ) by ring]
  rw [Real.rpow_mul_natCast hRR.le]

private theorem fin_mul_le_pow_five {n : ℕ}
    (u : Fin (n * n)) (v : Fin ((n * n) * n)) :
    (u : ℕ) * (v : ℕ) ≤ n ^ 5 := by
  calc
    (u : ℕ) * (v : ℕ) ≤ (n * n) * ((n * n) * n) :=
      Nat.mul_le_mul u.isLt.le v.isLt.le
    _ = n ^ 5 := by ring

private theorem exp_rowArg_mul_colArg_common_denominator
    {a b c ra rb rc : ℚ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {n : ℕ} {x : ℝ}
    (haPow : (ra : ℝ) = (a : ℝ) ^ x)
    (hbPow : (rb : ℝ) = (b : ℝ) ^ x)
    (hcPow : (rc : ℝ) = (c : ℝ) ^ x)
    (i : RowBox n) (j : ColBox n) :
    ∃ z : ℤ, (z : ℝ) =
      ((a.den * b.den * c.den * ra.den * rb.den * rc.den : ℕ) : ℝ) ^ (n ^ 5) *
        Real.exp (rowArg a b c i * colArg x j) := by
  let R : ℚ := rowRat a b c i
  let ua : ℕ := i.1
  let ub : ℕ := i.2.1
  let uc : ℕ := i.2.2
  let v₀ : ℕ := j.1
  let v₁ : ℕ := j.2
  have hR : 0 < R := rowRat_pos ha hb hc i
  obtain ⟨za₀, hza₀⟩ := rat_pow_mul_den_pow_mem_intCast
    (q := a) (e := ua * v₀) (L := n ^ 5) (fin_mul_le_pow_five i.1 j.1)
  obtain ⟨zb₀, hzb₀⟩ := rat_pow_mul_den_pow_mem_intCast
    (q := b) (e := ub * v₀) (L := n ^ 5) (fin_mul_le_pow_five i.2.1 j.1)
  obtain ⟨zc₀, hzc₀⟩ := rat_pow_mul_den_pow_mem_intCast
    (q := c) (e := uc * v₀) (L := n ^ 5) (fin_mul_le_pow_five i.2.2 j.1)
  obtain ⟨za₁, hza₁⟩ := rat_pow_mul_den_pow_mem_intCast
    (q := ra) (e := ua * v₁) (L := n ^ 5) (fin_mul_le_pow_five i.1 j.2)
  obtain ⟨zb₁, hzb₁⟩ := rat_pow_mul_den_pow_mem_intCast
    (q := rb) (e := ub * v₁) (L := n ^ 5) (fin_mul_le_pow_five i.2.1 j.2)
  obtain ⟨zc₁, hzc₁⟩ := rat_pow_mul_den_pow_mem_intCast
    (q := rc) (e := uc * v₁) (L := n ^ 5) (fin_mul_le_pow_five i.2.2 j.2)
  refine ⟨za₀ * zb₀ * zc₀ * za₁ * zb₁ * zc₁, ?_⟩
  change (((za₀ * zb₀ * zc₀ * za₁ * zb₁ * zc₁ : ℤ) : ℝ)) =
    ((a.den * b.den * c.den * ra.den * rb.den * rc.den : ℕ) : ℝ) ^ (n ^ 5) *
      Real.exp (Real.log (R : ℝ) * ((v₀ : ℝ) + (v₁ : ℝ) * x))
  rw [exp_log_mul_nat_add_eq hR]
  rw [show R = rowRat a b c i by rfl,
    row_rpow_eq ha hb hc haPow hbPow hcPow]
  simp only [rowRat, Rat.cast_mul, Rat.cast_pow]
  push_cast
  rw [hza₀, hzb₀, hzc₀, hza₁, hzb₁, hzc₁]
  simp only [mul_pow, pow_mul]
  dsimp only [ua, ub, uc]
  ring

private theorem not_irrational_of_three_rat_rpows_rational_of_monomial_injective
    {a b c : ℚ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ a ^ u.1 * b ^ u.2.1 * c ^ u.2.2))
    {x : ℝ}
    (haPow : ∃ ra : ℚ, (ra : ℝ) = (a : ℝ) ^ x)
    (hbPow : ∃ rb : ℚ, (rb : ℝ) = (b : ℝ) ^ x)
    (hcPow : ∃ rc : ℚ, (rc : ℝ) = (c : ℝ) ^ x) :
    ¬ Irrational x := by
  classical
  intro hxirr
  obtain ⟨ra, hra⟩ := haPow
  obtain ⟨rb, hrb⟩ := hbPow
  obtain ⟨rc, hrc⟩ := hcPow
  let K : ℝ :=
    (|Real.log (a : ℝ)| + |Real.log (b : ℝ)| + |Real.log (c : ℝ)|) *
      (1 + |x|)
  obtain ⟨D, hD⟩ := exists_nat_ge K
  let B : ℕ := a.den * b.den * c.den * ra.den * rb.den * rc.den
  let N : ℕ := 192 * D + 2 * B + 3
  let n : ℕ := 2 * N
  let m : ℕ := n ^ 6
  let r : ℕ := 32 * N ^ 6
  let C : ℕ := D * n ^ 5
  let s : ℕ := n ^ 11
  let Q : ℕ := B ^ (n ^ 5)

  have hBpos : 0 < B := by
    dsimp only [B]
    positivity
  have hDN : 192 * D ≤ N := by
    dsimp only [N]
    omega
  have hNpos : 0 < N := by
    dsimp only [N]
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
  have hmargin : B * s + 2 * r < r * r := by
    have hBN : 32 * B + 1 < 16 * N := by
      dsimp only [N]
      omega
    have hN5pos : 0 < N ^ 5 := pow_pos hNpos _
    have hstep : 32 * B * N ^ 5 + 1 < 16 * N * N ^ 5 := by
      calc
        32 * B * N ^ 5 + 1 ≤ (32 * B + 1) * N ^ 5 := by nlinarith
        _ < (16 * N) * N ^ 5 := Nat.mul_lt_mul_of_pos_right hBN hN5pos
        _ = 16 * N * N ^ 5 := rfl
    have hscale : 0 < 64 * N ^ 6 := by positivity
    have hscaled := Nat.mul_lt_mul_of_pos_right hstep hscale
    change B * (2 * N) ^ 11 + 2 * (32 * N ^ 6) <
      (32 * N ^ 6) * (32 * N ^ 6)
    calc
      B * (2 * N) ^ 11 + 2 * (32 * N ^ 6) =
          (32 * B * N ^ 5 + 1) * (64 * N ^ 6) := by ring
      _ < (16 * N * N ^ 5) * (64 * N ^ 6) := hscaled
      _ = (32 * N ^ 6) * (32 * N ^ 6) := by ring
  have hrm : r ≤ m := by omega
  obtain ⟨hsmall, hnumeric⟩ :=
    IntegerExponent.exponential_det_numeric_bound_with_denominator
      C m r B s hm hr hCr hmargin

  have hrowcard : Fintype.card (RowBox n) = m := by rw [card_rowBox]
  have hcolcard : Fintype.card (ColBox n) = m := by rw [card_colBox]
  let erow : Fin m ≃ RowBox n := (Fintype.equivFinOfCardEq hrowcard).symm
  let ecol : Fin m ≃ ColBox n := (Fintype.equivFinOfCardEq hcolcard).symm
  let row : Fin m → ℝ := fun i ↦ rowArg a b c (erow i)
  let col : Fin m → ℝ := fun j ↦ colArg x (ecol j)
  let A : Matrix (Fin m) (Fin m) ℝ := fun i j ↦ Real.exp (row i * col j)

  have hrow : Function.Injective row :=
    (rowArg_injective ha hb hc hmono n).comp erow.injective
  have hcol : Function.Injective col :=
    (colArg_injective hxirr n).comp ecol.injective
  have hAne : A.det ≠ 0 :=
    IntegerExponent.det_exp_mul_ne_zero_of_injective row col hrow hcol
  have hQpos : 0 < Q := by
    dsimp only [Q]
    exact pow_pos hBpos _
  have hAden : ∀ i j, ∃ z : ℤ, (z : ℝ) = (Q : ℝ) * A i j := by
    intro i j
    change ∃ z : ℤ, (z : ℝ) = (Q : ℝ) *
      Real.exp (rowArg a b c (erow i) * colArg x (ecol j))
    simpa only [Q, B, Nat.cast_pow, Nat.cast_mul] using
      (exp_rowArg_mul_colArg_common_denominator
        ha hb hc hra hrb hrc (erow i) (ecol j))
  have hlower : 1 / (Q : ℝ) ^ m ≤ |A.det| := by
    simpa using
      (IntegerExponent.one_div_pow_le_abs_det_of_common_denominator
        A Q hQpos hAden hAne)

  have hkernel : ∀ i j, |row i * col j| ≤ (C : ℝ) := by
    intro i j
    change |rowArg a b c (erow i) * colArg x (ecol j)| ≤ (C : ℝ)
    simpa only [C] using
      (abs_rowArg_mul_colArg_le ha hb hc
        (by simpa only [K] using hD) (erow i) (ecol j))
  have hupper : |A.det| ≤
      (2 : ℝ) ^ m * (m.factorial : ℝ) * Real.exp (C : ℝ) ^ r *
        (Real.exp (C : ℝ) * (C : ℝ) ^ r / (r.factorial : ℝ)) ^ (m - r) := by
    change |Matrix.det (fun i j ↦ Real.exp (row i * col j))| ≤ _
    exact IntegerExponent.abs_det_exp_mul_le hrm row col (C : ℝ)
      (Nat.cast_nonneg _) hkernel hsmall
  have hQm : (Q : ℝ) ^ m = (B : ℝ) ^ s := by
    dsimp only [Q, m, s]
    push_cast
    rw [← pow_mul]
    have hexp : n ^ 5 * n ^ 6 = n ^ 11 := by rw [← pow_add]
    rw [hexp]
  have hdenpos : 0 < (B : ℝ) ^ s := pow_pos (by exact_mod_cast hBpos) _
  have hlowerS : 1 / (B : ℝ) ^ s ≤ |A.det| := by
    rw [← hQm]
    exact hlower
  have hone_le : 1 ≤ (B : ℝ) ^ s * |A.det| := by
    have h := (div_le_iff₀ hdenpos).mp hlowerS
    simpa [mul_comm] using h
  have hscaledUpper : (B : ℝ) ^ s * |A.det| ≤
      (B : ℝ) ^ s *
        ((2 : ℝ) ^ m * (m.factorial : ℝ) * Real.exp (C : ℝ) ^ r *
          (Real.exp (C : ℝ) * ((C : ℝ) ^ r / (r.factorial : ℝ))) ^ (m - r)) := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
    simpa only [mul_div_assoc] using hupper
  have : (1 : ℝ) < 1 :=
    lt_of_le_of_lt (hone_le.trans hscaledUpper) hnumeric
  exact lt_irrefl 1 this

/-- **Generic rational six-exponentials special theorem.**  If three positive rational
bases have injective nonnegative monomials, then rationality of all three real powers
forces the exponent to be rational. -/
theorem rational_of_three_rat_rpows_rational_of_monomial_injective
    {a b c : ℚ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ a ^ u.1 * b ^ u.2.1 * c ^ u.2.2))
    {x : ℝ}
    (haPow : ∃ ra : ℚ, (ra : ℝ) = (a : ℝ) ^ x)
    (hbPow : ∃ rb : ℚ, (rb : ℝ) = (b : ℝ) ^ x)
    (hcPow : ∃ rc : ℚ, (rc : ℝ) = (c : ℝ) ^ x) :
    x ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  exact not_not.mp
    (not_irrational_of_three_rat_rpows_rational_of_monomial_injective
      ha hb hc hmono haPow hbPow hcPow)

/-- Contrapositive six-exponentials restriction: for an irrational exponent, three
positive rational bases with rational outputs cannot have injective nonnegative
monomials. -/
theorem not_monomial_injective_of_irrational_of_three_rat_rpows_rational
    {a b c : ℚ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {x : ℝ} (hx : Irrational x)
    (haPow : ∃ ra : ℚ, (ra : ℝ) = (a : ℝ) ^ x)
    (hbPow : ∃ rb : ℚ, (rb : ℝ) = (b : ℝ) ^ x)
    (hcPow : ∃ rc : ℚ, (rc : ℝ) = (c : ℝ) ^ x) :
    ¬ Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ a ^ u.1 * b ^ u.2.1 * c ^ u.2.2) := by
  intro hmono
  exact hx (rational_of_three_rat_rpows_rational_of_monomial_injective
    ha hb hc hmono haPow hbPow hcPow)

end

end LeanProofs.RationalSixExponentials
