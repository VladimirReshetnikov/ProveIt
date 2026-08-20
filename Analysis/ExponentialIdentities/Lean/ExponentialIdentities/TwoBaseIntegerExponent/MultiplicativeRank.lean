import ExponentialIdentities.TwoBaseIntegerExponent
import ExponentialIdentities.TwoBaseIntegerExponent.NonintegerDensity

open scoped BigOperators Nat

/-!
# Multiplicative rank of the natural-candidate sequence

This file generalizes the three-base interpolation determinant to arbitrary natural bases.
It then applies that generic six-exponentials consequence at `log 3 / log 2`: any three
natural candidates have linearly dependent prime-exponent vectors. Consequently every finite
candidate set has multiplicative rank at most two, yielding an explicit logarithmic-square
counting bound.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

abbrev RowBox (n : ℕ) := Fin (n * n) × Fin (n * n) × Fin (n * n)

abbrev ColBox (n : ℕ) := Fin ((n * n) * n) × Fin ((n * n) * n)

private theorem card_rowBox (n : ℕ) : Fintype.card (RowBox n) = n ^ 6 := by
  simp [RowBox]
  ring

private theorem card_colBox (n : ℕ) : Fintype.card (ColBox n) = n ^ 6 := by
  simp [ColBox]
  ring

private def rowNat (a b c : ℕ) {n : ℕ} (i : RowBox n) : ℕ :=
  a ^ (i.1 : ℕ) * b ^ (i.2.1 : ℕ) * c ^ (i.2.2 : ℕ)

private def rowArg (a b c : ℕ) {n : ℕ} (i : RowBox n) : ℝ :=
  Real.log (rowNat a b c i : ℝ)

private def colArg {n : ℕ} (x : ℝ) (i : ColBox n) : ℝ :=
  (i.1 : ℝ) + (i.2 : ℝ) * x

private theorem rowNat_injective {a b c n : ℕ}
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ a ^ u.1 * b ^ u.2.1 * c ^ u.2.2)) :
    Function.Injective (@rowNat a b c n) := by
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
  have huv : ((i : ℕ), (j : ℕ), (k : ℕ)) =
      ((i' : ℕ), (j' : ℕ), (k' : ℕ)) := hmono h
  simp only [Prod.mk.injEq] at huv
  exact Prod.ext (Fin.ext huv.1) (Prod.ext (Fin.ext huv.2.1) (Fin.ext huv.2.2))

private theorem colArg_injective {x : ℝ} (hx : Irrational x) (n : ℕ) :
    Function.Injective (@colArg n x) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have huv : ((i : ℕ), (j : ℕ)) = ((i' : ℕ), (j' : ℕ)) :=
    IntegerExponent.Irrational.injective_nat_add_mul hx h
  simp only [Prod.mk.injEq] at huv
  exact Prod.ext (Fin.ext huv.1) (Fin.ext huv.2)

private theorem bases_gt_one_of_monomial_injective {a b c : ℕ}
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ a ^ u.1 * b ^ u.2.1 * c ^ u.2.2)) :
    1 < a ∧ 1 < b ∧ 1 < c := by
  have ha0 : a ≠ 0 := by
    intro ha
    have h := hmono (a₁ := ((1, 0, 0) : ℕ × ℕ × ℕ))
      (a₂ := ((2, 0, 0) : ℕ × ℕ × ℕ)) (show
      a ^ (1 : ℕ) * b ^ (0 : ℕ) * c ^ (0 : ℕ) =
        a ^ (2 : ℕ) * b ^ (0 : ℕ) * c ^ (0 : ℕ) by simp [ha])
    simp at h
  have ha1 : a ≠ 1 := by
    intro ha
    have h := hmono (a₁ := ((0, 0, 0) : ℕ × ℕ × ℕ))
      (a₂ := ((1, 0, 0) : ℕ × ℕ × ℕ)) (show
      a ^ (0 : ℕ) * b ^ (0 : ℕ) * c ^ (0 : ℕ) =
        a ^ (1 : ℕ) * b ^ (0 : ℕ) * c ^ (0 : ℕ) by simp [ha])
    simp at h
  have hb0 : b ≠ 0 := by
    intro hb
    have h := hmono (a₁ := ((0, 1, 0) : ℕ × ℕ × ℕ))
      (a₂ := ((0, 2, 0) : ℕ × ℕ × ℕ)) (show
      a ^ (0 : ℕ) * b ^ (1 : ℕ) * c ^ (0 : ℕ) =
        a ^ (0 : ℕ) * b ^ (2 : ℕ) * c ^ (0 : ℕ) by simp [hb])
    simp at h
  have hb1 : b ≠ 1 := by
    intro hb
    have h := hmono (a₁ := ((0, 0, 0) : ℕ × ℕ × ℕ))
      (a₂ := ((0, 1, 0) : ℕ × ℕ × ℕ)) (show
      a ^ (0 : ℕ) * b ^ (0 : ℕ) * c ^ (0 : ℕ) =
        a ^ (0 : ℕ) * b ^ (1 : ℕ) * c ^ (0 : ℕ) by simp [hb])
    simp at h
  have hc0 : c ≠ 0 := by
    intro hc
    have h := hmono (a₁ := ((0, 0, 1) : ℕ × ℕ × ℕ))
      (a₂ := ((0, 0, 2) : ℕ × ℕ × ℕ)) (show
      a ^ (0 : ℕ) * b ^ (0 : ℕ) * c ^ (1 : ℕ) =
        a ^ (0 : ℕ) * b ^ (0 : ℕ) * c ^ (2 : ℕ) by simp [hc])
    simp at h
  have hc1 : c ≠ 1 := by
    intro hc
    have h := hmono (a₁ := ((0, 0, 0) : ℕ × ℕ × ℕ))
      (a₂ := ((0, 0, 1) : ℕ × ℕ × ℕ)) (show
      a ^ (0 : ℕ) * b ^ (0 : ℕ) * c ^ (0 : ℕ) =
        a ^ (0 : ℕ) * b ^ (0 : ℕ) * c ^ (1 : ℕ) by simp [hc])
    simp at h
  omega

private theorem rowNat_pos {a b c n : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (i : RowBox n) : 0 < rowNat a b c i := by
  unfold rowNat
  positivity

private theorem rowArg_injective {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ a ^ u.1 * b ^ u.2.1 * c ^ u.2.2))
    (n : ℕ) : Function.Injective (@rowArg a b c n) := by
  intro i j h
  apply rowNat_injective hmono
  have hcst : (rowNat a b c i : ℝ) = (rowNat a b c j : ℝ) :=
    Real.log_injOn_pos
      (show 0 < (rowNat a b c i : ℝ) by exact_mod_cast rowNat_pos ha hb hc i)
      (show 0 < (rowNat a b c j : ℝ) by exact_mod_cast rowNat_pos ha hb hc j) h
  exact Nat.cast_injective hcst

private theorem product_rpow_integer {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {x : ℝ} {ua ub uc : ℕ}
    (haPow : ∃ z : ℤ, (z : ℝ) = (a : ℝ) ^ x)
    (hbPow : ∃ z : ℤ, (z : ℝ) = (b : ℝ) ^ x)
    (hcPow : ∃ z : ℤ, (z : ℝ) = (c : ℝ) ^ x) :
    ∃ z : ℤ, (z : ℝ) = ((a ^ ua * b ^ ub * c ^ uc : ℕ) : ℝ) ^ x := by
  obtain ⟨za, hza⟩ := haPow
  obtain ⟨zb, hzb⟩ := hbPow
  obtain ⟨zc, hzc⟩ := hcPow
  refine ⟨za ^ ua * zb ^ ub * zc ^ uc, ?_⟩
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity)]
  rw [← Real.rpow_pow_comm (by exact_mod_cast ha.le) x ua,
    ← Real.rpow_pow_comm (by exact_mod_cast hb.le) x ub,
    ← Real.rpow_pow_comm (by exact_mod_cast hc.le) x uc]
  rw [← hza, ← hzb, ← hzc]

private theorem exp_log_mul_nat_add_integer {R : ℕ} (hR : 0 < R)
    {x : ℝ} (v₀ v₁ : ℕ)
    (hRx : ∃ z : ℤ, (z : ℝ) = (R : ℝ) ^ x) :
    ∃ z : ℤ,
      (z : ℝ) = Real.exp (Real.log (R : ℝ) * ((v₀ : ℝ) + (v₁ : ℝ) * x)) := by
  obtain ⟨z, hz⟩ := hRx
  refine ⟨(R : ℤ) ^ v₀ * z ^ v₁, ?_⟩
  push_cast
  rw [← Real.rpow_def_of_pos (by exact_mod_cast hR)]
  rw [Real.rpow_add (by exact_mod_cast hR)]
  rw [Real.rpow_natCast]
  rw [show (v₁ : ℝ) * x = x * (v₁ : ℝ) by ring]
  rw [Real.rpow_mul_natCast (by exact_mod_cast hR.le)]
  rw [← hz]

private theorem rowArg_nonneg {a b c n : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (i : RowBox n) :
    0 ≤ rowArg a b c i := by
  apply Real.log_nonneg
  exact_mod_cast rowNat_pos ha hb hc i

private theorem rowArg_le {a b c n : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (i : RowBox n) :
    rowArg a b c i ≤ (n * n : ℕ) * (Real.log a + Real.log b + Real.log c) := by
  have hua : ((i.1 : ℕ) : ℝ) ≤ (n * n : ℕ) := by exact_mod_cast i.1.isLt.le
  have hub : ((i.2.1 : ℕ) : ℝ) ≤ (n * n : ℕ) := by exact_mod_cast i.2.1.isLt.le
  have huc : ((i.2.2 : ℕ) : ℝ) ≤ (n * n : ℕ) := by exact_mod_cast i.2.2.isLt.le
  have hloga : 0 ≤ Real.log a := Real.log_nonneg (by exact_mod_cast ha)
  have hlogb : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast hb)
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg (by exact_mod_cast hc)
  have hterma : ((i.1 : ℕ) : ℝ) * Real.log a ≤
      ((n * n : ℕ) : ℝ) * Real.log a := mul_le_mul_of_nonneg_right hua hloga
  have htermb : ((i.2.1 : ℕ) : ℝ) * Real.log b ≤
      ((n * n : ℕ) : ℝ) * Real.log b := mul_le_mul_of_nonneg_right hub hlogb
  have htermc : ((i.2.2 : ℕ) : ℝ) * Real.log c ≤
      ((n * n : ℕ) : ℝ) * Real.log c := mul_le_mul_of_nonneg_right huc hlogc
  have hexpand : rowArg a b c i =
      ((i.1 : ℕ) : ℝ) * Real.log a +
      ((i.2.1 : ℕ) : ℝ) * Real.log b +
      ((i.2.2 : ℕ) : ℝ) * Real.log c := by
    simp only [rowArg, rowNat, Nat.cast_mul, Nat.cast_pow]
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
  rw [hexpand]
  linarith

private theorem colArg_nonneg {n : ℕ} {x : ℝ} (hx : 0 ≤ x) (i : ColBox n) :
    0 ≤ colArg x i := by
  dsimp only [colArg]
  positivity

private theorem colArg_le {n : ℕ} {x : ℝ} (hx : 0 ≤ x) (i : ColBox n) :
    colArg x i ≤ ((n * n) * n : ℕ) * (1 + x) := by
  have hv₀ : ((i.1 : ℕ) : ℝ) ≤ ((n * n) * n : ℕ) := by exact_mod_cast i.1.isLt.le
  have hv₁ : ((i.2 : ℕ) : ℝ) ≤ ((n * n) * n : ℕ) := by exact_mod_cast i.2.isLt.le
  have hv₁x : ((i.2 : ℕ) : ℝ) * x ≤
      (((n * n) * n : ℕ) : ℝ) * x := mul_le_mul_of_nonneg_right hv₁ hx
  dsimp only [colArg]
  linarith

private theorem abs_rowArg_mul_colArg_le {a b c n D : ℕ} {x : ℝ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hx : 0 ≤ x)
    (hD : (Real.log a + Real.log b + Real.log c) * (1 + x) ≤ D)
    (i : RowBox n) (j : ColBox n) :
    |rowArg a b c i * colArg x j| ≤ (D * n ^ 5 : ℕ) := by
  have hrow0 := rowArg_nonneg (by omega : 0 < a) (by omega : 0 < b) (by omega : 0 < c) i
  have hcol0 := colArg_nonneg hx j
  have hrow := rowArg_le ha.le hb.le hc.le i
  have hcol := colArg_le hx j
  rw [abs_of_nonneg (mul_nonneg hrow0 hcol0)]
  calc
    rowArg a b c i * colArg x j ≤
        ((n * n : ℕ) : ℝ) * (Real.log a + Real.log b + Real.log c) *
          (((n * n) * n : ℕ) * (1 + x)) :=
      mul_le_mul hrow hcol hcol0
        (mul_nonneg (Nat.cast_nonneg _) (by positivity))
    _ = ((n ^ 5 : ℕ) : ℝ) *
        ((Real.log a + Real.log b + Real.log c) * (1 + x)) := by
      push_cast
      ring
    _ ≤ ((n ^ 5 : ℕ) : ℝ) * D :=
      mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg _)
    _ = (D * n ^ 5 : ℕ) := by
      push_cast
      ring

private theorem exp_rowArg_mul_colArg_integer {a b c n : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {x : ℝ}
    (haPow : ∃ z : ℤ, (z : ℝ) = (a : ℝ) ^ x)
    (hbPow : ∃ z : ℤ, (z : ℝ) = (b : ℝ) ^ x)
    (hcPow : ∃ z : ℤ, (z : ℝ) = (c : ℝ) ^ x)
    (i : RowBox n) (j : ColBox n) :
    ∃ z : ℤ, (z : ℝ) = Real.exp (rowArg a b c i * colArg x j) := by
  have hR : ∃ z : ℤ, (z : ℝ) = (rowNat a b c i : ℝ) ^ x := by
    simpa only [rowNat] using
      (product_rpow_integer ha hb hc (x := x)
        (ua := (i.1 : ℕ)) (ub := (i.2.1 : ℕ)) (uc := (i.2.2 : ℕ))
        haPow hbPow hcPow)
  simpa only [rowArg, colArg] using
    (exp_log_mul_nat_add_integer (R := rowNat a b c i)
      (rowNat_pos ha hb hc i) (j.1 : ℕ) (j.2 : ℕ) hR)

private theorem nonneg_of_rpow_integer {a : ℕ} (ha : 1 < a) {x : ℝ}
    (h : ∃ z : ℤ, (z : ℝ) = (a : ℝ) ^ x) : 0 ≤ x := by
  obtain ⟨z, hz⟩ := h
  by_contra hx
  have hp : 0 < (a : ℝ) ^ x := Real.rpow_pos_of_pos (by positivity) _
  have hlt : (a : ℝ) ^ x < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast ha) (lt_of_not_ge hx)
  have hzpos : 0 < z := by exact_mod_cast (hz.symm ▸ hp)
  have hzone : z < 1 := by exact_mod_cast (hz.symm ▸ hlt)
  omega

private theorem not_irrational_of_three_rpows_integer_of_monomial_injective
    {a b c : ℕ}
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ a ^ u.1 * b ^ u.2.1 * c ^ u.2.2))
    {x : ℝ}
    (haPow : ∃ z : ℤ, (z : ℝ) = (a : ℝ) ^ x)
    (hbPow : ∃ z : ℤ, (z : ℝ) = (b : ℝ) ^ x)
    (hcPow : ∃ z : ℤ, (z : ℝ) = (c : ℝ) ^ x) :
    ¬ Irrational x := by
  intro hxirr
  obtain ⟨ha, hb, hc⟩ := bases_gt_one_of_monomial_injective hmono
  have hx0 : 0 ≤ x := nonneg_of_rpow_integer ha haPow
  let K : ℝ := (Real.log a + Real.log b + Real.log c) * (1 + x)
  obtain ⟨D, hD⟩ := exists_nat_ge K
  let N : ℕ := 192 * D + 3
  let n : ℕ := 2 * N
  let m : ℕ := n ^ 6
  let r : ℕ := 32 * N ^ 6
  let C : ℕ := D * n ^ 5

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
  have hrm : r ≤ m := by omega
  obtain ⟨hsmall, hnumeric⟩ :=
    IntegerExponent.exponential_det_numeric_bound C m r hm hr hCr

  have hrowcard : Fintype.card (RowBox n) = m := by
    rw [card_rowBox]
  have hcolcard : Fintype.card (ColBox n) = m := by
    rw [card_colBox]
  let erow : Fin m ≃ RowBox n := (Fintype.equivFinOfCardEq hrowcard).symm
  let ecol : Fin m ≃ ColBox n := (Fintype.equivFinOfCardEq hcolcard).symm
  let row : Fin m → ℝ := fun i ↦ rowArg a b c (erow i)
  let col : Fin m → ℝ := fun j ↦ colArg x (ecol j)
  let A : Matrix (Fin m) (Fin m) ℝ := fun i j ↦ Real.exp (row i * col j)

  have hrow : Function.Injective row :=
    (rowArg_injective (by omega) (by omega) (by omega) hmono n).comp erow.injective
  have hcol : Function.Injective col :=
    (colArg_injective hxirr n).comp ecol.injective
  have hAne : A.det ≠ 0 := by
    exact IntegerExponent.det_exp_mul_ne_zero_of_injective row col hrow hcol
  have hAint : ∀ i j, ∃ z : ℤ, (z : ℝ) = A i j := by
    intro i j
    exact exp_rowArg_mul_colArg_integer (by omega) (by omega) (by omega)
      haPow hbPow hcPow (erow i) (ecol j)
  have hlower : 1 ≤ |A.det| :=
    IntegerExponent.one_le_abs_det_of_integer_entries A hAint hAne

  have hkernel : ∀ i j, |row i * col j| ≤ (C : ℝ) := by
    intro i j
    change |rowArg a b c (erow i) * colArg x (ecol j)| ≤ (C : ℝ)
    simpa only [C] using
      (abs_rowArg_mul_colArg_le ha hb hc hx0
        (by simpa only [K] using hD) (erow i) (ecol j))
  have hupper : |A.det| ≤
      (2 : ℝ) ^ m * (m.factorial : ℝ) * Real.exp (C : ℝ) ^ r *
        (Real.exp (C : ℝ) * (C : ℝ) ^ r / (r.factorial : ℝ)) ^ (m - r) := by
    change |Matrix.det (fun i j ↦ Real.exp (row i * col j))| ≤ _
    exact IntegerExponent.abs_det_exp_mul_le hrm row col (C : ℝ)
      (Nat.cast_nonneg _) hkernel hsmall
  have hdet_lt : |A.det| < 1 := hupper.trans_lt (by
    simpa only [mul_div_assoc] using hnumeric)
  exact (not_lt_of_ge hlower) hdet_lt

/-- Generic three-base form of the six-exponentials determinant: if the natural
monomials in the bases are pairwise distinct, integrality of all three powers forces
the real exponent to be rational. -/
theorem rational_of_three_rpows_integer_of_monomial_injective
    {a b c : ℕ}
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ a ^ u.1 * b ^ u.2.1 * c ^ u.2.2))
    {x : ℝ}
    (haPow : ∃ z : ℤ, (z : ℝ) = (a : ℝ) ^ x)
    (hbPow : ∃ z : ℤ, (z : ℝ) = (b : ℝ) ^ x)
    (hcPow : ∃ z : ℤ, (z : ℝ) = (c : ℝ) ^ x) :
    x ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  exact not_not.mp
    (not_irrational_of_three_rpows_integer_of_monomial_injective
      hmono haPow hbPow hcPow)

private theorem two_rpow_logThreeDivLogTwo :
    (2 : ℝ) ^ (LeanProofs.TwoBaseIntegerExponent.logThreeDivLogTwo : ℝ) = 3 := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    LeanProofs.TwoBaseIntegerExponent.logThreeDivLogTwo]
  have hmul : Real.log (2 : ℝ) * (Real.log (3 : ℝ) / Real.log (2 : ℝ)) =
      Real.log (3 : ℝ) := by field_simp
  rw [hmul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]

/-- The logarithmic exponent governing the natural-candidate sequence is irrational. -/
theorem irrational_logThreeDivLogTwo :
    Irrational LeanProofs.TwoBaseIntegerExponent.logThreeDivLogTwo := by
  apply LeanProofs.TwoBaseIntegerExponent.irrational_of_not_integer_of_two_rpow_integer
  · rintro ⟨z, hz⟩
    have hz1R : (1 : ℝ) < (z : ℝ) := by
      rw [hz]
      exact LeanProofs.TwoBaseIntegerExponent.one_lt_logThreeDivLogTwo
    have hz2R : (z : ℝ) < 2 := by
      rw [hz]
      linarith [LeanProofs.TwoBaseIntegerExponent.logThreeDivLogTwo_lt_eight_fifths]
    have hz1 : (1 : ℤ) < z := by exact_mod_cast hz1R
    have hz2 : z < (2 : ℤ) := by exact_mod_cast hz2R
    omega
  · exact ⟨3, two_rpow_logThreeDivLogTwo.symm⟩

/-- No three natural candidates can be multiplicatively independent.  Equivalently,
their exponent vectors in the free abelian group on the primes have rank at most two. -/
theorem not_monomial_injective_of_three_twoBaseNaturalCandidates
    {a b c : ℕ}
    (ha : LeanProofs.TwoBaseIntegerExponent.TwoBaseNaturalCandidate a)
    (hb : LeanProofs.TwoBaseIntegerExponent.TwoBaseNaturalCandidate b)
    (hc : LeanProofs.TwoBaseIntegerExponent.TwoBaseNaturalCandidate c) :
    ¬ Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ a ^ u.1 * b ^ u.2.1 * c ^ u.2.2) := by
  intro hmono
  exact irrational_logThreeDivLogTwo
    (rational_of_three_rpows_integer_of_monomial_injective
      hmono ha.2 hb.2 hc.2)

/-- The prime-exponent vector of a natural number, regarded over `ℚ`. -/
def primeExponentVector (m : ℕ) : ℕ →₀ ℚ :=
  m.factorization.mapRange (fun e : ℕ ↦ (e : ℚ)) (by simp)

private def tripleGet (u : ℕ × ℕ × ℕ) : Fin 3 → ℕ :=
  ![u.1, u.2.1, u.2.2]

/-- The three prime-exponent vectors associated to a triple of natural numbers. -/
def threePrimeExponentVectors (a b c : ℕ) : Fin 3 → (ℕ →₀ ℚ) :=
  ![primeExponentVector a, primeExponentVector b, primeExponentVector c]

private theorem primeExponentVector_three_monomial_eval
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (u : ℕ × ℕ × ℕ) (p : ℕ) :
    primeExponentVector (a ^ u.1 * b ^ u.2.1 * c ^ u.2.2) p =
      (u.1 : ℚ) * primeExponentVector a p +
      (u.2.1 : ℚ) * primeExponentVector b p +
      (u.2.2 : ℚ) * primeExponentVector c p := by
  simp only [primeExponentVector, Finsupp.mapRange_apply]
  rw [Nat.factorization_mul
      (mul_ne_zero (pow_ne_zero _ ha.ne') (pow_ne_zero _ hb.ne'))
      (pow_ne_zero _ hc.ne'),
    Nat.factorization_mul (pow_ne_zero _ ha.ne') (pow_ne_zero _ hb.ne'),
    Nat.factorization_pow, Nat.factorization_pow, Nat.factorization_pow]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul]
  norm_cast

/-- Linear independence of three prime-exponent vectors implies injectivity of the
corresponding nonnegative monomial map. -/
theorem monomial_injective_of_primeExponentVector_linearIndependent
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hli : LinearIndependent ℚ (threePrimeExponentVectors a b c)) :
    Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ a ^ u.1 * b ^ u.2.1 * c ^ u.2.2) := by
  intro u v huv
  let g : Fin 3 → ℚ := fun i ↦ (tripleGet u i : ℚ) - (tripleGet v i : ℚ)
  have hfac (p : ℕ) :
      (u.1 : ℚ) * primeExponentVector a p +
          (u.2.1 : ℚ) * primeExponentVector b p +
          (u.2.2 : ℚ) * primeExponentVector c p =
        (v.1 : ℚ) * primeExponentVector a p +
          (v.2.1 : ℚ) * primeExponentVector b p +
          (v.2.2 : ℚ) * primeExponentVector c p := by
    rw [← primeExponentVector_three_monomial_eval ha hb hc,
      ← primeExponentVector_three_monomial_eval ha hb hc]
    exact congrArg (fun n : ℕ ↦ primeExponentVector n p) huv
  have hsum : ∑ i : Fin 3, g i • threePrimeExponentVectors a b c i = 0 := by
    ext p
    simp [Fin.sum_univ_succ, g, tripleGet, threePrimeExponentVectors]
    have hp := hfac p
    ring_nf at hp ⊢
    linarith
  have hg := (Fintype.linearIndependent_iff.mp hli) g hsum
  have h0 := hg (0 : Fin 3)
  have h1 := hg (1 : Fin 3)
  have h2 := hg (2 : Fin 3)
  simp only [g, tripleGet] at h0 h1 h2
  have hu0 : u.1 = v.1 := by exact_mod_cast (sub_eq_zero.mp h0)
  have hu1 : u.2.1 = v.2.1 := by exact_mod_cast (sub_eq_zero.mp h1)
  have hu2 : u.2.2 = v.2.2 := by exact_mod_cast (sub_eq_zero.mp h2)
  exact Prod.ext hu0 (Prod.ext hu1 hu2)

/-- The prime-exponent vectors of any three natural candidates are linearly dependent. -/
theorem not_linearIndependent_primeExponentVector_of_three_candidates
    {a b c : ℕ}
    (ha : LeanProofs.TwoBaseIntegerExponent.TwoBaseNaturalCandidate a)
    (hb : LeanProofs.TwoBaseIntegerExponent.TwoBaseNaturalCandidate b)
    (hc : LeanProofs.TwoBaseIntegerExponent.TwoBaseNaturalCandidate c) :
    ¬ LinearIndependent ℚ (threePrimeExponentVectors a b c) := by
  intro hli
  exact not_monomial_injective_of_three_twoBaseNaturalCandidates ha hb hc
    (monomial_injective_of_primeExponentVector_linearIndependent
      ha.1 hb.1 hc.1 hli)

/-- For every finite collection of natural candidates, the rational span of their
prime-exponent vectors has dimension at most two. -/
theorem finrank_span_primeExponentVectors_le_two
    (s : Finset ℕ)
    (hs : ∀ m ∈ s,
      LeanProofs.TwoBaseIntegerExponent.TwoBaseNaturalCandidate m) :
    Module.finrank ℚ
      (Submodule.span ℚ (↑(s.image primeExponentVector) : Set (ℕ →₀ ℚ))) ≤ 2 := by
  classical
  let S : Set (ℕ →₀ ℚ) := ↑(s.image primeExponentVector)
  let d : ℕ := Module.finrank ℚ (Submodule.span ℚ S)
  change d ≤ 2
  by_contra hd
  have h3d : 3 ≤ d := by omega
  obtain ⟨f, hfmem, _hfspan, hfli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ S
  let e : Fin 3 → Fin d := Fin.castLE h3d
  have heli : LinearIndependent ℚ (f ∘ e) :=
    hfli.comp e (Fin.castLE_injective h3d)
  have hmem (i : Fin 3) : f (e i) ∈ S := hfmem (e i)
  choose a haS haEq using fun i : Fin 3 ↦
    (show ∃ a ∈ s, primeExponentVector a = f (e i) by
      have hi := hmem i
      change f (e i) ∈ (↑(s.image primeExponentVector) : Set (ℕ →₀ ℚ)) at hi
      rw [Finset.coe_image] at hi
      rcases hi with ⟨a, ha, hae⟩
      exact ⟨a, by simpa using ha, hae⟩)
  have haCand (i : Fin 3) :
      LeanProofs.TwoBaseIntegerExponent.TwoBaseNaturalCandidate (a i) :=
    hs (a i) (haS i)
  have hvec : threePrimeExponentVectors (a 0) (a 1) (a 2) = f ∘ e := by
    funext i
    fin_cases i
    · simpa [threePrimeExponentVectors, Function.comp_apply] using haEq (0 : Fin 3)
    · simpa [threePrimeExponentVectors, Function.comp_apply] using haEq (1 : Fin 3)
    · simpa [threePrimeExponentVectors, Function.comp_apply] using haEq (2 : Fin 3)
  rw [← hvec] at heli
  exact not_linearIndependent_primeExponentVector_of_three_candidates
    (haCand 0) (haCand 1) (haCand 2) heli

private theorem exists_coordinate_pair_injective_of_finrank_le_two
    (P : Submodule ℚ (ℕ →₀ ℚ)) [Module.Finite ℚ P]
    (hP : Module.finrank ℚ P ≤ 2) :
    ∃ p q : ℕ, Function.Injective (fun v : P ↦ (v.1 p, v.1 q)) := by
  let d := Module.finrank ℚ P
  have hd : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hd with hd | hd | hd
  · have hsub : Subsingleton P := Module.finrank_zero_iff.mp (by simpa only [d] using hd)
    exact ⟨0, 0, fun _ _ _ ↦ @Subsingleton.elim P hsub _ _⟩
  · have hd' : Module.finrank ℚ P = 1 := by simpa only [d] using hd
    let B0 := Module.finBasis ℚ P
    let B : Module.Basis (Fin 1) ℚ P := B0.reindex (finCongr hd')
    have hBne : (B 0).1 ≠ 0 := by
      intro h
      have hz : B 0 = 0 := Subtype.ext h
      exact (B.linearIndependent.ne_zero 0) hz
    obtain ⟨p, hp⟩ := Finsupp.ne_iff.mp hBne
    refine ⟨p, p, ?_⟩
    intro x y hxy
    let z : P := x - y
    have hzp : z.1 p = 0 := by
      dsimp only [z]
      have hpEq := congrArg Prod.fst hxy
      dsimp at hpEq
      exact sub_eq_zero.mpr hpEq
    have hzrepr := B.sum_repr z
    rw [Fin.sum_univ_one] at hzrepr
    have heval := congrArg (fun w : P ↦ w.1 p) hzrepr
    simp only [Submodule.coe_smul, Finsupp.smul_apply, smul_eq_mul] at heval
    rw [hzp] at heval
    have hcoeff : B.repr z 0 = 0 := (mul_eq_zero.mp heval).resolve_right hp
    have hz0 : z = 0 := by
      rw [← hzrepr, hcoeff, zero_smul]
    exact sub_eq_zero.mp hz0
  · have hd' : Module.finrank ℚ P = 2 := by simpa only [d] using hd
    let B0 := Module.finBasis ℚ P
    let B : Module.Basis (Fin 2) ℚ P := B0.reindex (finCongr hd')
    let w0 : P := B 0
    let w1 : P := B 1
    have hw0ne : w0.1 ≠ 0 := by
      intro h
      have hz : w0 = 0 := Subtype.ext h
      exact (B.linearIndependent.ne_zero 0) hz
    obtain ⟨p, hp⟩ := Finsupp.ne_iff.mp hw0ne
    let r : ℚ := w1.1 p / w0.1 p
    have hdiff : w1 - r • w0 ≠ 0 := by
      intro h
      have hw1 : w1 = r • w0 := sub_eq_zero.mp h
      have hre := congrArg (fun z : P ↦ B.repr z 1) hw1
      have hone : (1 : ℚ) = 0 := by
        convert hre using 1 <;> simp [w0, w1]
      exact one_ne_zero hone
    have hdiffCoe : (w1 - r • w0).1 ≠ 0 := by
      intro h
      exact hdiff (Subtype.ext h)
    obtain ⟨q, hq⟩ := Finsupp.ne_iff.mp hdiffCoe
    have hdet : w0.1 p * w1.1 q - w1.1 p * w0.1 q ≠ 0 := by
      have hq' : w1.1 q - r * w0.1 q ≠ 0 := by
        simpa [r] using hq
      intro hzero
      apply hq'
      have hmul : w0.1 p * (w1.1 q - r * w0.1 q) = 0 := by
        calc
          w0.1 p * (w1.1 q - r * w0.1 q) =
              w0.1 p * w1.1 q - w1.1 p * w0.1 q := by
                dsimp only [r]
                rw [mul_sub, ← mul_assoc, mul_div_cancel₀ _ hp]
          _ = 0 := hzero
      exact (mul_eq_zero.mp hmul).resolve_left hp
    refine ⟨p, q, ?_⟩
    intro x y hxy
    let z : P := x - y
    have hzp : z.1 p = 0 := by
      dsimp only [z]
      exact sub_eq_zero.mpr (congrArg Prod.fst hxy)
    have hzq : z.1 q = 0 := by
      dsimp only [z]
      exact sub_eq_zero.mpr (congrArg Prod.snd hxy)
    have hzrepr := B.sum_repr z
    rw [Fin.sum_univ_two] at hzrepr
    have hevalp := congrArg (fun w : P ↦ w.1 p) hzrepr
    have hevalq := congrArg (fun w : P ↦ w.1 q) hzrepr
    simp only [Submodule.coe_add, Finsupp.add_apply, Submodule.coe_smul,
      Finsupp.smul_apply, smul_eq_mul] at hevalp hevalq
    rw [hzp] at hevalp
    rw [hzq] at hevalq
    have hc1det : B.repr z 1 *
        (w0.1 p * w1.1 q - w1.1 p * w0.1 q) = 0 := by
      dsimp only [w0, w1]
      linear_combination (B 0).1 p * hevalq - (B 0).1 q * hevalp
    have hc1 : B.repr z 1 = 0 := (mul_eq_zero.mp hc1det).resolve_right hdet
    have hc0mul : B.repr z 0 * w0.1 p = 0 := by
      rw [hc1, zero_mul, add_zero] at hevalp
      simpa only [w0] using hevalp
    have hc0 : B.repr z 0 = 0 := (mul_eq_zero.mp hc0mul).resolve_right hp
    have hz0 : z = 0 := by
      rw [← hzrepr, hc0, hc1, zero_smul, zero_smul, zero_add]
    exact sub_eq_zero.mp hz0

private theorem primeExponentVector_injective_of_pos {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (h : primeExponentVector m = primeExponentVector n) :
    m = n := by
  apply Nat.eq_of_factorization_eq hm.ne' hn.ne'
  intro p
  have hp := DFunLike.congr_fun h p
  simp only [primeExponentVector, Finsupp.mapRange_apply] at hp
  exact_mod_cast hp

private theorem factorization_lt_clog_two {m N p : ℕ}
    (hm : 0 < m) (hmN : m < N) :
    m.factorization p < Nat.clog 2 N := by
  by_cases he : m.factorization p = 0
  · rw [he]
    exact (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).2 (by
      simpa using (show 1 < N by omega))
  · have hmem : p ∈ m.primeFactors := by
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.mpr he
    have hp : p.Prime := (Nat.mem_primeFactors.mp hmem).1
    have hpdvd : p ^ m.factorization p ∣ m :=
      (hp.pow_dvd_iff_le_factorization hm.ne').2 le_rfl
    have hp_le_m : p ^ m.factorization p ≤ m := Nat.le_of_dvd hm hpdvd
    have htwo_le : 2 ^ m.factorization p ≤ p ^ m.factorization p :=
      Nat.pow_le_pow_left hp.two_le _
    exact (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).2
      (htwo_le.trans_lt (hp_le_m.trans_lt hmN))

/-- Explicit logarithmic-square bound: among the positive integers below `N`, at most
`clog 2 N ^ 2` have an integral `(log 3 / log 2)`-th power. -/
theorem twoBaseNaturalCandidatesBelow_card_le_clog_sq (N : ℕ) :
    (LeanProofs.TwoBaseIntegerExponent.twoBaseNaturalCandidatesBelow N).card ≤
      (Nat.clog 2 N) ^ 2 := by
  classical
  let s := LeanProofs.TwoBaseIntegerExponent.twoBaseNaturalCandidatesBelow N
  change s.card ≤ (Nat.clog 2 N) ^ 2
  by_cases hN : N ≤ 1
  · have hs0 : s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro m hm
      have hm' := hm
      simp only [s, LeanProofs.TwoBaseIntegerExponent.twoBaseNaturalCandidatesBelow,
        Finset.mem_filter, Finset.mem_range] at hm'
      rcases hm' with ⟨hmN, hmpos, _⟩
      omega
    simp only [hs0, Finset.card_empty, Nat.zero_le]
  · let S : Set (ℕ →₀ ℚ) := ↑(s.image primeExponentVector)
    let P : Submodule ℚ (ℕ →₀ ℚ) := Submodule.span ℚ S
    have hCand : ∀ m ∈ s,
        LeanProofs.TwoBaseIntegerExponent.TwoBaseNaturalCandidate m := by
      intro m hm
      have hm' := hm
      simp only [s, LeanProofs.TwoBaseIntegerExponent.twoBaseNaturalCandidatesBelow,
        Finset.mem_filter, Finset.mem_range] at hm'
      exact hm'.2
    have hlt : ∀ m ∈ s, m < N := by
      intro m hm
      have hm' := hm
      simp only [s, LeanProofs.TwoBaseIntegerExponent.twoBaseNaturalCandidatesBelow,
        Finset.mem_filter, Finset.mem_range] at hm'
      exact hm'.1
    have hrank : Module.finrank ℚ P ≤ 2 := by
      simpa only [P, S] using finrank_span_primeExponentVectors_le_two s hCand
    obtain ⟨p, q, hpq⟩ := exists_coordinate_pair_injective_of_finrank_le_two P hrank
    let L := Nat.clog 2 N
    let code : {m // m ∈ s} → Fin L × Fin L := fun m ↦
      (⟨m.1.factorization p, factorization_lt_clog_two
          (hCand m.1 m.2).1 (hlt m.1 m.2)⟩,
       ⟨m.1.factorization q, factorization_lt_clog_two
          (hCand m.1 m.2).1 (hlt m.1 m.2)⟩)
    have hcode : Function.Injective code := by
      intro m n hmn
      have hmvec : primeExponentVector m.1 ∈ S := by
        change primeExponentVector m.1 ∈ (↑(s.image primeExponentVector) : Set (ℕ →₀ ℚ))
        simp only [Finset.mem_coe, Finset.mem_image]
        exact ⟨m.1, m.2, rfl⟩
      have hnvec : primeExponentVector n.1 ∈ S := by
        change primeExponentVector n.1 ∈ (↑(s.image primeExponentVector) : Set (ℕ →₀ ℚ))
        simp only [Finset.mem_coe, Finset.mem_image]
        exact ⟨n.1, n.2, rfl⟩
      let vm : P := ⟨primeExponentVector m.1, Submodule.subset_span hmvec⟩
      let vn : P := ⟨primeExponentVector n.1, Submodule.subset_span hnvec⟩
      have hcoord : (vm.1 p, vm.1 q) = (vn.1 p, vn.1 q) := by
        apply Prod.ext
        · change (m.1.factorization p : ℚ) = (n.1.factorization p : ℚ)
          have h0 := congrArg (fun z : Fin L × Fin L ↦ z.1.1) hmn
          change m.1.factorization p = n.1.factorization p at h0
          exact_mod_cast h0
        · change (m.1.factorization q : ℚ) = (n.1.factorization q : ℚ)
          have h1 := congrArg (fun z : Fin L × Fin L ↦ z.2.1) hmn
          change m.1.factorization q = n.1.factorization q at h1
          exact_mod_cast h1
      have hv : vm = vn := hpq hcoord
      have hvec : primeExponentVector m.1 = primeExponentVector n.1 :=
        congrArg Subtype.val hv
      apply Subtype.ext
      exact primeExponentVector_injective_of_pos
        (hCand m.1 m.2).1 (hCand n.1 n.2).1 hvec
    have hcard := Fintype.card_le_of_injective code hcode
    simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin, pow_two,
      s, L] using hcard

/-- Explicit logarithmic-square bound for hypothetical noninteger candidate values. -/
theorem twoBaseNonintegerCandidatesBelow_card_le_clog_sq (N : ℕ) :
    (twoBaseNonintegerCandidatesBelow N).card ≤ (Nat.clog 2 N) ^ 2 := by
  exact (Finset.card_le_card (twoBaseNonintegerCandidatesBelow_subset N)).trans
    (twoBaseNaturalCandidatesBelow_card_le_clog_sq N)

end

end LeanProofs.TwoBaseIntegerExponent
