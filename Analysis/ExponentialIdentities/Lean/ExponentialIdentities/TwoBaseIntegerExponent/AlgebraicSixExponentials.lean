import ExponentialIdentities.TwoBaseIntegerExponent.RationalThirdBase
import ExponentialIdentities.TwoBaseIntegerExponent.AlgebraicIntegerDeterminant
import ExponentialIdentities.TwoBaseIntegerExponent.FiniteAlgebraicOutputBridge

/-!
# Algebraic six-exponentials for three positive real bases

A field-norm interpolation determinant for three positive algebraic real bases and
three algebraic real outputs.  The finite-family bridge places all six values in one
number field and clears them with one natural denominator.
-/

open scoped BigOperators Nat

namespace LeanProofs.AlgebraicSixExponentials

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

private def rowReal (a b c : ℝ) {n : ℕ} (i : RowBox n) : ℝ :=
  a ^ (i.1 : ℕ) * b ^ (i.2.1 : ℕ) * c ^ (i.2.2 : ℕ)

private def rowArg (a b c : ℝ) {n : ℕ} (i : RowBox n) : ℝ :=
  Real.log (rowReal a b c i : ℝ)

private def colArg {n : ℕ} (x : ℝ) (j : ColBox n) : ℝ :=
  (j.1 : ℝ) + (j.2 : ℝ) * x

private theorem rowReal_pos {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {n : ℕ} (i : RowBox n) : 0 < rowReal a b c i := by
  unfold rowReal
  positivity

private theorem rowReal_injective {a b c : ℝ} {n : ℕ}
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ a ^ u.1 * b ^ u.2.1 * c ^ u.2.2)) :
    Function.Injective (@rowReal a b c n) := by
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
  have huv : ((i : ℕ), (j : ℕ), (k : ℕ)) =
      ((i' : ℕ), (j' : ℕ), (k' : ℕ)) := hmono h
  simp only [Prod.mk.injEq] at huv
  exact Prod.ext (Fin.ext huv.1) (Prod.ext (Fin.ext huv.2.1) (Fin.ext huv.2.2))

private theorem rowArg_injective {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ a ^ u.1 * b ^ u.2.1 * c ^ u.2.2))
    (n : ℕ) : Function.Injective (@rowArg a b c n) := by
  intro i j h
  apply rowReal_injective hmono
  have hcast : rowReal a b c i = rowReal a b c j :=
    Real.log_injOn_pos
      (rowReal_pos ha hb hc i) (rowReal_pos ha hb hc j) h
  exact hcast

private theorem colArg_injective {x : ℝ} (hx : Irrational x) (n : ℕ) :
    Function.Injective (@colArg n x) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have huv : ((i : ℕ), (j : ℕ)) = ((i' : ℕ), (j' : ℕ)) :=
    IntegerExponent.Irrational.injective_nat_add_mul hx h
  simp only [Prod.mk.injEq] at huv
  exact Prod.ext (Fin.ext huv.1) (Fin.ext huv.2)

private theorem rowArg_eq {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {n : ℕ} (i : RowBox n) :
    rowArg a b c i =
      ((i.1 : ℕ) : ℝ) * Real.log (a : ℝ) +
      ((i.2.1 : ℕ) : ℝ) * Real.log (b : ℝ) +
      ((i.2.2 : ℕ) : ℝ) * Real.log (c : ℝ) := by
  simp only [rowArg, rowReal]
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow]

private theorem abs_rowArg_le {a b c : ℝ}
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

private theorem abs_rowArg_mul_colArg_le {a b c : ℝ}
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

private theorem row_rpow_eq {a b c x : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {n : ℕ} (i : RowBox n) :
    (rowReal a b c i) ^ x =
      (a ^ x) ^ (i.1 : ℕ) * (b ^ x) ^ (i.2.1 : ℕ) *
        (c ^ x) ^ (i.2.2 : ℕ) := by
  simp only [rowReal]
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity)]
  rw [← Real.rpow_pow_comm ha.le x (i.1 : ℕ),
    ← Real.rpow_pow_comm hb.le x (i.2.1 : ℕ),
    ← Real.rpow_pow_comm hc.le x (i.2.2 : ℕ)]

private theorem exp_log_mul_nat_add_eq {R x : ℝ} (hR : 0 < R)
    (v₀ v₁ : ℕ) :
    Real.exp (Real.log R * ((v₀ : ℝ) + (v₁ : ℝ) * x)) =
      R ^ v₀ * (R ^ x) ^ v₁ := by
  rw [← Real.rpow_def_of_pos hR, Real.rpow_add hR, Real.rpow_natCast]
  rw [show (v₁ : ℝ) * x = x * (v₁ : ℝ) by ring]
  rw [Real.rpow_mul_natCast hR.le]

private theorem exp_rowArg_mul_colArg_eq {a b c x : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {n : ℕ} (i : RowBox n) (j : ColBox n) :
    Real.exp (rowArg a b c i * colArg x j) =
      a ^ ((i.1 : ℕ) * (j.1 : ℕ)) *
      b ^ ((i.2.1 : ℕ) * (j.1 : ℕ)) *
      c ^ ((i.2.2 : ℕ) * (j.1 : ℕ)) *
      (a ^ x) ^ ((i.1 : ℕ) * (j.2 : ℕ)) *
      (b ^ x) ^ ((i.2.1 : ℕ) * (j.2 : ℕ)) *
      (c ^ x) ^ ((i.2.2 : ℕ) * (j.2 : ℕ)) := by
  rw [rowArg, colArg,
    exp_log_mul_nat_add_eq (rowReal_pos ha hb hc i)]
  rw [row_rpow_eq ha hb hc]
  simp only [rowReal, mul_pow, pow_mul]
  ring

private def sixValues (a b c x : ℝ) : Fin 6 → ℝ :=
  ![a, b, c, a ^ x, b ^ x, c ^ x]

private theorem coordinate_mul_le_pow_five {n : ℕ}
    (u : Fin (n * n)) (v : Fin ((n * n) * n)) :
    (u : ℕ) * (v : ℕ) ≤ n ^ 5 := by
  calc
    (u : ℕ) * (v : ℕ) ≤ (n * n) * ((n * n) * n) :=
      Nat.mul_le_mul u.isLt.le v.isLt.le
    _ = n ^ 5 := by ring

private def scaledPair {K : Type*} [Field K] [NumberField K]
    (gamma : NumberField.RingOfIntegers K) (d L e : ℕ) :
    NumberField.RingOfIntegers K :=
  (d : NumberField.RingOfIntegers K) ^ (L - e) * gamma ^ e

private def algebraicEntry {K : Type*} [Field K] [NumberField K]
    (gamma : Fin 6 → NumberField.RingOfIntegers K) (d L : ℕ)
    {n : ℕ} (i : RowBox n) (j : ColBox n) :
    NumberField.RingOfIntegers K :=
  scaledPair (gamma 0) d L ((i.1 : ℕ) * (j.1 : ℕ)) *
  scaledPair (gamma 1) d L ((i.2.1 : ℕ) * (j.1 : ℕ)) *
  scaledPair (gamma 2) d L ((i.2.2 : ℕ) * (j.1 : ℕ)) *
  scaledPair (gamma 3) d L ((i.1 : ℕ) * (j.2 : ℕ)) *
  scaledPair (gamma 4) d L ((i.2.1 : ℕ) * (j.2 : ℕ)) *
  scaledPair (gamma 5) d L ((i.2.2 : ℕ) * (j.2 : ℕ))

private theorem map_scaledPair
    {K : Type*} [Field K] [NumberField K]
    (gamma : NumberField.RingOfIntegers K) (sigma : K →+* ℂ)
    (d L e : ℕ) (y : ℝ)
    (hgamma : sigma (gamma : K) = (d : ℂ) * (y : ℂ))
    (he : e ≤ L) :
    sigma ((scaledPair gamma d L e : NumberField.RingOfIntegers K) : K) =
      (d : ℂ) ^ L * (y : ℂ) ^ e := by
  simp only [scaledPair, map_mul, map_pow,
    map_natCast]
  rw [hgamma, mul_pow]
  have hdPow :
      (d : ℂ) ^ (L - e) * (d : ℂ) ^ e = (d : ℂ) ^ L := by
    rw [← pow_add, Nat.sub_add_cancel he]
  calc
    (d : ℂ) ^ (L - e) * ((d : ℂ) ^ e * (y : ℂ) ^ e) =
        ((d : ℂ) ^ (L - e) * (d : ℂ) ^ e) * (y : ℂ) ^ e := by ring
    _ = (d : ℂ) ^ L * (y : ℂ) ^ e := by rw [hdPow]

private theorem map_algebraicEntry
    {K : Type*} [Field K] [NumberField K]
    (gamma : Fin 6 → NumberField.RingOfIntegers K) (sigma : K →+* ℂ)
    (d L : ℕ) {a b c x : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hgamma : ∀ k, sigma (gamma k : K) =
      (d : ℂ) * (sixValues a b c x k : ℂ))
    {n : ℕ} (i : RowBox n) (j : ColBox n)
    (hL : n ^ 5 ≤ L) :
    sigma ((algebraicEntry gamma d L i j :
      NumberField.RingOfIntegers K) : K) =
      (d : ℂ) ^ (6 * L) *
        (Real.exp (rowArg a b c i * colArg x j) : ℂ) := by
  have h₀ : (i.1 : ℕ) * (j.1 : ℕ) ≤ L :=
    (coordinate_mul_le_pow_five i.1 j.1).trans hL
  have h₁ : (i.2.1 : ℕ) * (j.1 : ℕ) ≤ L :=
    (coordinate_mul_le_pow_five i.2.1 j.1).trans hL
  have h₂ : (i.2.2 : ℕ) * (j.1 : ℕ) ≤ L :=
    (coordinate_mul_le_pow_five i.2.2 j.1).trans hL
  have h₃ : (i.1 : ℕ) * (j.2 : ℕ) ≤ L :=
    (coordinate_mul_le_pow_five i.1 j.2).trans hL
  have h₄ : (i.2.1 : ℕ) * (j.2 : ℕ) ≤ L :=
    (coordinate_mul_le_pow_five i.2.1 j.2).trans hL
  have h₅ : (i.2.2 : ℕ) * (j.2 : ℕ) ≤ L :=
    (coordinate_mul_le_pow_five i.2.2 j.2).trans hL
  simp only [algebraicEntry, map_mul]
  rw [map_scaledPair _ sigma d L _ _ (hgamma 0) h₀,
    map_scaledPair _ sigma d L _ _ (hgamma 1) h₁,
    map_scaledPair _ sigma d L _ _ (hgamma 2) h₂,
    map_scaledPair _ sigma d L _ _ (hgamma 3) h₃,
    map_scaledPair _ sigma d L _ _ (hgamma 4) h₄,
    map_scaledPair _ sigma d L _ _ (hgamma 5) h₅]
  simp only [sixValues, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [exp_rowArg_mul_colArg_eq ha hb hc]
  push_cast
  rw [show 6 * L = L * 6 by omega, pow_mul]
  ring

private theorem norm_map_scaledPair_le
    {K : Type*} [Field K] [NumberField K]
    (gamma : NumberField.RingOfIntegers K) (tau : K →+* ℂ)
    (d L e T : ℕ)
    (hd : (d : ℝ) ≤ T)
    (hgamma : NumberField.house (gamma : K) ≤ T)
    (he : e ≤ L) :
    ‖tau ((scaledPair gamma d L e : NumberField.RingOfIntegers K) : K)‖ ≤
      (T : ℝ) ^ L := by
  have hgamma' : ‖tau (gamma : K)‖ ≤ (T : ℝ) :=
    (NumberField.norm_embedding_le_house (gamma : K) tau).trans hgamma
  have hd' : ‖tau (d : K)‖ ≤ (T : ℝ) := by
    rw [map_natCast, Complex.norm_natCast]
    exact hd
  change ‖tau ((d : K) ^ (L - e) * (gamma : K) ^ e)‖ ≤ (T : ℝ) ^ L
  simp only [map_mul, map_pow, norm_mul, norm_pow]
  calc
    ‖tau (d : K)‖ ^ (L - e) * ‖tau (gamma : K)‖ ^ e ≤
        (T : ℝ) ^ (L - e) * (T : ℝ) ^ e := by gcongr
    _ = (T : ℝ) ^ L := by
      rw [← pow_add, Nat.sub_add_cancel he]

private theorem norm_map_algebraicEntry_le
    {K : Type*} [Field K] [NumberField K]
    (gamma : Fin 6 → NumberField.RingOfIntegers K)
    (tau : K →+* ℂ) (d L T : ℕ)
    (hd : (d : ℝ) ≤ T)
    (hgamma : ∀ k, NumberField.house (gamma k : K) ≤ T)
    {n : ℕ} (i : RowBox n) (j : ColBox n)
    (hL : n ^ 5 ≤ L) :
    ‖tau ((algebraicEntry gamma d L i j :
      NumberField.RingOfIntegers K) : K)‖ ≤ (T : ℝ) ^ (6 * L) := by
  have h₀ := norm_map_scaledPair_le (gamma 0) tau d L
    ((i.1 : ℕ) * (j.1 : ℕ)) T hd (hgamma 0)
    ((coordinate_mul_le_pow_five i.1 j.1).trans hL)
  have h₁ := norm_map_scaledPair_le (gamma 1) tau d L
    ((i.2.1 : ℕ) * (j.1 : ℕ)) T hd (hgamma 1)
    ((coordinate_mul_le_pow_five i.2.1 j.1).trans hL)
  have h₂ := norm_map_scaledPair_le (gamma 2) tau d L
    ((i.2.2 : ℕ) * (j.1 : ℕ)) T hd (hgamma 2)
    ((coordinate_mul_le_pow_five i.2.2 j.1).trans hL)
  have h₃ := norm_map_scaledPair_le (gamma 3) tau d L
    ((i.1 : ℕ) * (j.2 : ℕ)) T hd (hgamma 3)
    ((coordinate_mul_le_pow_five i.1 j.2).trans hL)
  have h₄ := norm_map_scaledPair_le (gamma 4) tau d L
    ((i.2.1 : ℕ) * (j.2 : ℕ)) T hd (hgamma 4)
    ((coordinate_mul_le_pow_five i.2.1 j.2).trans hL)
  have h₅ := norm_map_scaledPair_le (gamma 5) tau d L
    ((i.2.2 : ℕ) * (j.2 : ℕ)) T hd (hgamma 5)
    ((coordinate_mul_le_pow_five i.2.2 j.2).trans hL)
  simp only [algebraicEntry, map_mul, norm_mul]
  calc
    _ ≤ ((T : ℝ) ^ L) ^ 6 := by
      calc
        _ ≤ (T : ℝ) ^ L * (T : ℝ) ^ L * (T : ℝ) ^ L *
            (T : ℝ) ^ L * (T : ℝ) ^ L * (T : ℝ) ^ L := by gcongr
        _ = ((T : ℝ) ^ L) ^ 6 := by ring
    _ = (T : ℝ) ^ (6 * L) := by
      rw [show 6 * L = L * 6 by omega, pow_mul]

private theorem real_det_loss_eq (n T degree : ℕ) :
    ((n ^ 6).factorial • (((T : ℝ) ^ (6 * n ^ 5)) ^ (n ^ 6)) : ℝ) ^
        (degree - 1) =
      ((((n ^ 6).factorial * T ^ (6 * n ^ 11)) ^ (degree - 1) : ℕ) : ℝ) := by
  simp only [nsmul_eq_mul]
  push_cast
  rw [← pow_mul]
  congr 2
  · congr 1
    ring

private theorem common_denominator_scale_pow_eq
    (d n m s : ℕ) (h : (6 * n ^ 5) * m = 6 * s) :
    ((((d ^ (6 * n ^ 5) : ℕ) : ℝ) ^ m)) =
      (((d ^ 6 : ℕ) : ℝ) ^ s) := by
  calc
    (((d ^ (6 * n ^ 5) : ℕ) : ℝ) ^ m) =
        (((d : ℝ) ^ (6 * n ^ 5)) ^ m) := by simp only [Nat.cast_pow]
    _ = (d : ℝ) ^ ((6 * n ^ 5) * m) := (pow_mul _ _ _).symm
    _ = (d : ℝ) ^ (6 * s) := by rw [h]
    _ = (((d : ℝ) ^ 6) ^ s) := pow_mul _ _ _
    _ = (((d ^ 6 : ℕ) : ℝ) ^ s) := by simp only [Nat.cast_pow]

set_option maxHeartbeats 4000000 in
private theorem not_irrational_of_finiteAlgebraicBridge
    {a b c x : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ a ^ u.1 * b ^ u.2.1 * c ^ u.2.2))
    (B : IntegerExponent.FiniteAlgebraicOutputBridge
      (fun k ↦ (sixValues a b c x k : ℂ))) :
    ¬ Irrational x := by
  classical
  letI : Field B.K := B.fieldK
  letI : NumberField B.K := B.numberFieldK
  intro hxirr

  let kernelScale : ℝ :=
    (|Real.log a| + |Real.log b| + |Real.log c|) * (1 + |x|)
  obtain ⟨D, hD⟩ := exists_nat_ge kernelScale

  let conjugateScale : ℝ :=
    1 + (B.denominator : ℝ) +
      NumberField.house (B.integer 0 : B.K) +
      NumberField.house (B.integer 1 : B.K) +
      NumberField.house (B.integer 2 : B.K) +
      NumberField.house (B.integer 3 : B.K) +
      NumberField.house (B.integer 4 : B.K) +
      NumberField.house (B.integer 5 : B.K)
  obtain ⟨T, hT⟩ := exists_nat_ge conjugateScale
  have hdNonneg : 0 ≤ (B.denominator : ℝ) := Nat.cast_nonneg _
  have hh₀ : 0 ≤ NumberField.house (B.integer 0 : B.K) :=
    NumberField.house_nonneg _
  have hh₁ : 0 ≤ NumberField.house (B.integer 1 : B.K) :=
    NumberField.house_nonneg _
  have hh₂ : 0 ≤ NumberField.house (B.integer 2 : B.K) :=
    NumberField.house_nonneg _
  have hh₃ : 0 ≤ NumberField.house (B.integer 3 : B.K) :=
    NumberField.house_nonneg _
  have hh₄ : 0 ≤ NumberField.house (B.integer 4 : B.K) :=
    NumberField.house_nonneg _
  have hh₅ : 0 ≤ NumberField.house (B.integer 5 : B.K) :=
    NumberField.house_nonneg _
  have hTOne : (1 : ℝ) ≤ T := by
    dsimp only [conjugateScale] at hT
    nlinarith
  have hTd : (B.denominator : ℝ) ≤ T := by
    dsimp only [conjugateScale] at hT
    nlinarith
  have hTgamma : ∀ k, NumberField.house (B.integer k : B.K) ≤ T := by
    intro k
    fin_cases k
    · change NumberField.house (B.integer 0 : B.K) ≤ T
      dsimp only [conjugateScale] at hT
      nlinarith
    · change NumberField.house (B.integer 1 : B.K) ≤ T
      dsimp only [conjugateScale] at hT
      nlinarith
    · change NumberField.house (B.integer 2 : B.K) ≤ T
      dsimp only [conjugateScale] at hT
      nlinarith
    · change NumberField.house (B.integer 3 : B.K) ≤ T
      dsimp only [conjugateScale] at hT
      nlinarith
    · change NumberField.house (B.integer 4 : B.K) ≤ T
      dsimp only [conjugateScale] at hT
      nlinarith
    · change NumberField.house (B.integer 5 : B.K) ≤ T
      dsimp only [conjugateScale] at hT
      nlinarith
  have hTNat : 2 ≤ T := by
    have hdpos : (0 : ℕ) < B.denominator :=
      Nat.pos_of_ne_zero B.denominator_ne_zero
    have hdone : (1 : ℝ) ≤ B.denominator := by exact_mod_cast hdpos
    have : (2 : ℝ) ≤ T := by linarith
    exact_mod_cast this

  let degree : ℕ := Module.finrank ℚ B.K
  let denominatorBase : ℕ := B.denominator ^ 6
  let numericBase : ℕ :=
    denominatorBase * (2 * T ^ 6) ^ (degree - 1)
  let N : ℕ := 192 * D + 2 * numericBase + 3
  let n : ℕ := 2 * N
  let m : ℕ := n ^ 6
  let r : ℕ := 32 * N ^ 6
  let C : ℕ := D * n ^ 5
  let s : ℕ := n ^ 11
  let E : ℝ := (T : ℝ) ^ (6 * n ^ 5)
  let Q : ℕ := B.denominator ^ (6 * n ^ 5)

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
  have hmargin : numericBase * s + 2 * r < r * r := by
    have hbN : 32 * numericBase + 1 < 16 * N := by
      dsimp only [N]
      omega
    have hN5pos : 0 < N ^ 5 := pow_pos hNpos _
    have hstep : 32 * numericBase * N ^ 5 + 1 < 16 * N * N ^ 5 := by
      calc
        32 * numericBase * N ^ 5 + 1 ≤
            (32 * numericBase + 1) * N ^ 5 := by nlinarith
        _ < (16 * N) * N ^ 5 := Nat.mul_lt_mul_of_pos_right hbN hN5pos
        _ = 16 * N * N ^ 5 := rfl
    have hscale : 0 < 64 * N ^ 6 := by positivity
    have hscaled := Nat.mul_lt_mul_of_pos_right hstep hscale
    change numericBase * (2 * N) ^ 11 + 2 * (32 * N ^ 6) <
      (32 * N ^ 6) * (32 * N ^ 6)
    calc
      numericBase * (2 * N) ^ 11 + 2 * (32 * N ^ 6) =
          (32 * numericBase * N ^ 5 + 1) * (64 * N ^ 6) := by ring
      _ < (16 * N * N ^ 5) * (64 * N ^ 6) := hscaled
      _ = (32 * N ^ 6) * (32 * N ^ 6) := by ring
  have hrm : r ≤ m := by omega
  obtain ⟨hsmall, hnumeric⟩ :=
    IntegerExponent.exponential_det_numeric_bound_with_denominator
      C m r numericBase s hm hr hCr hmargin

  have hrowcard : Fintype.card (RowBox n) = m := by rw [card_rowBox]
  have hcolcard : Fintype.card (ColBox n) = m := by rw [card_colBox]
  let erow : Fin m ≃ RowBox n := (Fintype.equivFinOfCardEq hrowcard).symm
  let ecol : Fin m ≃ ColBox n := (Fintype.equivFinOfCardEq hcolcard).symm
  let row : Fin m → ℝ := fun i ↦ rowArg a b c (erow i)
  let col : Fin m → ℝ := fun j ↦ colArg x (ecol j)
  let A : Matrix (Fin m) (Fin m) ℝ := fun i j ↦ Real.exp (row i * col j)
  let AO : Matrix (Fin m) (Fin m) (NumberField.RingOfIntegers B.K) :=
    fun i j ↦ algebraicEntry B.integer B.denominator (n ^ 5)
      (erow i) (ecol j)

  have hrow : Function.Injective row :=
    (rowArg_injective ha hb hc hmono n).comp erow.injective
  have hcol : Function.Injective col :=
    (colArg_injective hxirr n).comp ecol.injective
  have hAne : A.det ≠ 0 :=
    IntegerExponent.det_exp_mul_ne_zero_of_injective row col hrow hcol
  have hgamma : ∀ k, B.embedding (B.integer k : B.K) =
      (B.denominator : ℂ) * (sixValues a b c x k : ℂ) := by
    intro k
    rw [← B.denominator_smul_eq_map_integer k]
    simp only [nsmul_eq_mul]
  have hentryMap : ∀ i j,
      B.embedding ((AO i j : NumberField.RingOfIntegers B.K) : B.K) =
        (Q : ℂ) * (A i j : ℂ) := by
    intro i j
    simpa only [AO, Q, A, row, col, Nat.cast_pow] using
      (map_algebraicEntry B.integer B.embedding B.denominator (n ^ 5)
        ha hb hc hgamma (erow i) (ecol j) le_rfl)
  let f : NumberField.RingOfIntegers B.K →+* ℂ :=
    B.embedding.comp (algebraMap (NumberField.RingOfIntegers B.K) B.K)
  have hmatrixMap : f.mapMatrix AO = (Q : ℂ) • A.map Complex.ofReal := by
    ext i j
    change B.embedding ((AO i j : NumberField.RingOfIntegers B.K) : B.K) =
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
      exact_mod_cast (pow_ne_zero (6 * n ^ 5) B.denominator_ne_zero)
    have hAdetC : (A.det : ℂ) ≠ 0 := by exact_mod_cast hAne
    have hprod : (Q : ℂ) ^ m * (A.det : ℂ) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hQne) hAdetC
    apply hprod
    rw [← hdetMap, hzero, map_zero]

  have hentryBound : ∀ (tau : B.K →+* ℂ) i j,
      ‖tau ((AO i j : NumberField.RingOfIntegers B.K) : B.K)‖ ≤ E := by
    intro tau i j
    simpa only [AO, E] using
      (norm_map_algebraicEntry_le B.integer tau B.denominator (n ^ 5) T
        hTd hTgamma (erow i) (ecol j) le_rfl)
  have hlowerRaw :=
    IntegerExponent.one_div_entry_bound_le_scaled_norm_det AO hAOdet
      (A.map Complex.ofReal) B.embedding Q hentryMap hentryBound
  have hlower :
      1 / ((m.factorial • E ^ m : ℝ) ^ (degree - 1)) ≤
        (denominatorBase : ℝ) ^ s * |A.det| := by
    have hpowExp : (6 * n ^ 5) * m = 6 * s := by
      dsimp only [m, s]
      ring
    have hQpow : (Q : ℝ) ^ m = (denominatorBase : ℝ) ^ s := by
      simpa only [Q, denominatorBase] using
        (common_denominator_scale_pow_eq B.denominator n m s hpowExp)
    have hselectedNorm : ‖Matrix.det (A.map Complex.ofReal)‖ = |A.det| := by
      rw [hdetOfReal, Complex.norm_real, Real.norm_eq_abs]
    simpa only [Fintype.card_fin, degree, hQpow, hselectedNorm] using hlowerRaw

  have hlossNat :
      denominatorBase ^ s *
          ((n ^ 6).factorial * T ^ (6 * n ^ 11)) ^ (degree - 1) ≤
        numericBase ^ s := by
    simpa only [numericBase, s] using
      (IntegerExponent.combined_algebraic_loss_le_uniform_power
        n T degree denominatorBase hnTwo)
  have hdenEq :
      (m.factorial • E ^ m : ℝ) ^ (degree - 1) =
        (((n ^ 6).factorial * T ^ (6 * n ^ 11)) ^
          (degree - 1) : ℕ) := by
    simpa only [m, E] using real_det_loss_eq n T degree
  have hdenLe :
      (denominatorBase : ℝ) ^ s *
          (m.factorial • E ^ m : ℝ) ^ (degree - 1) ≤
        (numericBase : ℝ) ^ s := by
    rw [hdenEq]
    exact_mod_cast hlossNat
  have hdenPos : 0 < (m.factorial • E ^ m : ℝ) ^ (degree - 1) := by
    have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hTOne
    dsimp only [E]
    positivity

  have hkernel : ∀ i j, |row i * col j| ≤ (C : ℝ) := by
    intro i j
    change |rowArg a b c (erow i) * colArg x (ecol j)| ≤ (C : ℝ)
    simpa only [C] using
      (abs_rowArg_mul_colArg_le ha hb hc
        (by simpa only [kernelScale] using hD) (erow i) (ecol j))
  have hupper : |A.det| ≤
      (2 : ℝ) ^ m * (m.factorial : ℝ) * Real.exp (C : ℝ) ^ r *
        (Real.exp (C : ℝ) * (C : ℝ) ^ r / (r.factorial : ℝ)) ^ (m - r) := by
    change |Matrix.det (fun i j ↦ Real.exp (row i * col j))| ≤ _
    exact IntegerExponent.abs_det_exp_mul_le hrm row col (C : ℝ)
      (Nat.cast_nonneg _) hkernel hsmall
  have hone_le : 1 ≤ (numericBase : ℝ) ^ s * |A.det| := by
    have hone : 1 ≤
        (m.factorial • E ^ m : ℝ) ^ (degree - 1) *
          ((denominatorBase : ℝ) ^ s * |A.det|) := by
      have h := (div_le_iff₀ hdenPos).mp hlower
      simpa [mul_comm] using h
    calc
      1 ≤ (m.factorial • E ^ m : ℝ) ^ (degree - 1) *
          ((denominatorBase : ℝ) ^ s * |A.det|) := hone
      _ = ((denominatorBase : ℝ) ^ s *
          (m.factorial • E ^ m : ℝ) ^ (degree - 1)) * |A.det| := by ring
      _ ≤ (numericBase : ℝ) ^ s * |A.det| :=
        mul_le_mul_of_nonneg_right hdenLe (abs_nonneg _)
  have hscaledUpper : (numericBase : ℝ) ^ s * |A.det| ≤
      (numericBase : ℝ) ^ s *
        ((2 : ℝ) ^ m * (m.factorial : ℝ) * Real.exp (C : ℝ) ^ r *
          (Real.exp (C : ℝ) * ((C : ℝ) ^ r / (r.factorial : ℝ))) ^
            (m - r)) := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
    simpa only [mul_div_assoc] using hupper
  have : (1 : ℝ) < 1 :=
    lt_of_le_of_lt (hone_le.trans hscaledUpper) hnumeric
  exact lt_irrefl 1 this

/-- **Algebraic six-exponentials theorem for three real bases.** Three positive
algebraic real bases with injective nonnegative monomials cannot all have algebraic
`x`-th powers unless `x` is rational.  No assumption that the bases exceed `1`, or
that `x` is nonnegative, is required. -/
theorem rational_of_three_real_rpows_isAlgebraic_of_monomial_injective
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (haAlg : IsAlgebraic ℚ a) (hbAlg : IsAlgebraic ℚ b)
    (hcAlg : IsAlgebraic ℚ c)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ a ^ u.1 * b ^ u.2.1 * c ^ u.2.2))
    {x : ℝ}
    (haPowAlg : IsAlgebraic ℚ (a ^ x))
    (hbPowAlg : IsAlgebraic ℚ (b ^ x))
    (hcPowAlg : IsAlgebraic ℚ (c ^ x)) :
    x ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  have hvalues : ∀ k, IsAlgebraic ℚ (sixValues a b c x k : ℂ) := by
    intro k
    fin_cases k
    · simpa [sixValues] using haAlg.algHom Complex.ofRealHom.toRatAlgHom
    · simpa [sixValues] using hbAlg.algHom Complex.ofRealHom.toRatAlgHom
    · simpa [sixValues] using hcAlg.algHom Complex.ofRealHom.toRatAlgHom
    · simpa [sixValues] using haPowAlg.algHom Complex.ofRealHom.toRatAlgHom
    · simpa [sixValues] using hbPowAlg.algHom Complex.ofRealHom.toRatAlgHom
    · simpa [sixValues] using hcPowAlg.algHom Complex.ofRealHom.toRatAlgHom
  let B := IntegerExponent.FiniteAlgebraicOutputBridge.ofFinSixIsAlgebraic hvalues
  exact not_not.mp
    (not_irrational_of_finiteAlgebraicBridge ha hb hc hmono B)

end

end LeanProofs.AlgebraicSixExponentials
