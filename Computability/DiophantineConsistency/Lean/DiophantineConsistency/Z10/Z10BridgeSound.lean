import DiophantineConsistency.Z10.Z10ExpCong

/-! # Ten-integer package 106: signs, the binary base and the central divisibility

Soundness steps S13–S15 of the route. At a zero with `X = ι Xn`:

* **S13** (`signs`, `b_pow`). `W = b · x₅ = 2^(2X+1) > 0`
  (`Z10ExpCong.W_eq`) and `b > 0` give `x₅ > 0`; then
  `V = 4 g x₅ Y > 0` and `Phalf = 2 · halfU² · V > 0`. The square root `β`
  of `b` divides `2^(2X+1)`, so it is a power of two (`Pow2.of_dvd`), and
  `b = β² = 2^(2s)`: the base is a power of four.
* **S14** (inside `central`). With all signs known, the registers
  `(R, Y, U, M, A, P) := (X, |L|, V, X |L|, |A/2|, Phalf)` satisfy the
  hypotheses of the unsigned ratio method `ModelRatio.ratio_sound`; the two
  (B3) inequalities are `Z10Guard.C_interval` at the Pell indices of
  `Z10Size.sizes`. The premise `4 · 2^(2X) < V` holds because
  `V = 4 x₁ W Y` with `x₁ ≥ 1`, `Y ≥ 64`. Hence
  `|L| = C(2X, X) + V · w'`. The sign of `l` is never needed.
* **S15** (`central`). `Y` divides `|L| = |l| · Y` and `V`, so
  `Y ∣ C(2X, X)`.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Z10BridgeSound
open Nine121 Nine121.N105Layout Z10Regs Z10Bootstrap Z10Squares Z10Guard Z10Index Z10KIndex
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares ArithmeticPellRecurrence ArithmeticBinomPascal
open P138Bootstrap (one_le_of_pos')

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (p : Fin 4 → DiffRing V) (x : Fin 10 → DiffRing V)
local notation "𝓡" => regs p x

/-- **S13, signs**: at a zero, `x₁`, `x₅`, `V` and `Phalf` are positive. -/
theorem signs (hz : value p x = 0) (Xn : V) (hX : (𝓡).X = ι Xn) (hX3 : 3 ≤ Xn) :
    0 < x 1 ∧ 0 < x 5 ∧ 0 < (𝓡).V ∧ 0 < (𝓡).Phalf := by
  have hb := b_pos p x hz
  have hg := (guard p x hz).2.1
  have hY := Y_pos p x hz
  have hW := Z10ExpCong.W_pos p x hz Xn hX hX3
  have hx1 : 0 < x 1 := by
    by_contra hcon
    have h := _root_.mul_nonneg hb.le (neg_nonneg.mpr (not_lt.mp hcon))
    rw [mul_neg, ← g_def p x] at h
    linarith
  have hx5 : 0 < x 5 := by
    by_contra hcon
    have h := _root_.mul_nonneg hb.le (neg_nonneg.mpr (not_lt.mp hcon))
    rw [mul_neg, ← W_def p x] at h
    linarith
  have hV : 0 < (𝓡).V := by
    rw [V_def p x]
    exact _root_.mul_pos (_root_.mul_pos (_root_.mul_pos (by norm_num) hg) hx5) hY
  have hP0 : 0 ≤ (𝓡).Phalf := by
    rw [Phalf_def p x, U_def p x, uv_def p x,
      show 2 * (𝓡).halfU * ((𝓡).halfU * (𝓡).V) = 2 * ((𝓡).halfU * (𝓡).halfU) * (𝓡).V by ring]
    exact _root_.mul_nonneg
      (_root_.mul_nonneg (by norm_num) (_root_.mul_self_nonneg _)) hV.le
  exact ⟨hx1, hx5, hV, lt_of_le_of_ne hP0 (Phalf_ne p x hz).symm⟩

/-- **S13, the base**: at a zero, `b` is a power of four. -/
theorem b_pow (hz : value p x = 0) (Xn : V) (hX : (𝓡).X = ι Xn) (hX3 : 3 ≤ Xn) :
    ∃ s : V, (𝓡).b = ι (Exp.exp (2 * s)) := by
  obtain ⟨β, -, -, -, -, -, -, -, hb, -, -, -⟩ := roots p x hz
  obtain ⟨-, hx5, -, -⟩ := signs p x hz Xn hX hX3
  obtain ⟨w, hw⟩ := nonneg_iff.mp hx5.le
  have hW := Z10ExpCong.W_eq p x hz Xn hX hX3
  rw [W_def p x, hb, hw] at hW
  have hd : β ∣ Exp.exp (2 * Xn + 1) := by
    refine ⟨β * w, ?_⟩
    apply ι_injective (V := V)
    rw [← hW]
    simp only [map_mul]
    ring
  obtain ⟨s, hs⟩ : ∃ s : V, Exp.exp s = β :=
    ⟨_, exp_of_exponential (exponential_of_pow2 (Pow2.of_dvd hd (exp_pow2 _)))⟩
  refine ⟨s, ?_⟩
  rw [hb, exp_even, sq, hs, map_mul]

/-- **S14–S15, the central divisibility**: at a zero with `X = ι Xn`, `Xn ≥ 8`, the
register `Y` is a natural number dividing the central binomial coefficient
`C(2 Xn, Xn)`. -/
theorem central (hz : value p x = 0) (Xn : V) (hX : (𝓡).X = ι Xn) (hX8 : 8 ≤ Xn) :
    ∃ Yn : V, (𝓡).Y = ι Yn ∧ Yn ∣ binom (2 * Xn) Xn := by
  have hX3 : 3 ≤ Xn := le_trans (by norm_num) hX8
  obtain ⟨a, pp, -, hA, hP, -, hC, hK, -, -, -, -⟩ := Z10Size.sizes p x hz Xn hX hX3
  obtain ⟨hx1, -, hV, -⟩ := signs p x hz Xn hX hX3
  have hY := Y_pos p x hz
  have hY64 := Z10Size.Y_ge64 p x hz
  have hW := Z10ExpCong.W_eq p x hz Xn hX hX3
  obtain ⟨Yn, hYn⟩ := nonneg_iff.mp hY.le
  obtain ⟨Ln, hLn⟩ := abs_eq_ι (𝓡).L
  obtain ⟨Vn, hVn⟩ := nonneg_iff.mp hV.le
  obtain ⟨l, hl⟩ := abs_eq_ι (x 4)
  obtain ⟨x1n, hx1n⟩ := nonneg_iff.mp hx1.le
  -- the natural-number shapes of `|L|` and `V`
  have hLY : Ln = l * Yn := by
    apply ι_injective (V := V)
    rw [← hLn, L_def p x, _root_.abs_mul, abs_of_pos hY, hl, hYn]
    simp only [map_mul]
  have hVeq : (𝓡).V = 4 * x 1 * (𝓡).W * (𝓡).Y := by
    rw [V_def p x, g_def p x, W_def p x]
    ring
  have hVnat : Vn = 4 * x1n * Exp.exp (2 * Xn + 1) * Yn := by
    apply ι_injective (V := V)
    rw [← hVn, hVeq, hW, hx1n, hYn]
    simp only [map_mul, map_ofNat]
  have hYL : Yn ∣ Ln := ⟨l, by rw [hLY]; ring⟩
  have hYV : Yn ∣ Vn := ⟨4 * x1n * Exp.exp (2 * Xn + 1), by rw [hVnat]; ring⟩
  -- sizes
  have hE : (ι (Exp.exp (2 * Xn + 1)) : DiffRing V) = 2 * ι (Exp.exp (2 * Xn)) := by
    rw [exp_succ, map_mul, map_ofNat]
  have hE1 : (1 : DiffRing V) ≤ ι (Exp.exp (2 * Xn)) := by
    have h := (ι_le_ι (V := V)).mpr (one_le_exp (2 * Xn))
    rwa [map_one] at h
  have h1 : ι (Exp.exp (2 * Xn)) ≤ x 1 * ι (Exp.exp (2 * Xn)) :=
    le_mul_of_one_le_left (by linarith) (one_le_of_pos' hx1)
  have h2 : x 1 * ι (Exp.exp (2 * Xn)) * 64 ≤ x 1 * ι (Exp.exp (2 * Xn)) * (𝓡).Y :=
    mul_le_mul_of_nonneg_left hY64 (by linarith)
  have hVbig : 512 * ι (Exp.exp (2 * Xn)) ≤ (𝓡).V := by
    rw [hVeq, hW, hE]
    linarith
  have hU4 : 4 * Exp.exp (2 * Xn) < Vn := by
    apply (ι_lt_ι (V := V)).mp
    simp only [map_mul, map_ofNat]
    rw [← hVn]
    linarith
  have hV64 : 64 ≤ Vn := by
    apply (ι_le_ι (V := V)).mp
    simp only [map_ofNat]
    rw [← hVn]
    linarith
  have hL64 : 64 ≤ Ln := by
    apply (ι_le_ι (V := V)).mp
    simp only [map_ofNat]
    rw [← hLn]
    have h := abs_L_ge p x hz
    rw [abs_of_pos hY] at h
    linarith
  -- the ratio registers
  have ha : a + 2 = Xn * Ln * (Vn + 1) := by
    apply ι_injective (V := V)
    rw [← hA, abs_halfA p x Xn hX, hLn, abs_of_pos (by linarith : (0 : DiffRing V) < 1 + (𝓡).V),
      hVn]
    simp only [map_add, map_mul, map_one]
    ring
  have hp : pp + 2 = 2 * (Xn * Ln) * (Xn * Ln) * Vn := by
    apply ι_injective (V := V)
    rw [← hP, abs_Phalf p x, abs_halfU p x Xn hX, hLn, abs_of_pos hV, hVn]
    simp only [map_mul, map_ofNat]
    ring
  have hB3a : 2 * ycoord (2 * Xn + 1) a < ycoord (Xn + 1) pp * (2 * Ln + 1) := by
    have h := (C_interval p x hz).2
    rw [hK, hC, abs_of_nonneg (ι_nonneg (ycoord (2 * Xn + 1) a)), hLn] at h
    apply (ι_lt_ι (V := V)).mp
    simp only [map_add, map_mul, map_one, map_ofNat]
    exact h
  have hB3b : 2 * ycoord (Xn + 1) pp * Ln < 2 * ycoord (2 * Xn + 1) a + ycoord (Xn + 1) pp := by
    have h := (C_interval p x hz).1
    rw [hK, hC, abs_of_nonneg (ι_nonneg (ycoord (2 * Xn + 1) a)), hLn] at h
    apply (ι_lt_ι (V := V)).mp
    simp only [map_add, map_mul, map_ofNat]
    linarith
  obtain ⟨-, hsplit⟩ := ModelRatio.ratio_sound Xn Ln Vn (Xn * Ln) (Xn * Ln * (Vn + 1))
    (2 * (Xn * Ln) * (Xn * Ln) * Vn) a pp hX8 hL64 hV64 rfl rfl rfl ha hp hB3a hB3b
  obtain ⟨w', hw'⟩ := hsplit hU4
  have hYn0 : 0 < Yn := by
    apply (ι_lt_ι (V := V)).mp
    rw [map_zero, ← hYn]
    exact hY
  refine ⟨Yn, hYn, ?_⟩
  exact ModelRatio.dvd_of_add_dvd hYn0 (by rw [← hw']; exact hYL) (Dvd.dvd.mul_right hYV w')

#print axioms b_pow
#print axioms central

end DiophantineConsistency.Z10BridgeSound
