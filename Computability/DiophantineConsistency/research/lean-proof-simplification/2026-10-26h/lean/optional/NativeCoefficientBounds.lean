import DiophantineConsistency.NativeQuadraticParent
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith

/-!
# Sharp coefficient bounds for the package-52 native parent

The large transport coefficient occurs only linearly. A shared envelope for
the literal recipes is bounded by `2 B K`; the quadratic correction is at most
two, giving the published weighted bound `4 B K` without squaring `K`.
-/

namespace DiophantineConsistency.NativeCoefficientBounds

open SidonPositions
open NativeQuadraticParent

def envelope (ports : Fin 4 → ℤ) : ℤ :=
  2 * ports 0 ^ 2 + 2 * ports 3 * ports 0 + ports 2 + ports 3 +
    2 * ports 0 + ports 1 * ports 0 + ports 1 + 8

theorem envelope_lt (ports : Fin 4 → ℤ) (B K : ℤ)
    (hB : 2 ≤ B) (hK : 16*B ≤ K)
    (hbeta : 0 ≤ ports 0 ∧ ports 0 < B)
    (htransport : 0 ≤ ports 1 ∧ ports 1 < K)
    (hMC : 0 ≤ ports 2 ∧ ports 2 < B)
    (hMF : 0 ≤ ports 3 ∧ ports 3 < 2*B) :
    envelope ports < 2*B*K := by
  have hbetaSq : ports 0 ^ 2 ≤ B ^ 2 :=
    (sq_le_sq₀ hbeta.1 (by omega)).mpr (by omega)
  have hmaskProduct : ports 3 * ports 0 ≤ 2 * B ^ 2 := by
    calc
      ports 3 * ports 0 ≤ (2*B) * B := mul_le_mul hMF.2.le hbeta.2.le hbeta.1 (by omega)
      _ = 2 * B ^ 2 := by ring
  have hlargeProduct : ports 1 * (ports 0+1) < K*B := by
    calc
      ports 1 * (ports 0+1) ≤ ports 1 * B :=
        mul_le_mul_of_nonneg_left (by omega) htransport.1
      _ < K*B := mul_lt_mul_of_pos_right htransport.2 (by omega)
  have hBK : 16 * B ^ 2 ≤ B*K := by
    nlinarith [mul_nonneg (by omega : 0 ≤ B) (sub_nonneg.mpr hK)]
  have hsmall : 5*B+8 ≤ 5*B ^ 2 := by
    nlinarith [mul_nonneg (by omega : 0 ≤ B-2) (by omega : 0 ≤ B)]
  unfold envelope
  nlinarith [sq_nonneg B]

theorem correction_abs_mul_le (p : PairIndex 31) (a : ℤ) :
    |QuadraticCoding.correction p * a| ≤ 2 * |a| := by
  unfold QuadraticCoding.correction
  split_ifs
  · simp only [abs_mul]
    norm_num
  · simp only [one_mul]
    nlinarith [abs_nonneg a]


private theorem abs_ite_le {P : Prop} [Decidable P] {a b E : ℤ}
    (ha : |a| ≤ E) (hb : |b| ≤ E) : |if P then a else b| ≤ E := by
  by_cases h : P
  · simpa only [if_pos h] using ha
  · simpa only [if_neg h] using hb

set_option maxHeartbeats 4000000 in
/-- Every literal unweighted coefficient is bounded by the same envelope.
All branch bounds use the same seven nonnegative quantities. -/
theorem abs_rowCoefficient_le_envelope (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (k : Fin 22) (p : PairIndex 31) : |rowCoefficient ports k p| ≤ envelope ports := by
  have hsq := sq_nonneg (ports 0)
  have hmf := mul_nonneg h3 h0
  have hkp := mul_nonneg h1 h0
  fin_cases k <;> dsimp only [rowCoefficient]
  all_goals
    unfold envelope
    repeat' apply abs_ite_le
    all_goals rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]

/-- The exact height required by the package-52 radix: the large transport
port contributes linearly, and the quadratic correction contributes at most two. -/
theorem weighted_rowCoefficient_lt (ports : Fin 4 → ℤ) (B K : ℤ)
    (hB : 2 ≤ B) (hK : 16*B ≤ K)
    (hbeta : 0 ≤ ports 0 ∧ ports 0 < B)
    (htransport : 0 ≤ ports 1 ∧ ports 1 < K)
    (hMC : 0 ≤ ports 2 ∧ ports 2 < B)
    (hMF : 0 ≤ ports 3 ∧ ports 3 < 2*B)
    (k : Fin 22) (p : PairIndex 31) :
    |QuadraticCoding.correction p * rowCoefficient ports k p| < 4*B*K := by
  have hrecipe := abs_rowCoefficient_le_envelope ports hbeta.1 htransport.1 hMC.1 hMF.1 k p
  have henv := envelope_lt ports B K hB hK hbeta htransport hMC hMF
  calc
    |QuadraticCoding.correction p * rowCoefficient ports k p| ≤ 2 * |rowCoefficient ports k p| :=
      correction_abs_mul_le p _
    _ ≤ 2 * envelope ports := mul_le_mul_of_nonneg_left hrecipe (by norm_num)
    _ < 4*B*K := by nlinarith

theorem published_base_ge_two : (2 : ℤ) ≤ 2 ^ 590069 := by
  simpa only [pow_one] using
    (pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) (by decide : 1 ≤ 590069))

theorem published_large_scale : (16 : ℤ) * 2 ^ 590069 ≤ 2 ^ 592884 := by
  change (2 : ℤ) ^ 4 * 2 ^ 590069 ≤ 2 ^ 592884
  rw [← pow_add]
  exact pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) (by decide)

/-- Exact agreement with package 52's published `M`, proved by exponent laws
without expanding the million-bit integer. -/
theorem published_height_eq : (4 : ℤ) * 2 ^ 590069 * 2 ^ 592884 = 2 ^ 1182955 := by
  have hfour : (4 : ℤ) = 2 ^ 2 := by decide
  rw [hfour, ← pow_add, ← pow_add]

theorem weighted_rowCoefficient_lt_published (ports : Fin 4 → ℤ)
    (hbeta : 0 ≤ ports 0 ∧ ports 0 < 2 ^ 590069)
    (htransport : 0 ≤ ports 1 ∧ ports 1 < 2 ^ 592884)
    (hMC : 0 ≤ ports 2 ∧ ports 2 < 2 ^ 590069)
    (hMF : 0 ≤ ports 3 ∧ ports 3 < 2 * 2 ^ 590069)
    (k : Fin 22) (p : PairIndex 31) :
    |QuadraticCoding.correction p * rowCoefficient ports k p| < 2 ^ 1182955 := by
  have h := weighted_rowCoefficient_lt ports (2 ^ 590069) (2 ^ 592884)
    published_base_ge_two published_large_scale hbeta htransport hMC hMF k p
  rwa [published_height_eq] at h

end DiophantineConsistency.NativeCoefficientBounds
