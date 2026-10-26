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

private theorem rowEnvelope_0 (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (p : PairIndex 31) : |rowCoefficient ports 0 p| ≤ envelope ports := by
  have hsq := sq_nonneg (ports 0)
  have hmf := mul_nonneg h3 h0
  have hkp := mul_nonneg h1 h0
  have heq : rowCoefficient ports (0 : Fin 22) = (fun p => if p = ⟨(1, 1), by decide⟩ then (-(ports 0 ^ 2)) else if p = ⟨(0, 1), by decide⟩ then (((-2) * (ports 0 ^ 2)) - (2 * ports 0)) else if p = ⟨(0, 25), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then (((-(ports 0 ^ 2)) - (2 * ports 0)) + 1) else 0) := rfl
  rw [heq]
  dsimp only
  unfold envelope
  apply abs_ite_le
  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
  · apply abs_ite_le
    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
    · apply abs_ite_le
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
      · apply abs_ite_le
        · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
        · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]

private theorem rowEnvelope_1 (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (p : PairIndex 31) : |rowCoefficient ports 1 p| ≤ envelope ports := by
  have hsq := sq_nonneg (ports 0)
  have hmf := mul_nonneg h3 h0
  have hkp := mul_nonneg h1 h0
  have heq : rowCoefficient ports (1 : Fin 22) = (fun p => if p = ⟨(1, 25), by decide⟩ then (-ports 0) else if p = ⟨(0, 1), by decide⟩ then ((-2) * ports 0) else if p = ⟨(0, 17), by decide⟩ then 1 else if p = ⟨(0, 25), by decide⟩ then ((-ports 0) - 1) else if p = ⟨(0, 0), by decide⟩ then (((-2) * ports 0) - 1) else 0) := rfl
  rw [heq]
  dsimp only
  unfold envelope
  apply abs_ite_le
  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
  · apply abs_ite_le
    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
    · apply abs_ite_le
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
      · apply abs_ite_le
        · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
        · apply abs_ite_le
          · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
          · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]

private theorem rowEnvelope_2 (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (p : PairIndex 31) : |rowCoefficient ports 2 p| ≤ envelope ports := by
  have hsq := sq_nonneg (ports 0)
  have hmf := mul_nonneg h3 h0
  have hkp := mul_nonneg h1 h0
  have heq : rowCoefficient ports (2 : Fin 22) = (fun p => if p = ⟨(1, 11), by decide⟩ then (-ports 0) else if p = ⟨(0, 1), by decide⟩ then (-ports 0) else if p = ⟨(0, 11), by decide⟩ then ((-ports 0) - 1) else if p = ⟨(0, 22), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then (-ports 0) else 0) := rfl
  rw [heq]
  dsimp only
  unfold envelope
  apply abs_ite_le
  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
  · apply abs_ite_le
    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
    · apply abs_ite_le
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
      · apply abs_ite_le
        · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
        · apply abs_ite_le
          · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
          · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]

private theorem rowEnvelope_3 (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (p : PairIndex 31) : |rowCoefficient ports 3 p| ≤ envelope ports := by
  have hsq := sq_nonneg (ports 0)
  have hmf := mul_nonneg h3 h0
  have hkp := mul_nonneg h1 h0
  have heq : rowCoefficient ports (3 : Fin 22) = (fun p => if p = ⟨(10, 17), by decide⟩ then (-1) else if p = ⟨(0, 10), by decide⟩ then (-1) else if p = ⟨(0, 17), by decide⟩ then (-1) else if p = ⟨(0, 18), by decide⟩ then (-1) else if p = ⟨(0, 21), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then (-1) else 0) := rfl
  rw [heq]
  dsimp only
  unfold envelope
  apply abs_ite_le
  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
  · apply abs_ite_le
    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
    · apply abs_ite_le
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
      · apply abs_ite_le
        · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
        · apply abs_ite_le
          · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
          · apply abs_ite_le
            · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
            · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]

private theorem rowEnvelope_4 (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (p : PairIndex 31) : |rowCoefficient ports 4 p| ≤ envelope ports := by
  have hsq := sq_nonneg (ports 0)
  have hmf := mul_nonneg h3 h0
  have hkp := mul_nonneg h1 h0
  have heq : rowCoefficient ports (4 : Fin 22) = (fun p => if p = ⟨(13, 18), by decide⟩ then 1 else if p = ⟨(13, 21), by decide⟩ then (-1) else if p = ⟨(0, 13), by decide⟩ then (-1) else if p = ⟨(14, 18), by decide⟩ then 1 else if p = ⟨(14, 21), by decide⟩ then (-1) else if p = ⟨(0, 18), by decide⟩ then 2 else if p = ⟨(0, 20), by decide⟩ then 1 else if p = ⟨(0, 21), by decide⟩ then (-2) else 0) := rfl
  rw [heq]
  dsimp only
  unfold envelope
  apply abs_ite_le
  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
  · apply abs_ite_le
    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
    · apply abs_ite_le
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
      · apply abs_ite_le
        · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
        · apply abs_ite_le
          · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
          · apply abs_ite_le
            · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
            · apply abs_ite_le
              · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
              · apply abs_ite_le
                · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
                · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]

private theorem rowEnvelope_5 (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (p : PairIndex 31) : |rowCoefficient ports 5 p| ≤ envelope ports := by
  have hsq := sq_nonneg (ports 0)
  have hmf := mul_nonneg h3 h0
  have hkp := mul_nonneg h1 h0
  have heq : rowCoefficient ports (5 : Fin 22) = (fun p => if p = ⟨(13, 18), by decide⟩ then 1 else if p = ⟨(0, 14), by decide⟩ then (-1) else if p = ⟨(18, 20), by decide⟩ then (-1) else if p = ⟨(0, 19), by decide⟩ then 1 else if p = ⟨(0, 20), by decide⟩ then (-1) else if p = ⟨(0, 0), by decide⟩ then (-1) else 0) := rfl
  rw [heq]
  dsimp only
  unfold envelope
  apply abs_ite_le
  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
  · apply abs_ite_le
    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
    · apply abs_ite_le
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
      · apply abs_ite_le
        · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
        · apply abs_ite_le
          · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
          · apply abs_ite_le
            · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
            · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]

private theorem rowEnvelope_6 (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (p : PairIndex 31) : |rowCoefficient ports 6 p| ≤ envelope ports := by
  have hsq := sq_nonneg (ports 0)
  have hmf := mul_nonneg h3 h0
  have hkp := mul_nonneg h1 h0
  have heq : rowCoefficient ports (6 : Fin 22) = (fun p => if p = ⟨(12, 12), by decide⟩ then 1 else if p = ⟨(0, 12), by decide⟩ then 2 else if p = ⟨(13, 19), by decide⟩ then 1 else if p = ⟨(0, 13), by decide⟩ then 1 else if p = ⟨(14, 19), by decide⟩ then 1 else if p = ⟨(0, 14), by decide⟩ then 1 else if p = ⟨(19, 19), by decide⟩ then (-1) else if p = ⟨(0, 0), by decide⟩ then 1 else 0) := rfl
  rw [heq]
  dsimp only
  unfold envelope
  apply abs_ite_le
  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
  · apply abs_ite_le
    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
    · apply abs_ite_le
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
      · apply abs_ite_le
        · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
        · apply abs_ite_le
          · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
          · apply abs_ite_le
            · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
            · apply abs_ite_le
              · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
              · apply abs_ite_le
                · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
                · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]

private theorem rowEnvelope_7 (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (p : PairIndex 31) : |rowCoefficient ports 7 p| ≤ envelope ports := by
  have hsq := sq_nonneg (ports 0)
  have hmf := mul_nonneg h3 h0
  have hkp := mul_nonneg h1 h0
  have heq : rowCoefficient ports (7 : Fin 22) = (fun p => if p = ⟨(16, 21), by decide⟩ then (-4) else if p = ⟨(0, 16), by decide⟩ then (-7) else if p = ⟨(20, 21), by decide⟩ then (-1) else if p = ⟨(0, 20), by decide⟩ then (-1) else if p = ⟨(0, 21), by decide⟩ then (-5) else if p = ⟨(0, 22), by decide⟩ then (-1) else if p = ⟨(0, 23), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then (-8) else 0) := rfl
  rw [heq]
  dsimp only
  unfold envelope
  apply abs_ite_le
  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
  · apply abs_ite_le
    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
    · apply abs_ite_le
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
      · apply abs_ite_le
        · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
        · apply abs_ite_le
          · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
          · apply abs_ite_le
            · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
            · apply abs_ite_le
              · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
              · apply abs_ite_le
                · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
                · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]

private theorem rowEnvelope_8 (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (p : PairIndex 31) : |rowCoefficient ports 8 p| ≤ envelope ports := by
  have hsq := sq_nonneg (ports 0)
  have hmf := mul_nonneg h3 h0
  have hkp := mul_nonneg h1 h0
  have heq : rowCoefficient ports (8 : Fin 22) = (fun p => if p = ⟨(21, 21), by decide⟩ then (-1) else if p = ⟨(0, 21), by decide⟩ then (-6) else if p = ⟨(0, 31), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then (-7) else 0) := rfl
  rw [heq]
  dsimp only
  unfold envelope
  apply abs_ite_le
  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
  · apply abs_ite_le
    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
    · apply abs_ite_le
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
      · apply abs_ite_le
        · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
        · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]

private theorem rowEnvelope_9 (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (p : PairIndex 31) : |rowCoefficient ports 9 p| ≤ envelope ports := by
  have hsq := sq_nonneg (ports 0)
  have hmf := mul_nonneg h3 h0
  have hkp := mul_nonneg h1 h0
  have heq : rowCoefficient ports (9 : Fin 22) = (fun p => if p = ⟨(20, 20), by decide⟩ then (-1) else if p = ⟨(0, 20), by decide⟩ then (-2) else if p = ⟨(0, 24), by decide⟩ then 1 else 0) := rfl
  rw [heq]
  dsimp only
  unfold envelope
  apply abs_ite_le
  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
  · apply abs_ite_le
    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
    · apply abs_ite_le
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]

private theorem rowEnvelope_10 (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (p : PairIndex 31) : |rowCoefficient ports 10 p| ≤ envelope ports := by
  have hsq := sq_nonneg (ports 0)
  have hmf := mul_nonneg h3 h0
  have hkp := mul_nonneg h1 h0
  have heq : rowCoefficient ports (10 : Fin 22) = (fun p => if p = ⟨(23, 23), by decide⟩ then 1 else if p = ⟨(0, 23), by decide⟩ then 2 else if p = ⟨(24, 31), by decide⟩ then (-1) else if p = ⟨(0, 24), by decide⟩ then (-1) else if p = ⟨(0, 31), by decide⟩ then (-1) else if p = ⟨(0, 0), by decide⟩ then (-1) else 0) := rfl
  rw [heq]
  dsimp only
  unfold envelope
  apply abs_ite_le
  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
  · apply abs_ite_le
    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
    · apply abs_ite_le
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
      · apply abs_ite_le
        · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
        · apply abs_ite_le
          · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
          · apply abs_ite_le
            · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
            · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]

private theorem rowEnvelope_11 (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (p : PairIndex 31) : |rowCoefficient ports 11 p| ≤ envelope ports := by
  have hsq := sq_nonneg (ports 0)
  have hmf := mul_nonneg h3 h0
  have hkp := mul_nonneg h1 h0
  have heq : rowCoefficient ports (11 : Fin 22) = (fun p => if p = ⟨(6, 18), by decide⟩ then (-1) else if p = ⟨(0, 6), by decide⟩ then (-1) else if p = ⟨(9, 20), by decide⟩ then (-1) else if p = ⟨(0, 9), by decide⟩ then (-1) else if p = ⟨(0, 13), by decide⟩ then 1 else if p = ⟨(0, 14), by decide⟩ then 1 else if p = ⟨(0, 18), by decide⟩ then (-1) else if p = ⟨(0, 20), by decide⟩ then (-1) else if p = ⟨(0, 27), by decide⟩ then 1 else 0) := rfl
  rw [heq]
  dsimp only
  unfold envelope
  apply abs_ite_le
  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
  · apply abs_ite_le
    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
    · apply abs_ite_le
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
      · apply abs_ite_le
        · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
        · apply abs_ite_le
          · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
          · apply abs_ite_le
            · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
            · apply abs_ite_le
              · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
              · apply abs_ite_le
                · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
                · apply abs_ite_le
                  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
                  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]

private theorem rowEnvelope_12 (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (p : PairIndex 31) : |rowCoefficient ports 12 p| ≤ envelope ports := by
  have hsq := sq_nonneg (ports 0)
  have hmf := mul_nonneg h3 h0
  have hkp := mul_nonneg h1 h0
  have heq : rowCoefficient ports (12 : Fin 22) = (fun p => if p = ⟨(1, 1), by decide⟩ then (((-ports 3) * ports 0) + (ports 0 ^ 2)) else if p = ⟨(1, 2), by decide⟩ then (-ports 0) else if p = ⟨(1, 17), by decide⟩ then (-ports 0) else if p = ⟨(1, 25), by decide⟩ then ports 0 else if p = ⟨(0, 1), by decide⟩ then (((((-ports 2) - ((2 * ports 3) * ports 0)) - ports 3) + (2 * (ports 0 ^ 2))) + ports 0) else if p = ⟨(2, 17), by decide⟩ then 1 else if p = ⟨(2, 25), by decide⟩ then (-1) else if p = ⟨(0, 2), by decide⟩ then ((-ports 0) - 1) else if p = ⟨(3, 25), by decide⟩ then (-1) else if p = ⟨(0, 3), by decide⟩ then (-1) else if p = ⟨(9, 20), by decide⟩ then 1 else if p = ⟨(0, 9), by decide⟩ then 1 else if p = ⟨(0, 17), by decide⟩ then (-ports 0) else if p = ⟨(0, 20), by decide⟩ then 1 else if p = ⟨(0, 25), by decide⟩ then (ports 0 - 1) else if p = ⟨(0, 27), by decide⟩ then (-1) else if p = ⟨(0, 0), by decide⟩ then ((((((-ports 2) - (ports 3 * ports 0)) - ports 3) + (ports 0 ^ 2)) + ports 0) - 1) else 0) := rfl
  rw [heq]
  dsimp only
  unfold envelope
  apply abs_ite_le
  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
  · apply abs_ite_le
    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
    · apply abs_ite_le
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
      · apply abs_ite_le
        · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
        · apply abs_ite_le
          · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
          · apply abs_ite_le
            · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
            · apply abs_ite_le
              · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
              · apply abs_ite_le
                · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
                · apply abs_ite_le
                  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
                  · apply abs_ite_le
                    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
                    · apply abs_ite_le
                      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
                      · apply abs_ite_le
                        · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
                        · apply abs_ite_le
                          · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
                          · apply abs_ite_le
                            · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
                            · apply abs_ite_le
                              · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
                              · apply abs_ite_le
                                · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
                                · apply abs_ite_le
                                  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
                                  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]

private theorem rowEnvelope_13 (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (p : PairIndex 31) : |rowCoefficient ports 13 p| ≤ envelope ports := by
  have hsq := sq_nonneg (ports 0)
  have hmf := mul_nonneg h3 h0
  have hkp := mul_nonneg h1 h0
  have heq : rowCoefficient ports (13 : Fin 22) = (fun p => if p = ⟨(1, 4), by decide⟩ then (-ports 0) else if p = ⟨(1, 11), by decide⟩ then ports 0 else if p = ⟨(0, 1), by decide⟩ then (ports 1 * ports 0) else if p = ⟨(2, 11), by decide⟩ then (-1) else if p = ⟨(0, 2), by decide⟩ then ((-ports 1) - 2) else if p = ⟨(3, 11), by decide⟩ then (-1) else if p = ⟨(0, 3), by decide⟩ then ((-ports 1) - 1) else if p = ⟨(0, 4), by decide⟩ then (-ports 0) else if p = ⟨(0, 11), by decide⟩ then (ports 0 - 1) else if p = ⟨(0, 0), by decide⟩ then (((ports 1 * ports 0) - ports 1) - 2) else 0) := rfl
  rw [heq]
  dsimp only
  unfold envelope
  apply abs_ite_le
  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
  · apply abs_ite_le
    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
    · apply abs_ite_le
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
      · apply abs_ite_le
        · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
        · apply abs_ite_le
          · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
          · apply abs_ite_le
            · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
            · apply abs_ite_le
              · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
              · apply abs_ite_le
                · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
                · apply abs_ite_le
                  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
                  · apply abs_ite_le
                    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
                    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]

private theorem rowEnvelope_14 (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (p : PairIndex 31) : |rowCoefficient ports 14 p| ≤ envelope ports := by
  have hsq := sq_nonneg (ports 0)
  have hmf := mul_nonneg h3 h0
  have hkp := mul_nonneg h1 h0
  have heq : rowCoefficient ports (14 : Fin 22) = (fun p => if p = ⟨(5, 5), by decide⟩ then (-1) else if p = ⟨(0, 5), by decide⟩ then (-2) else if p = ⟨(0, 26), by decide⟩ then 1 else 0) := rfl
  rw [heq]
  dsimp only
  unfold envelope
  apply abs_ite_le
  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
  · apply abs_ite_le
    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
    · apply abs_ite_le
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]

private theorem rowEnvelope_15 (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (p : PairIndex 31) : |rowCoefficient ports 15 p| ≤ envelope ports := by
  have hsq := sq_nonneg (ports 0)
  have hmf := mul_nonneg h3 h0
  have hkp := mul_nonneg h1 h0
  have heq : rowCoefficient ports (15 : Fin 22) = (fun p => if p = ⟨(5, 8), by decide⟩ then (-1) else if p = ⟨(0, 5), by decide⟩ then (-1) else if p = ⟨(0, 8), by decide⟩ then (-1) else if p = ⟨(0, 20), by decide⟩ then 1 else if p = ⟨(0, 27), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then 1 else 0) := rfl
  rw [heq]
  dsimp only
  unfold envelope
  apply abs_ite_le
  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
  · apply abs_ite_le
    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
    · apply abs_ite_le
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
      · apply abs_ite_le
        · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
        · apply abs_ite_le
          · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
          · apply abs_ite_le
            · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
            · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]

private theorem rowEnvelope_16 (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (p : PairIndex 31) : |rowCoefficient ports 16 p| ≤ envelope ports := by
  have hsq := sq_nonneg (ports 0)
  have hmf := mul_nonneg h3 h0
  have hkp := mul_nonneg h1 h0
  have heq : rowCoefficient ports (16 : Fin 22) = (fun p => if p = ⟨(15, 15), by decide⟩ then (-1) else if p = ⟨(0, 15), by decide⟩ then (-2) else if p = ⟨(27, 27), by decide⟩ then 1 else if p = ⟨(0, 27), by decide⟩ then 2 else if p = ⟨(0, 28), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then 1 else 0) := rfl
  rw [heq]
  dsimp only
  unfold envelope
  apply abs_ite_le
  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
  · apply abs_ite_le
    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
    · apply abs_ite_le
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
      · apply abs_ite_le
        · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
        · apply abs_ite_le
          · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
          · apply abs_ite_le
            · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
            · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]

private theorem rowEnvelope_17 (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (p : PairIndex 31) : |rowCoefficient ports 17 p| ≤ envelope ports := by
  have hsq := sq_nonneg (ports 0)
  have hmf := mul_nonneg h3 h0
  have hkp := mul_nonneg h1 h0
  have heq : rowCoefficient ports (17 : Fin 22) = (fun p => if p = ⟨(7, 24), by decide⟩ then (-1) else if p = ⟨(0, 7), by decide⟩ then (-1) else if p = ⟨(0, 24), by decide⟩ then (-1) else if p = ⟨(0, 29), by decide⟩ then 1 else 0) := rfl
  rw [heq]
  dsimp only
  unfold envelope
  apply abs_ite_le
  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
  · apply abs_ite_le
    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
    · apply abs_ite_le
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
      · apply abs_ite_le
        · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
        · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]

private theorem rowEnvelope_18 (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (p : PairIndex 31) : |rowCoefficient ports 18 p| ≤ envelope ports := by
  have hsq := sq_nonneg (ports 0)
  have hmf := mul_nonneg h3 h0
  have hkp := mul_nonneg h1 h0
  have heq : rowCoefficient ports (18 : Fin 22) = (fun p => if p = ⟨(29, 29), by decide⟩ then (-1) else if p = ⟨(0, 29), by decide⟩ then (-2) else if p = ⟨(0, 30), by decide⟩ then 1 else 0) := rfl
  rw [heq]
  dsimp only
  unfold envelope
  apply abs_ite_le
  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
  · apply abs_ite_le
    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
    · apply abs_ite_le
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]

private theorem rowEnvelope_19 (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (p : PairIndex 31) : |rowCoefficient ports 19 p| ≤ envelope ports := by
  have hsq := sq_nonneg (ports 0)
  have hmf := mul_nonneg h3 h0
  have hkp := mul_nonneg h1 h0
  have heq : rowCoefficient ports (19 : Fin 22) = (fun p => if p = ⟨(26, 31), by decide⟩ then (-1) else if p = ⟨(0, 26), by decide⟩ then (-1) else if p = ⟨(0, 30), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then 1 else 0) := rfl
  rw [heq]
  dsimp only
  unfold envelope
  apply abs_ite_le
  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
  · apply abs_ite_le
    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
    · apply abs_ite_le
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
      · apply abs_ite_le
        · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
        · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]

private theorem rowEnvelope_20 (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (p : PairIndex 31) : |rowCoefficient ports 20 p| ≤ envelope ports := by
  have hsq := sq_nonneg (ports 0)
  have hmf := mul_nonneg h3 h0
  have hkp := mul_nonneg h1 h0
  have heq : rowCoefficient ports (20 : Fin 22) = (fun p => if p = ⟨(15, 15), by decide⟩ then 1 else if p = ⟨(0, 15), by decide⟩ then 2 else if p = ⟨(28, 30), by decide⟩ then (-1) else if p = ⟨(0, 28), by decide⟩ then (-1) else if p = ⟨(0, 30), by decide⟩ then (-1) else if p = ⟨(0, 0), by decide⟩ then (-1) else 0) := rfl
  rw [heq]
  dsimp only
  unfold envelope
  apply abs_ite_le
  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
  · apply abs_ite_le
    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
    · apply abs_ite_le
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
      · apply abs_ite_le
        · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
        · apply abs_ite_le
          · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
          · apply abs_ite_le
            · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
            · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]

private theorem rowEnvelope_21 (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (p : PairIndex 31) : |rowCoefficient ports 21 p| ≤ envelope ports := by
  have hsq := sq_nonneg (ports 0)
  have hmf := mul_nonneg h3 h0
  have hkp := mul_nonneg h1 h0
  have heq : rowCoefficient ports (21 : Fin 22) = (fun p => if p = ⟨(18, 22), by decide⟩ then 1 else if p = ⟨(0, 18), by decide⟩ then 2 else if p = ⟨(21, 22), by decide⟩ then (-1) else if p = ⟨(0, 21), by decide⟩ then (-1) else if p = ⟨(0, 0), by decide⟩ then 1 else 0) := rfl
  rw [heq]
  dsimp only
  unfold envelope
  apply abs_ite_le
  · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
  · apply abs_ite_le
    · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
    · apply abs_ite_le
      · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
      · apply abs_ite_le
        · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
        · apply abs_ite_le
          · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]
          · rw [abs_le]; constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]

/-- Every literal unweighted coefficient is bounded by the same envelope.
The per-row function equalities are checked by reflexivity against the frozen
native parent; no support or coefficient is supplied by an assumption. -/
theorem abs_rowCoefficient_le_envelope (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (k : Fin 22) (p : PairIndex 31) : |rowCoefficient ports k p| ≤ envelope ports := by
  fin_cases k
  · exact rowEnvelope_0 ports h0 h1 h2 h3 p
  · exact rowEnvelope_1 ports h0 h1 h2 h3 p
  · exact rowEnvelope_2 ports h0 h1 h2 h3 p
  · exact rowEnvelope_3 ports h0 h1 h2 h3 p
  · exact rowEnvelope_4 ports h0 h1 h2 h3 p
  · exact rowEnvelope_5 ports h0 h1 h2 h3 p
  · exact rowEnvelope_6 ports h0 h1 h2 h3 p
  · exact rowEnvelope_7 ports h0 h1 h2 h3 p
  · exact rowEnvelope_8 ports h0 h1 h2 h3 p
  · exact rowEnvelope_9 ports h0 h1 h2 h3 p
  · exact rowEnvelope_10 ports h0 h1 h2 h3 p
  · exact rowEnvelope_11 ports h0 h1 h2 h3 p
  · exact rowEnvelope_12 ports h0 h1 h2 h3 p
  · exact rowEnvelope_13 ports h0 h1 h2 h3 p
  · exact rowEnvelope_14 ports h0 h1 h2 h3 p
  · exact rowEnvelope_15 ports h0 h1 h2 h3 p
  · exact rowEnvelope_16 ports h0 h1 h2 h3 p
  · exact rowEnvelope_17 ports h0 h1 h2 h3 p
  · exact rowEnvelope_18 ports h0 h1 h2 h3 p
  · exact rowEnvelope_19 ports h0 h1 h2 h3 p
  · exact rowEnvelope_20 ports h0 h1 h2 h3 p
  · exact rowEnvelope_21 ports h0 h1 h2 h3 p

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
  have hfour : (16 : ℤ) = 2 ^ 4 := by decide
  have he : 592884 = 590069 + 2815 := by decide
  rw [he, pow_add, hfour]
  have hsmall : (2 : ℤ) ^ 4 ≤ 2 ^ 2815 :=
    pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) (by decide : 4 ≤ 2815)
  have hpos : (0 : ℤ) ≤ 2 ^ 590069 := pow_nonneg (by decide) _
  calc
    2 ^ 4 * (2 : ℤ) ^ 590069 = 2 ^ 590069 * 2 ^ 4 := by rw [mul_comm]
    _ ≤ 2 ^ 590069 * 2 ^ 2815 := mul_le_mul_of_nonneg_left hsmall hpos

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

-- Review-only axiom audit, not part of integration diff.
#print axioms DiophantineConsistency.NativeCoefficientBounds.abs_rowCoefficient_le_envelope
#print axioms DiophantineConsistency.NativeCoefficientBounds.weighted_rowCoefficient_lt_published
#print axioms DiophantineConsistency.NativeCoefficientBounds.published_large_scale
