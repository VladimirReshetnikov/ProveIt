import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Scalar rank bounds for the fourteen-variable first-Pell carrier

These are the rank and transport expressions printed in `equation.tex`.
The transport unit first forces the free carrier positive. Only then do
the fixed-port inequalities bound the rank below the first-Pell modulus.
No machine interpretation or sign of the first Pell root is assumed.
-/

namespace DiophantineConsistency.CarrierRankBounds

def rank (q J MC MF F alpha : ℤ) : ℤ :=
  ((q - 1) * (q - F) + alpha) * (q ^ 2 - 1) + (MC + q * MF) * J

theorem carrier_pos_of_transport {q K w F alpha z : ℤ}
    (hq : 1 < q) (hK : 0 < K) (hw : 0 < w) (hF : 0 < F) (hz : 0 < z)
    (ht : (K + w) * (q - F - alpha) + (q - F) - z * (q - 1) = 1) :
    0 < q - F - alpha := by
  by_contra hn
  have hC : q - F - alpha ≤ 0 := by omega
  have hp : (K + w) * (q - F - alpha) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by omega) hC
  have hz1 : 1 ≤ z := hz
  have hmul := mul_le_mul_of_nonneg_right hz1 (by omega : 0 ≤ q - 1)
  nlinarith only [ht, hp, hmul, hF]

theorem rank_bounds {q beta J MC MF F alpha : ℤ}
    (hq : 3 ≤ q) (hJ : 0 < J) (hbeta : beta * J = q - 1)
    (hMC : 0 < MC) (hMCb : MC < beta) (hMF : 0 < MF) (hMFb : MF < 2 * beta)
    (hF : 0 < F) (halpha : 0 < alpha) (hC : 0 < q - F - alpha) :
    q * (q ^ 2 - 1) < rank q J MC MF F alpha ∧
      rank q J MC MF F alpha < q ^ 4 - q ^ 3 := by
  let u := q - F
  let G := (q - 1) * u + alpha
  let M := (MC + q * MF) * J
  have hu : 2 ≤ u := by dsimp [u]; omega
  have huq : u ≤ q - 1 := by dsimp [u]; omega
  have hau : alpha ≤ u - 1 := by dsimp [u]; omega
  have hGlo : 2 * q - 1 ≤ G := by
    have hm := mul_le_mul_of_nonneg_left hu (by omega : 0 ≤ q - 1)
    dsimp [G]
    nlinarith only [hm, halpha]
  have hGhi : G ≤ q ^ 2 - q - 1 := by
    have hm := mul_le_mul_of_nonneg_left huq (by omega : 0 ≤ q)
    dsimp [G]
    nlinarith only [hm, hau]
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hMCJ : MC * J < q - 1 := by
    simpa only [hbeta] using mul_lt_mul_of_pos_right hMCb hJ
  have hMFJ : MF * J < 2 * (q - 1) := by
    calc MF * J < (2 * beta) * J := mul_lt_mul_of_pos_right hMFb hJ
      _ = 2 * (q - 1) := by rw [mul_assoc, hbeta]
  have hMhi : M < (1 + 2 * q) * (q - 1) := by
    have hm := mul_lt_mul_of_pos_left hMFJ (by omega : 0 < q)
    dsimp [M]
    nlinarith only [hm, hMCJ]
  have hq2 : 0 < q ^ 2 - 1 := by nlinarith only [hq]
  have hlow := mul_le_mul_of_nonneg_right hGlo hq2.le
  have hhigh := mul_le_mul_of_nonneg_right hGhi hq2.le
  have hgap : 0 < (q - 1) * (q ^ 2 - 1) := mul_pos (by omega) hq2
  have hr : rank q J MC MF F alpha = G * (q ^ 2 - 1) + M := rfl
  constructor
  · rw [hr]
    nlinarith only [hlow, hMpos, hgap]
  · rw [hr]
    nlinarith only [hhigh, hMhi]

/-- The two strict inequalities needed to restore the omitted positive
quotient are derived from the actual rank, rather than supplied as a
native-window or Pell-index premise. -/
theorem rank_window {q beta J MC MF F alpha w s : ℤ}
    (hq : 3 ≤ q) (hJ : 0 < J) (hbeta : beta * J = q - 1)
    (hMC : 0 < MC) (hMCb : MC < beta) (hMF : 0 < MF) (hMFb : MF < 2 * beta)
    (hF : 0 < F) (halpha : 0 < alpha) (hC : 0 < q - F - alpha)
    (hw : 0 < w) (hs : 0 < s) :
    1 < rank q J MC MF F alpha ∧ rank q J MC MF F alpha + 2 < w * s * q ^ 4 := by
  obtain ⟨hlo, hhi⟩ := rank_bounds hq hJ hbeta hMC hMCb hMF hMFb hF halpha hC
  have hq2 : 8 ≤ q ^ 2 - 1 := by nlinarith only [hq]
  have hq3 : 3 ≤ q ^ 3 := by nlinarith only [hq, sq_nonneg (q - 1)]
  have hq4 : 0 ≤ q ^ 4 := by positivity
  have hws : 1 ≤ w * s := Int.mul_pos hw hs
  have hE := mul_le_mul_of_nonneg_right hws hq4
  have hlow := mul_le_mul (by omega : (3 : ℤ) ≤ q) hq2 (by norm_num : (0 : ℤ) ≤ 8)
    (by omega : 0 ≤ q)
  constructor
  · nlinarith only [hlo, hlow]
  · nlinarith only [hhi, hq3, hE]

end DiophantineConsistency.CarrierRankBounds
