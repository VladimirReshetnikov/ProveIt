import GowersSzemeredi.Proofs16SplitStepBounds
import GowersSzemeredi.Proofs16AllDimensions

/-! Degree bounds for the split step (Notes L.7, F3a): `splitStepA_le`, the
polynomial `split_degree_poly` behind the parameter-degree bound, and the
dimension-two seed `splitSeed = 2^132`.

The split classes in every dimension (`splitUniformClass_all`) are in
`Proofs16SplitAllDimensionsSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### The step degrees -/

theorem splitStepA_le {k a : Nat} (ha : 1 ≤ a) : splitStepA k a ≤ 2 ^ (k + 5) * (a * a) := by
  have hA : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h2 : 2 ^ (k + 2) = 2 ^ k * 4 := by rw [pow_add]; norm_num
  have h5 : 2 ^ (k + 5) = 2 ^ k * 32 := by rw [pow_add]; norm_num
  unfold splitStepA sCountN sExpN sLN sBqN sErN sPbN sSN sQrN
  rw [h2, h5]
  set A := 2 ^ k
  have haa : a ≤ a * a := Nat.le_mul_of_pos_left _ ha
  nlinarith [Nat.mul_le_mul hA haa, Nat.mul_le_mul hA ha, Nat.zero_le (A * a), Nat.zero_le (A * (a * a))]

/-- The polynomial behind `splitStepD_le`, over plain variables. -/
theorem split_degree_poly {a D P A A4 T k Y SW PbW CW EbW ErW BqW LW ZW EW Th : Nat}
    (ha : 1 ≤ a) (hD : 1 ≤ D) (hA : 1 ≤ A) (hkP : k + 9 ≤ P) (hA4 : A4 = A * 4)
    (hY : Y = a * (P + 1) + D * (P + k + 6)) (hSW : SW = Y * A + P + 8)
    (hPb : PbW = a * (P + SW + 1) + D * (P + 5)) (hCW : CW = P + 1 + 2 * SW + 2 * PbW)
    (hEb : EbW = a * (P + 1) + D * (P + 6)) (hEr : ErW = (Y + 4) * A)
    (hBq : BqW = 4 + (EbW + 1) * A4) (hL : LW = BqW + (ErW + EbW))
    (hZ : ZW = T + a + EbW + 7) (hE : EW = ZW + LW + PbW + 6)
    (hTh : Th = D * (P + 2) + P + 2) :
    CW + EW + Th ≤ A * 64 * (a * (a + D)) * P + T := by
  -- Substitute the definitions and shift `a, D, A ≥ 1`, `P ≥ k + 9` to their lower bounds:
  -- every coefficient of the expanded difference is then nonnegative.
  subst_vars
  obtain ⟨x, rfl⟩ : ∃ x, a = x + 1 := ⟨a - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, A = b + 1 := ⟨A - 1, by omega⟩
  obtain ⟨p, rfl⟩ : ∃ p, P = k + 9 + p := ⟨P - (k + 9), by omega⟩
  ring_nf
  omega

/-! ### Every dimension -/

/-- The seed degree at dimension `2`. -/
def splitSeed : Nat := 2 ^ 132

end LeanProofs.GowersSzemeredi
