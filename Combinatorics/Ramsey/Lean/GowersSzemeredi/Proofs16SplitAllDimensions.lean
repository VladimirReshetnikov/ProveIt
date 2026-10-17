import GowersSzemeredi.Proofs16SplitStepBounds
import GowersSzemeredi.Proofs16AllDimensions

/-! Split uniform classes in every dimension, with `O(2^k)` logarithms
(Notes L.7, F3a).

* `splitStepA_le`: `splitStepA k a ≤ 2^(k+5)·a²`.
* `splitStepD_le`: `splitStepD k a D ≤ 2^(k+6)·a(a+D)·P + T`, with
  `P = stepP k` and `T = stepT k`. There is no `D²` term: the parameter degree
  enters the next class linearly, multiplied by `a` and `P`.
* `split_invariant_succ`: the step preserves the invariants
  `2^(k+6)·a_k ≤ 2^(35·2^k)` and `D_k ≤ 2^(75·2^k)`. At `k = 2` they hold for
  `a = D = 2^132`.
* `splitPair k = (a_k, D_k)`: the degrees, with `split_pair_bounds`.
* `splitUniformClass_all`: a split class in every dimension `k ≥ 2`.

So `log a_k ≤ 35·2^k` and `log D_k ≤ 75·2^k`, against `k·2^(k+6)` for the
power classes of Notes L.6. This is the budget Theorem 18.2 at every length
needs (Notes L.7).

`splitStepD_le`, `splitUniformClass_all`, `split_invariant_succ` and
`split_pair_bounds` are in `Proofs16SplitAllDimensionsSide`, outside the final
route. -/
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
  subst hA4
  have hs1 : 1 ≤ a + D := by omega
  have hsA : 1 ≤ (a + D) * A := Nat.mul_le_mul hs1 hA
  -- `Q = (a+D)·P·A ≤ R = a(a+D)·P·A`
  have hPQ : P * 1 ≤ P * ((a + D) * A) := Nat.mul_le_mul_left P hsA
  have hQR : 1 * ((a + D) * P * A) ≤ a * ((a + D) * P * A) := Nat.mul_le_mul_right _ ha
  have hsP : (a + D) * P * 1 ≤ (a + D) * P * A := Nat.mul_le_mul_left _ hA
  have hs1P : (a + D) * 1 ≤ (a + D) * P := Nat.mul_le_mul_left _ (by omega)
  have haS : a ≤ a + D := by omega
  have hDS : D ≤ a + D := by omega
  have h1 : Y ≤ 2 * (a + D) * P := by
    have e1 := Nat.mul_le_mul_left a (show P + 1 ≤ 2 * P by omega)
    have e2 := Nat.mul_le_mul_left D (show P + k + 6 ≤ 2 * P by omega)
    rw [hY]; nlinarith only [e1, e2]
  have h1A : Y * A ≤ 2 * (a + D) * P * A := Nat.mul_le_mul_right A h1
  have h2 : SW ≤ 4 * ((a + D) * P * A) := by
    rw [hSW]; nlinarith only [h1A, hPQ, hkP]
  have h3a : P + SW + 1 ≤ 6 * ((a + D) * P * A) := by nlinarith only [h2, hPQ, hkP]
  have h3b : a * (P + SW + 1) ≤ a * (6 * ((a + D) * P * A)) := Nat.mul_le_mul_left a h3a
  have h3c : D * (P + 5) ≤ (a + D) * (2 * P) := Nat.mul_le_mul hDS (by omega)
  have h3 : PbW ≤ 8 * (a * ((a + D) * P * A)) := by
    rw [hPb]; nlinarith only [h3b, h3c, hsP, hQR]
  have hC : CW ≤ 26 * (a * ((a + D) * P * A)) := by
    rw [hCW]; nlinarith only [h2, h3, hPQ, hQR, hkP]
  have hEb' : EbW ≤ 2 * (a + D) * P := by
    have e1 := Nat.mul_le_mul_left a (show P + 1 ≤ 2 * P by omega)
    have e2 := Nat.mul_le_mul_left D (show P + 6 ≤ 2 * P by omega)
    rw [hEb]; nlinarith only [e1, e2]
  have hEbA : EbW * A ≤ 2 * (a + D) * P * A := Nat.mul_le_mul_right A hEb'
  have h4A : 4 * A ≤ P * A := Nat.mul_le_mul_right A (by omega)
  have hPA : 1 * (P * A) ≤ (a + D) * (P * A) := Nat.mul_le_mul_right _ hs1
  have hEr' : ErW ≤ 3 * ((a + D) * P * A) := by
    rw [hEr]; nlinarith only [h1A, h4A, hPA]
  have hBq' : BqW ≤ 13 * ((a + D) * P * A) := by
    rw [hBq]; nlinarith only [hEbA, h4A, hPA, hA]
  have hL' : LW ≤ 18 * ((a + D) * P * A) := by
    rw [hL]; nlinarith only [hBq', hEr', hEb', hsP]
  have hZ' : ZW ≤ T + 4 * ((a + D) * P * A) := by
    rw [hZ]; nlinarith only [hEb', hsP, hs1P, haS, hkP, hPQ]
  have hE' : EW ≤ T + 31 * (a * ((a + D) * P * A)) := by
    rw [hE]; nlinarith only [hZ', hL', h3, hQR, hPQ, hkP]
  have hTh' : Th ≤ 4 * ((a + D) * P * A) := by
    have e1 := Nat.mul_le_mul_left D (show P + 2 ≤ 2 * P by omega)
    rw [hTh]; nlinarith only [e1, hDS, hsP, hPQ, hkP, Nat.mul_le_mul_right P hDS]
  nlinarith only [hC, hE', hTh', hQR]

/-! ### The invariants -/

/-! ### Every dimension -/

/-- The seed degree at dimension `2`. -/
def splitSeed : Nat := 2 ^ 132

/-- The degrees `(a_k, D_k)` of the split class in dimension `k`; constant
below dimension `2`. -/
def splitPair : Nat → Nat × Nat
  | 0 => (splitSeed, splitSeed)
  | k + 1 => if k < 2 then (splitSeed, splitSeed)
      else (splitStepA k (splitPair k).1, splitStepD k (splitPair k).1 (splitPair k).2)

theorem splitPair_two : splitPair 2 = (splitSeed, splitSeed) := by
  rw [splitPair, if_pos (by norm_num)]

theorem splitPair_succ {k : Nat} (hk : 2 ≤ k) :
    splitPair (k + 1) = (splitStepA k (splitPair k).1, splitStepD k (splitPair k).1 (splitPair k).2) := by
  rw [splitPair, if_neg (by omega)]

end LeanProofs.GowersSzemeredi
