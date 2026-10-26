import DiophantineConsistency.SidonPositions
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

/-! ISOLATED VERIFICATION: rowCoefficient and envelope copied byte-for-byte
from ProveIt commit 60e9c5d620c6c387d932876cfa2d9376f64ea56c.
This file checks refactoring mathematics without loading unrelated finite
certificates from NativeQuadraticParent. See extraction_manifest.json. -/

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

namespace DiophantineConsistency.NativeQuadraticParent
open SidonPositions
variable {R : Type*} [CommRing R]
def rowCoefficient (ports : Fin 4 → R) : Fin 22 → PairIndex 31 → R :=
  ![(fun p => if p = ⟨(1, 1), by decide⟩ then (-(ports 0 ^ 2)) else if p = ⟨(0, 1), by decide⟩ then (((-2) * (ports 0 ^ 2)) - (2 * ports 0)) else if p = ⟨(0, 25), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then (((-(ports 0 ^ 2)) - (2 * ports 0)) + 1) else 0),
    (fun p => if p = ⟨(1, 25), by decide⟩ then (-ports 0) else if p = ⟨(0, 1), by decide⟩ then ((-2) * ports 0) else if p = ⟨(0, 17), by decide⟩ then 1 else if p = ⟨(0, 25), by decide⟩ then ((-ports 0) - 1) else if p = ⟨(0, 0), by decide⟩ then (((-2) * ports 0) - 1) else 0),
    (fun p => if p = ⟨(1, 11), by decide⟩ then (-ports 0) else if p = ⟨(0, 1), by decide⟩ then (-ports 0) else if p = ⟨(0, 11), by decide⟩ then ((-ports 0) - 1) else if p = ⟨(0, 22), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then (-ports 0) else 0),
    (fun p => if p = ⟨(10, 17), by decide⟩ then (-1) else if p = ⟨(0, 10), by decide⟩ then (-1) else if p = ⟨(0, 17), by decide⟩ then (-1) else if p = ⟨(0, 18), by decide⟩ then (-1) else if p = ⟨(0, 21), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then (-1) else 0),
    (fun p => if p = ⟨(13, 18), by decide⟩ then 1 else if p = ⟨(13, 21), by decide⟩ then (-1) else if p = ⟨(0, 13), by decide⟩ then (-1) else if p = ⟨(14, 18), by decide⟩ then 1 else if p = ⟨(14, 21), by decide⟩ then (-1) else if p = ⟨(0, 18), by decide⟩ then 2 else if p = ⟨(0, 20), by decide⟩ then 1 else if p = ⟨(0, 21), by decide⟩ then (-2) else 0),
    (fun p => if p = ⟨(13, 18), by decide⟩ then 1 else if p = ⟨(0, 14), by decide⟩ then (-1) else if p = ⟨(18, 20), by decide⟩ then (-1) else if p = ⟨(0, 19), by decide⟩ then 1 else if p = ⟨(0, 20), by decide⟩ then (-1) else if p = ⟨(0, 0), by decide⟩ then (-1) else 0),
    (fun p => if p = ⟨(12, 12), by decide⟩ then 1 else if p = ⟨(0, 12), by decide⟩ then 2 else if p = ⟨(13, 19), by decide⟩ then 1 else if p = ⟨(0, 13), by decide⟩ then 1 else if p = ⟨(14, 19), by decide⟩ then 1 else if p = ⟨(0, 14), by decide⟩ then 1 else if p = ⟨(19, 19), by decide⟩ then (-1) else if p = ⟨(0, 0), by decide⟩ then 1 else 0),
    (fun p => if p = ⟨(16, 21), by decide⟩ then (-4) else if p = ⟨(0, 16), by decide⟩ then (-7) else if p = ⟨(20, 21), by decide⟩ then (-1) else if p = ⟨(0, 20), by decide⟩ then (-1) else if p = ⟨(0, 21), by decide⟩ then (-5) else if p = ⟨(0, 22), by decide⟩ then (-1) else if p = ⟨(0, 23), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then (-8) else 0),
    (fun p => if p = ⟨(21, 21), by decide⟩ then (-1) else if p = ⟨(0, 21), by decide⟩ then (-6) else if p = ⟨(0, 31), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then (-7) else 0),
    (fun p => if p = ⟨(20, 20), by decide⟩ then (-1) else if p = ⟨(0, 20), by decide⟩ then (-2) else if p = ⟨(0, 24), by decide⟩ then 1 else 0),
    (fun p => if p = ⟨(23, 23), by decide⟩ then 1 else if p = ⟨(0, 23), by decide⟩ then 2 else if p = ⟨(24, 31), by decide⟩ then (-1) else if p = ⟨(0, 24), by decide⟩ then (-1) else if p = ⟨(0, 31), by decide⟩ then (-1) else if p = ⟨(0, 0), by decide⟩ then (-1) else 0),
    (fun p => if p = ⟨(6, 18), by decide⟩ then (-1) else if p = ⟨(0, 6), by decide⟩ then (-1) else if p = ⟨(9, 20), by decide⟩ then (-1) else if p = ⟨(0, 9), by decide⟩ then (-1) else if p = ⟨(0, 13), by decide⟩ then 1 else if p = ⟨(0, 14), by decide⟩ then 1 else if p = ⟨(0, 18), by decide⟩ then (-1) else if p = ⟨(0, 20), by decide⟩ then (-1) else if p = ⟨(0, 27), by decide⟩ then 1 else 0),
    (fun p => if p = ⟨(1, 1), by decide⟩ then (((-ports 3) * ports 0) + (ports 0 ^ 2)) else if p = ⟨(1, 2), by decide⟩ then (-ports 0) else if p = ⟨(1, 17), by decide⟩ then (-ports 0) else if p = ⟨(1, 25), by decide⟩ then ports 0 else if p = ⟨(0, 1), by decide⟩ then (((((-ports 2) - ((2 * ports 3) * ports 0)) - ports 3) + (2 * (ports 0 ^ 2))) + ports 0) else if p = ⟨(2, 17), by decide⟩ then 1 else if p = ⟨(2, 25), by decide⟩ then (-1) else if p = ⟨(0, 2), by decide⟩ then ((-ports 0) - 1) else if p = ⟨(3, 25), by decide⟩ then (-1) else if p = ⟨(0, 3), by decide⟩ then (-1) else if p = ⟨(9, 20), by decide⟩ then 1 else if p = ⟨(0, 9), by decide⟩ then 1 else if p = ⟨(0, 17), by decide⟩ then (-ports 0) else if p = ⟨(0, 20), by decide⟩ then 1 else if p = ⟨(0, 25), by decide⟩ then (ports 0 - 1) else if p = ⟨(0, 27), by decide⟩ then (-1) else if p = ⟨(0, 0), by decide⟩ then ((((((-ports 2) - (ports 3 * ports 0)) - ports 3) + (ports 0 ^ 2)) + ports 0) - 1) else 0),
    (fun p => if p = ⟨(1, 4), by decide⟩ then (-ports 0) else if p = ⟨(1, 11), by decide⟩ then ports 0 else if p = ⟨(0, 1), by decide⟩ then (ports 1 * ports 0) else if p = ⟨(2, 11), by decide⟩ then (-1) else if p = ⟨(0, 2), by decide⟩ then ((-ports 1) - 2) else if p = ⟨(3, 11), by decide⟩ then (-1) else if p = ⟨(0, 3), by decide⟩ then ((-ports 1) - 1) else if p = ⟨(0, 4), by decide⟩ then (-ports 0) else if p = ⟨(0, 11), by decide⟩ then (ports 0 - 1) else if p = ⟨(0, 0), by decide⟩ then (((ports 1 * ports 0) - ports 1) - 2) else 0),
    (fun p => if p = ⟨(5, 5), by decide⟩ then (-1) else if p = ⟨(0, 5), by decide⟩ then (-2) else if p = ⟨(0, 26), by decide⟩ then 1 else 0),
    (fun p => if p = ⟨(5, 8), by decide⟩ then (-1) else if p = ⟨(0, 5), by decide⟩ then (-1) else if p = ⟨(0, 8), by decide⟩ then (-1) else if p = ⟨(0, 20), by decide⟩ then 1 else if p = ⟨(0, 27), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then 1 else 0),
    (fun p => if p = ⟨(15, 15), by decide⟩ then (-1) else if p = ⟨(0, 15), by decide⟩ then (-2) else if p = ⟨(27, 27), by decide⟩ then 1 else if p = ⟨(0, 27), by decide⟩ then 2 else if p = ⟨(0, 28), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then 1 else 0),
    (fun p => if p = ⟨(7, 24), by decide⟩ then (-1) else if p = ⟨(0, 7), by decide⟩ then (-1) else if p = ⟨(0, 24), by decide⟩ then (-1) else if p = ⟨(0, 29), by decide⟩ then 1 else 0),
    (fun p => if p = ⟨(29, 29), by decide⟩ then (-1) else if p = ⟨(0, 29), by decide⟩ then (-2) else if p = ⟨(0, 30), by decide⟩ then 1 else 0),
    (fun p => if p = ⟨(26, 31), by decide⟩ then (-1) else if p = ⟨(0, 26), by decide⟩ then (-1) else if p = ⟨(0, 30), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then 1 else 0),
    (fun p => if p = ⟨(15, 15), by decide⟩ then 1 else if p = ⟨(0, 15), by decide⟩ then 2 else if p = ⟨(28, 30), by decide⟩ then (-1) else if p = ⟨(0, 28), by decide⟩ then (-1) else if p = ⟨(0, 30), by decide⟩ then (-1) else if p = ⟨(0, 0), by decide⟩ then (-1) else 0),
    (fun p => if p = ⟨(18, 22), by decide⟩ then 1 else if p = ⟨(0, 18), by decide⟩ then 2 else if p = ⟨(21, 22), by decide⟩ then (-1) else if p = ⟨(0, 21), by decide⟩ then (-1) else if p = ⟨(0, 0), by decide⟩ then 1 else 0)]

end DiophantineConsistency.NativeQuadraticParent

namespace DiophantineConsistency.NativeCoefficientBounds
open SidonPositions NativeQuadraticParent

def envelope (ports : Fin 4 → ℤ) : ℤ :=
  2 * ports 0 ^ 2 + 2 * ports 3 * ports 0 + ports 2 + ports 3 +
    2 * ports 0 + ports 1 * ports 0 + ports 1 + 8


private theorem abs_ite_le {P : Prop} [Decidable P] {a b E : ℤ}
    (ha : |a| ≤ E) (hb : |b| ≤ E) : |if P then a else b| ≤ E := by
  by_cases h : P
  · simpa only [if_pos h] using ha
  · simpa only [if_neg h] using hb

theorem abs_rowCoefficient_le_envelope (ports : Fin 4 → ℤ)
    (h0 : 0 ≤ ports 0) (h1 : 0 ≤ ports 1) (h2 : 0 ≤ ports 2) (h3 : 0 ≤ ports 3)
    (k : Fin 22) (p : PairIndex 31) : |rowCoefficient ports k p| ≤ envelope ports := by
  have hsq := sq_nonneg (ports 0)
  have hmf := mul_nonneg h3 h0
  have hkp := mul_nonneg h1 h0
  unfold envelope
  fin_cases k <;> dsimp only [rowCoefficient, Fin.reduceFinMk, Matrix.cons_val]
  all_goals repeat' apply abs_ite_le
  all_goals
    rw [abs_le]
    constructor <;> linarith only [h0, h1, h2, h3, hsq, hmf, hkp]

#print axioms abs_rowCoefficient_le_envelope
end DiophantineConsistency.NativeCoefficientBounds

namespace DiophantineConsistency.NativeNinePolynomial52
open NativeQuadraticParent
variable {A B : Type*} [CommRing A] [CommRing B]

private theorem mapIte (f : A →+* B) (p : Prop) [Decidable p] (a b : A) :
    f (if p then a else b) = if p then f a else f b := by
  by_cases h : p <;> simp only [h, if_true, if_false]

theorem map_rowCoefficient (f : A →+* B) (ports : Fin 4 → A)
    (k : Fin 22) (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports k p) = rowCoefficient (fun i => f (ports i)) k p := by
  fin_cases k <;> dsimp only [rowCoefficient, Fin.reduceFinMk, Matrix.cons_val]
  all_goals
    simp only [mapIte, map_add, map_sub, map_mul, map_pow,
      map_neg, map_ofNat, map_one, map_zero]

#print axioms map_rowCoefficient
end DiophantineConsistency.NativeNinePolynomial52
