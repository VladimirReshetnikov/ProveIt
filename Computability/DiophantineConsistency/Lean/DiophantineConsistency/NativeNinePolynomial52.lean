import DiophantineConsistency.NativeNineFinalizer52
import DiophantineConsistency.NativeQuadraticParent
import DiophantineConsistency.NativeQuadraticPositions
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Literal package-52 nine-variable polynomial data

The variable order is b,g,h,s,w,phi,i,j,n. All arithmetic below is over an
arbitrary coefficient ring. Integer truncation and selected existential
polynomials do not occur in the recipe. The MvPolynomial specialization uses
the library's noncomputable finite-support operations; integer evaluation
is ordinary computable arithmetic.
-/

namespace DiophantineConsistency.NativeNinePolynomial52

open NativeQuadraticParent NativeQuadraticPositions SelectiveQuadraticCoding
open scoped BigOperators

variable {A B : Type*} [CommRing A] [CommRing B]

private theorem mapIte (f : A →+* B) (p : Prop) [Decidable p] (a b : A) :
    f (if p then a else b) = if p then f a else f b := by
  by_cases h : p <;> simp only [h, if_true, if_false]

/-- The exact ratio-register schedule, with supplied source quantities. -/
def ratioValue (R N b g cap h s w phi i j n : A) : A :=
  let U := N ^ 2 * w
  let Y := N ^ 2 * s
  let M := R * Y
  let P := 2 * M ^ 2 * U
  let K := R + 1 + h * (P - 1)
  let a := M * (U + 1)
  let b1 := 2 * R + 1
  let W := b * w
  let C := b1 + W + phi
  let J := 4 * a - 5
  let Q := 3 * W * C - 2 * (W ^ 2 - 1)
  let D := (a ^ 2 - 1) * C ^ 2 + 1
  let E := i * J * D * C ^ 2
  let F := (a ^ 2 - 1) * E ^ 2 + 1
  let G := a + F * (C * D + 1 - a)
  let H := C + F * (b1 + j * C)
  let I := (G ^ 2 - 1) * H ^ 2 + 1
  let k := i * J * C
  let V0 := P * K
  let V1 := k * (8 * D ^ 2 - 4 * D - 1) * G * H
  let m := K ^ 2 * cap - 4 * (C - K * Y) ^ 2 * cap - 8 * g * K ^ 2
  let omega := J * m
  let theta := J * n + Q - omega * (V0 + V1)
  NearSquareFinalizer.norm theta omega ((P ^ 2 - 1) * K ^ 2 + 1) 8 (D * F * I)

theorem ratioValue_nat (R N b g cap : ℕ) (v : NativeNineRatio52.NewVars) (n : ℕ) :
    ratioValue (R : ℤ) N b g cap v.h v.s v.w v.phi v.i v.j n =
      v.finalValue R N b g cap n := rfl

def sourceBase (height b : A) : A := 4096 * height * b ^ 2

/-- The 136 actual weighted source records, as a finite arithmetic sum. -/
def kernelValue (ports : Fin 4 → A) (base : A) : A :=
  ∑ k, ∑ p ∈ rowSupport k,
    QuadraticCoding.correction p * rowCoefficient ports k p *
      base ^ (target k - pairWeight SelectiveCertificate52.weights p)

def sourceN (base : A) : A := base ^ 175 * (4 * base ^ 7865)

def sourceCap (base b : A) : A := 32 * b * base ^ 174

def sourceHigh (ports : Fin 4 → A) (base g : A) : A :=
  2 * (base ^ 81 + g) ^ 2 * kernelValue ports base +
    base * ∑ i ∈ Finset.range 7865, base ^ i

def sourceMask (base b : A) : A :=
  base ^ 175 - 1 - (b - 1) * ∑ i : Fin 31, base ^ SelectiveCertificate52.weights i.succ

def sourceHighMask (base : A) : A := (base - 2) * ∑ k : Fin 22, base ^ target k

/-- The integer-polynomial central code, without natural subtraction or ToNat. -/
def sourceRank (ports : Fin 4 → A) (base b g : A) : A :=
  let N := sourceN base
  let S := g + sourceHigh ports base g * base ^ 175
  let T := sourceMask base b + sourceHighMask base * base ^ 175
  (N - 1) * ((S + T + 1) * N + T + 1)

/-- The literal full nine-variable evaluator. The supplied height is the
coefficient majorant, so the radix scale is 4096 times that height. -/
def value (ports : Fin 4 → A) (height : A) (x : Fin 9 → A) : A :=
  let base := sourceBase height (x 0)
  ratioValue (sourceRank ports base (x 0) (x 1)) (sourceN base) (x 0) (x 1)
    (sourceCap base (x 0)) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)

set_option maxHeartbeats 400000 in
set_option maxRecDepth 16000 in
set_option linter.unusedSimpArgs false in
private theorem mapRowCoefficient0 (f : A →+* B) (ports : Fin 4 → A)
    (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports 0 p) = rowCoefficient (fun i => f (ports i)) 0 p := by
  have hleft : rowCoefficient ports 0 = (fun p => if p = ⟨(1, 1), by decide⟩ then (-(ports 0 ^ 2)) else if p = ⟨(0, 1), by decide⟩ then (((-2) * (ports 0 ^ 2)) - (2 * ports 0)) else if p = ⟨(0, 25), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then (((-(ports 0 ^ 2)) - (2 * ports 0)) + 1) else 0) := by unfold rowCoefficient; rfl
  have hright : rowCoefficient (fun i => f (ports i)) 0 = (fun p => if p = ⟨(1, 1), by decide⟩ then (-((fun i => f (ports i)) 0 ^ 2)) else if p = ⟨(0, 1), by decide⟩ then (((-2) * ((fun i => f (ports i)) 0 ^ 2)) - (2 * (fun i => f (ports i)) 0)) else if p = ⟨(0, 25), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then (((-((fun i => f (ports i)) 0 ^ 2)) - (2 * (fun i => f (ports i)) 0)) + 1) else 0) := by unfold rowCoefficient; rfl
  rw [hleft, hright]
  dsimp only
  simp only [mapIte, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 16000 in
set_option linter.unusedSimpArgs false in
private theorem mapRowCoefficient1 (f : A →+* B) (ports : Fin 4 → A)
    (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports 1 p) = rowCoefficient (fun i => f (ports i)) 1 p := by
  have hleft : rowCoefficient ports 1 = (fun p => if p = ⟨(1, 25), by decide⟩ then (-ports 0) else if p = ⟨(0, 1), by decide⟩ then ((-2) * ports 0) else if p = ⟨(0, 17), by decide⟩ then 1 else if p = ⟨(0, 25), by decide⟩ then ((-ports 0) - 1) else if p = ⟨(0, 0), by decide⟩ then (((-2) * ports 0) - 1) else 0) := by unfold rowCoefficient; rfl
  have hright : rowCoefficient (fun i => f (ports i)) 1 = (fun p => if p = ⟨(1, 25), by decide⟩ then (-(fun i => f (ports i)) 0) else if p = ⟨(0, 1), by decide⟩ then ((-2) * (fun i => f (ports i)) 0) else if p = ⟨(0, 17), by decide⟩ then 1 else if p = ⟨(0, 25), by decide⟩ then ((-(fun i => f (ports i)) 0) - 1) else if p = ⟨(0, 0), by decide⟩ then (((-2) * (fun i => f (ports i)) 0) - 1) else 0) := by unfold rowCoefficient; rfl
  rw [hleft, hright]
  dsimp only
  simp only [mapIte, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 16000 in
set_option linter.unusedSimpArgs false in
private theorem mapRowCoefficient2 (f : A →+* B) (ports : Fin 4 → A)
    (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports 2 p) = rowCoefficient (fun i => f (ports i)) 2 p := by
  have hleft : rowCoefficient ports 2 = (fun p => if p = ⟨(1, 11), by decide⟩ then (-ports 0) else if p = ⟨(0, 1), by decide⟩ then (-ports 0) else if p = ⟨(0, 11), by decide⟩ then ((-ports 0) - 1) else if p = ⟨(0, 22), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then (-ports 0) else 0) := by unfold rowCoefficient; rfl
  have hright : rowCoefficient (fun i => f (ports i)) 2 = (fun p => if p = ⟨(1, 11), by decide⟩ then (-(fun i => f (ports i)) 0) else if p = ⟨(0, 1), by decide⟩ then (-(fun i => f (ports i)) 0) else if p = ⟨(0, 11), by decide⟩ then ((-(fun i => f (ports i)) 0) - 1) else if p = ⟨(0, 22), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then (-(fun i => f (ports i)) 0) else 0) := by unfold rowCoefficient; rfl
  rw [hleft, hright]
  dsimp only
  simp only [mapIte, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 16000 in
set_option linter.unusedSimpArgs false in
private theorem mapRowCoefficient3 (f : A →+* B) (ports : Fin 4 → A)
    (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports 3 p) = rowCoefficient (fun i => f (ports i)) 3 p := by
  have hleft : rowCoefficient ports 3 = (fun p => if p = ⟨(10, 17), by decide⟩ then (-1) else if p = ⟨(0, 10), by decide⟩ then (-1) else if p = ⟨(0, 17), by decide⟩ then (-1) else if p = ⟨(0, 18), by decide⟩ then (-1) else if p = ⟨(0, 21), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then (-1) else 0) := by unfold rowCoefficient; rfl
  have hright : rowCoefficient (fun i => f (ports i)) 3 = (fun p => if p = ⟨(10, 17), by decide⟩ then (-1) else if p = ⟨(0, 10), by decide⟩ then (-1) else if p = ⟨(0, 17), by decide⟩ then (-1) else if p = ⟨(0, 18), by decide⟩ then (-1) else if p = ⟨(0, 21), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then (-1) else 0) := by unfold rowCoefficient; rfl
  rw [hleft, hright]
  dsimp only
  simp only [mapIte, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 16000 in
set_option linter.unusedSimpArgs false in
private theorem mapRowCoefficient4 (f : A →+* B) (ports : Fin 4 → A)
    (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports 4 p) = rowCoefficient (fun i => f (ports i)) 4 p := by
  have hleft : rowCoefficient ports 4 = (fun p => if p = ⟨(13, 18), by decide⟩ then 1 else if p = ⟨(13, 21), by decide⟩ then (-1) else if p = ⟨(0, 13), by decide⟩ then (-1) else if p = ⟨(14, 18), by decide⟩ then 1 else if p = ⟨(14, 21), by decide⟩ then (-1) else if p = ⟨(0, 18), by decide⟩ then 2 else if p = ⟨(0, 20), by decide⟩ then 1 else if p = ⟨(0, 21), by decide⟩ then (-2) else 0) := by unfold rowCoefficient; rfl
  have hright : rowCoefficient (fun i => f (ports i)) 4 = (fun p => if p = ⟨(13, 18), by decide⟩ then 1 else if p = ⟨(13, 21), by decide⟩ then (-1) else if p = ⟨(0, 13), by decide⟩ then (-1) else if p = ⟨(14, 18), by decide⟩ then 1 else if p = ⟨(14, 21), by decide⟩ then (-1) else if p = ⟨(0, 18), by decide⟩ then 2 else if p = ⟨(0, 20), by decide⟩ then 1 else if p = ⟨(0, 21), by decide⟩ then (-2) else 0) := by unfold rowCoefficient; rfl
  rw [hleft, hright]
  dsimp only
  simp only [mapIte, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 16000 in
set_option linter.unusedSimpArgs false in
private theorem mapRowCoefficient5 (f : A →+* B) (ports : Fin 4 → A)
    (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports 5 p) = rowCoefficient (fun i => f (ports i)) 5 p := by
  have hleft : rowCoefficient ports 5 = (fun p => if p = ⟨(13, 18), by decide⟩ then 1 else if p = ⟨(0, 14), by decide⟩ then (-1) else if p = ⟨(18, 20), by decide⟩ then (-1) else if p = ⟨(0, 19), by decide⟩ then 1 else if p = ⟨(0, 20), by decide⟩ then (-1) else if p = ⟨(0, 0), by decide⟩ then (-1) else 0) := by unfold rowCoefficient; rfl
  have hright : rowCoefficient (fun i => f (ports i)) 5 = (fun p => if p = ⟨(13, 18), by decide⟩ then 1 else if p = ⟨(0, 14), by decide⟩ then (-1) else if p = ⟨(18, 20), by decide⟩ then (-1) else if p = ⟨(0, 19), by decide⟩ then 1 else if p = ⟨(0, 20), by decide⟩ then (-1) else if p = ⟨(0, 0), by decide⟩ then (-1) else 0) := by unfold rowCoefficient; rfl
  rw [hleft, hright]
  dsimp only
  simp only [mapIte, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 16000 in
set_option linter.unusedSimpArgs false in
private theorem mapRowCoefficient6 (f : A →+* B) (ports : Fin 4 → A)
    (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports 6 p) = rowCoefficient (fun i => f (ports i)) 6 p := by
  have hleft : rowCoefficient ports 6 = (fun p => if p = ⟨(12, 12), by decide⟩ then 1 else if p = ⟨(0, 12), by decide⟩ then 2 else if p = ⟨(13, 19), by decide⟩ then 1 else if p = ⟨(0, 13), by decide⟩ then 1 else if p = ⟨(14, 19), by decide⟩ then 1 else if p = ⟨(0, 14), by decide⟩ then 1 else if p = ⟨(19, 19), by decide⟩ then (-1) else if p = ⟨(0, 0), by decide⟩ then 1 else 0) := by unfold rowCoefficient; rfl
  have hright : rowCoefficient (fun i => f (ports i)) 6 = (fun p => if p = ⟨(12, 12), by decide⟩ then 1 else if p = ⟨(0, 12), by decide⟩ then 2 else if p = ⟨(13, 19), by decide⟩ then 1 else if p = ⟨(0, 13), by decide⟩ then 1 else if p = ⟨(14, 19), by decide⟩ then 1 else if p = ⟨(0, 14), by decide⟩ then 1 else if p = ⟨(19, 19), by decide⟩ then (-1) else if p = ⟨(0, 0), by decide⟩ then 1 else 0) := by unfold rowCoefficient; rfl
  rw [hleft, hright]
  dsimp only
  simp only [mapIte, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 16000 in
set_option linter.unusedSimpArgs false in
private theorem mapRowCoefficient7 (f : A →+* B) (ports : Fin 4 → A)
    (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports 7 p) = rowCoefficient (fun i => f (ports i)) 7 p := by
  have hleft : rowCoefficient ports 7 = (fun p => if p = ⟨(16, 21), by decide⟩ then (-4) else if p = ⟨(0, 16), by decide⟩ then (-7) else if p = ⟨(20, 21), by decide⟩ then (-1) else if p = ⟨(0, 20), by decide⟩ then (-1) else if p = ⟨(0, 21), by decide⟩ then (-5) else if p = ⟨(0, 22), by decide⟩ then (-1) else if p = ⟨(0, 23), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then (-8) else 0) := by unfold rowCoefficient; rfl
  have hright : rowCoefficient (fun i => f (ports i)) 7 = (fun p => if p = ⟨(16, 21), by decide⟩ then (-4) else if p = ⟨(0, 16), by decide⟩ then (-7) else if p = ⟨(20, 21), by decide⟩ then (-1) else if p = ⟨(0, 20), by decide⟩ then (-1) else if p = ⟨(0, 21), by decide⟩ then (-5) else if p = ⟨(0, 22), by decide⟩ then (-1) else if p = ⟨(0, 23), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then (-8) else 0) := by unfold rowCoefficient; rfl
  rw [hleft, hright]
  dsimp only
  simp only [mapIte, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 16000 in
set_option linter.unusedSimpArgs false in
private theorem mapRowCoefficient8 (f : A →+* B) (ports : Fin 4 → A)
    (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports 8 p) = rowCoefficient (fun i => f (ports i)) 8 p := by
  have hleft : rowCoefficient ports 8 = (fun p => if p = ⟨(21, 21), by decide⟩ then (-1) else if p = ⟨(0, 21), by decide⟩ then (-6) else if p = ⟨(0, 31), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then (-7) else 0) := by unfold rowCoefficient; rfl
  have hright : rowCoefficient (fun i => f (ports i)) 8 = (fun p => if p = ⟨(21, 21), by decide⟩ then (-1) else if p = ⟨(0, 21), by decide⟩ then (-6) else if p = ⟨(0, 31), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then (-7) else 0) := by unfold rowCoefficient; rfl
  rw [hleft, hright]
  dsimp only
  simp only [mapIte, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 16000 in
set_option linter.unusedSimpArgs false in
private theorem mapRowCoefficient9 (f : A →+* B) (ports : Fin 4 → A)
    (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports 9 p) = rowCoefficient (fun i => f (ports i)) 9 p := by
  have hleft : rowCoefficient ports 9 = (fun p => if p = ⟨(20, 20), by decide⟩ then (-1) else if p = ⟨(0, 20), by decide⟩ then (-2) else if p = ⟨(0, 24), by decide⟩ then 1 else 0) := by unfold rowCoefficient; rfl
  have hright : rowCoefficient (fun i => f (ports i)) 9 = (fun p => if p = ⟨(20, 20), by decide⟩ then (-1) else if p = ⟨(0, 20), by decide⟩ then (-2) else if p = ⟨(0, 24), by decide⟩ then 1 else 0) := by unfold rowCoefficient; rfl
  rw [hleft, hright]
  dsimp only
  simp only [mapIte, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 16000 in
set_option linter.unusedSimpArgs false in
private theorem mapRowCoefficient10 (f : A →+* B) (ports : Fin 4 → A)
    (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports 10 p) = rowCoefficient (fun i => f (ports i)) 10 p := by
  have hleft : rowCoefficient ports 10 = (fun p => if p = ⟨(23, 23), by decide⟩ then 1 else if p = ⟨(0, 23), by decide⟩ then 2 else if p = ⟨(24, 31), by decide⟩ then (-1) else if p = ⟨(0, 24), by decide⟩ then (-1) else if p = ⟨(0, 31), by decide⟩ then (-1) else if p = ⟨(0, 0), by decide⟩ then (-1) else 0) := by unfold rowCoefficient; rfl
  have hright : rowCoefficient (fun i => f (ports i)) 10 = (fun p => if p = ⟨(23, 23), by decide⟩ then 1 else if p = ⟨(0, 23), by decide⟩ then 2 else if p = ⟨(24, 31), by decide⟩ then (-1) else if p = ⟨(0, 24), by decide⟩ then (-1) else if p = ⟨(0, 31), by decide⟩ then (-1) else if p = ⟨(0, 0), by decide⟩ then (-1) else 0) := by unfold rowCoefficient; rfl
  rw [hleft, hright]
  dsimp only
  simp only [mapIte, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 16000 in
set_option linter.unusedSimpArgs false in
private theorem mapRowCoefficient11 (f : A →+* B) (ports : Fin 4 → A)
    (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports 11 p) = rowCoefficient (fun i => f (ports i)) 11 p := by
  have hleft : rowCoefficient ports 11 = (fun p => if p = ⟨(6, 18), by decide⟩ then (-1) else if p = ⟨(0, 6), by decide⟩ then (-1) else if p = ⟨(9, 20), by decide⟩ then (-1) else if p = ⟨(0, 9), by decide⟩ then (-1) else if p = ⟨(0, 13), by decide⟩ then 1 else if p = ⟨(0, 14), by decide⟩ then 1 else if p = ⟨(0, 18), by decide⟩ then (-1) else if p = ⟨(0, 20), by decide⟩ then (-1) else if p = ⟨(0, 27), by decide⟩ then 1 else 0) := by unfold rowCoefficient; rfl
  have hright : rowCoefficient (fun i => f (ports i)) 11 = (fun p => if p = ⟨(6, 18), by decide⟩ then (-1) else if p = ⟨(0, 6), by decide⟩ then (-1) else if p = ⟨(9, 20), by decide⟩ then (-1) else if p = ⟨(0, 9), by decide⟩ then (-1) else if p = ⟨(0, 13), by decide⟩ then 1 else if p = ⟨(0, 14), by decide⟩ then 1 else if p = ⟨(0, 18), by decide⟩ then (-1) else if p = ⟨(0, 20), by decide⟩ then (-1) else if p = ⟨(0, 27), by decide⟩ then 1 else 0) := by unfold rowCoefficient; rfl
  rw [hleft, hright]
  dsimp only
  simp only [mapIte, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 16000 in
set_option linter.unusedSimpArgs false in
private theorem mapRowCoefficient12 (f : A →+* B) (ports : Fin 4 → A)
    (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports 12 p) = rowCoefficient (fun i => f (ports i)) 12 p := by
  have hleft : rowCoefficient ports 12 = (fun p => if p = ⟨(1, 1), by decide⟩ then (((-ports 3) * ports 0) + (ports 0 ^ 2)) else if p = ⟨(1, 2), by decide⟩ then (-ports 0) else if p = ⟨(1, 17), by decide⟩ then (-ports 0) else if p = ⟨(1, 25), by decide⟩ then ports 0 else if p = ⟨(0, 1), by decide⟩ then (((((-ports 2) - ((2 * ports 3) * ports 0)) - ports 3) + (2 * (ports 0 ^ 2))) + ports 0) else if p = ⟨(2, 17), by decide⟩ then 1 else if p = ⟨(2, 25), by decide⟩ then (-1) else if p = ⟨(0, 2), by decide⟩ then ((-ports 0) - 1) else if p = ⟨(3, 25), by decide⟩ then (-1) else if p = ⟨(0, 3), by decide⟩ then (-1) else if p = ⟨(9, 20), by decide⟩ then 1 else if p = ⟨(0, 9), by decide⟩ then 1 else if p = ⟨(0, 17), by decide⟩ then (-ports 0) else if p = ⟨(0, 20), by decide⟩ then 1 else if p = ⟨(0, 25), by decide⟩ then (ports 0 - 1) else if p = ⟨(0, 27), by decide⟩ then (-1) else if p = ⟨(0, 0), by decide⟩ then ((((((-ports 2) - (ports 3 * ports 0)) - ports 3) + (ports 0 ^ 2)) + ports 0) - 1) else 0) := by unfold rowCoefficient; rfl
  have hright : rowCoefficient (fun i => f (ports i)) 12 = (fun p => if p = ⟨(1, 1), by decide⟩ then (((-(fun i => f (ports i)) 3) * (fun i => f (ports i)) 0) + ((fun i => f (ports i)) 0 ^ 2)) else if p = ⟨(1, 2), by decide⟩ then (-(fun i => f (ports i)) 0) else if p = ⟨(1, 17), by decide⟩ then (-(fun i => f (ports i)) 0) else if p = ⟨(1, 25), by decide⟩ then (fun i => f (ports i)) 0 else if p = ⟨(0, 1), by decide⟩ then (((((-(fun i => f (ports i)) 2) - ((2 * (fun i => f (ports i)) 3) * (fun i => f (ports i)) 0)) - (fun i => f (ports i)) 3) + (2 * ((fun i => f (ports i)) 0 ^ 2))) + (fun i => f (ports i)) 0) else if p = ⟨(2, 17), by decide⟩ then 1 else if p = ⟨(2, 25), by decide⟩ then (-1) else if p = ⟨(0, 2), by decide⟩ then ((-(fun i => f (ports i)) 0) - 1) else if p = ⟨(3, 25), by decide⟩ then (-1) else if p = ⟨(0, 3), by decide⟩ then (-1) else if p = ⟨(9, 20), by decide⟩ then 1 else if p = ⟨(0, 9), by decide⟩ then 1 else if p = ⟨(0, 17), by decide⟩ then (-(fun i => f (ports i)) 0) else if p = ⟨(0, 20), by decide⟩ then 1 else if p = ⟨(0, 25), by decide⟩ then ((fun i => f (ports i)) 0 - 1) else if p = ⟨(0, 27), by decide⟩ then (-1) else if p = ⟨(0, 0), by decide⟩ then ((((((-(fun i => f (ports i)) 2) - ((fun i => f (ports i)) 3 * (fun i => f (ports i)) 0)) - (fun i => f (ports i)) 3) + ((fun i => f (ports i)) 0 ^ 2)) + (fun i => f (ports i)) 0) - 1) else 0) := by unfold rowCoefficient; rfl
  rw [hleft, hright]
  dsimp only
  simp only [mapIte, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 16000 in
set_option linter.unusedSimpArgs false in
private theorem mapRowCoefficient13 (f : A →+* B) (ports : Fin 4 → A)
    (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports 13 p) = rowCoefficient (fun i => f (ports i)) 13 p := by
  have hleft : rowCoefficient ports 13 = (fun p => if p = ⟨(1, 4), by decide⟩ then (-ports 0) else if p = ⟨(1, 11), by decide⟩ then ports 0 else if p = ⟨(0, 1), by decide⟩ then (ports 1 * ports 0) else if p = ⟨(2, 11), by decide⟩ then (-1) else if p = ⟨(0, 2), by decide⟩ then ((-ports 1) - 2) else if p = ⟨(3, 11), by decide⟩ then (-1) else if p = ⟨(0, 3), by decide⟩ then ((-ports 1) - 1) else if p = ⟨(0, 4), by decide⟩ then (-ports 0) else if p = ⟨(0, 11), by decide⟩ then (ports 0 - 1) else if p = ⟨(0, 0), by decide⟩ then (((ports 1 * ports 0) - ports 1) - 2) else 0) := by unfold rowCoefficient; rfl
  have hright : rowCoefficient (fun i => f (ports i)) 13 = (fun p => if p = ⟨(1, 4), by decide⟩ then (-(fun i => f (ports i)) 0) else if p = ⟨(1, 11), by decide⟩ then (fun i => f (ports i)) 0 else if p = ⟨(0, 1), by decide⟩ then ((fun i => f (ports i)) 1 * (fun i => f (ports i)) 0) else if p = ⟨(2, 11), by decide⟩ then (-1) else if p = ⟨(0, 2), by decide⟩ then ((-(fun i => f (ports i)) 1) - 2) else if p = ⟨(3, 11), by decide⟩ then (-1) else if p = ⟨(0, 3), by decide⟩ then ((-(fun i => f (ports i)) 1) - 1) else if p = ⟨(0, 4), by decide⟩ then (-(fun i => f (ports i)) 0) else if p = ⟨(0, 11), by decide⟩ then ((fun i => f (ports i)) 0 - 1) else if p = ⟨(0, 0), by decide⟩ then ((((fun i => f (ports i)) 1 * (fun i => f (ports i)) 0) - (fun i => f (ports i)) 1) - 2) else 0) := by unfold rowCoefficient; rfl
  rw [hleft, hright]
  dsimp only
  simp only [mapIte, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 16000 in
set_option linter.unusedSimpArgs false in
private theorem mapRowCoefficient14 (f : A →+* B) (ports : Fin 4 → A)
    (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports 14 p) = rowCoefficient (fun i => f (ports i)) 14 p := by
  have hleft : rowCoefficient ports 14 = (fun p => if p = ⟨(5, 5), by decide⟩ then (-1) else if p = ⟨(0, 5), by decide⟩ then (-2) else if p = ⟨(0, 26), by decide⟩ then 1 else 0) := by unfold rowCoefficient; rfl
  have hright : rowCoefficient (fun i => f (ports i)) 14 = (fun p => if p = ⟨(5, 5), by decide⟩ then (-1) else if p = ⟨(0, 5), by decide⟩ then (-2) else if p = ⟨(0, 26), by decide⟩ then 1 else 0) := by unfold rowCoefficient; rfl
  rw [hleft, hright]
  dsimp only
  simp only [mapIte, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 16000 in
set_option linter.unusedSimpArgs false in
private theorem mapRowCoefficient15 (f : A →+* B) (ports : Fin 4 → A)
    (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports 15 p) = rowCoefficient (fun i => f (ports i)) 15 p := by
  have hleft : rowCoefficient ports 15 = (fun p => if p = ⟨(5, 8), by decide⟩ then (-1) else if p = ⟨(0, 5), by decide⟩ then (-1) else if p = ⟨(0, 8), by decide⟩ then (-1) else if p = ⟨(0, 20), by decide⟩ then 1 else if p = ⟨(0, 27), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then 1 else 0) := by unfold rowCoefficient; rfl
  have hright : rowCoefficient (fun i => f (ports i)) 15 = (fun p => if p = ⟨(5, 8), by decide⟩ then (-1) else if p = ⟨(0, 5), by decide⟩ then (-1) else if p = ⟨(0, 8), by decide⟩ then (-1) else if p = ⟨(0, 20), by decide⟩ then 1 else if p = ⟨(0, 27), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then 1 else 0) := by unfold rowCoefficient; rfl
  rw [hleft, hright]
  dsimp only
  simp only [mapIte, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 16000 in
set_option linter.unusedSimpArgs false in
private theorem mapRowCoefficient16 (f : A →+* B) (ports : Fin 4 → A)
    (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports 16 p) = rowCoefficient (fun i => f (ports i)) 16 p := by
  have hleft : rowCoefficient ports 16 = (fun p => if p = ⟨(15, 15), by decide⟩ then (-1) else if p = ⟨(0, 15), by decide⟩ then (-2) else if p = ⟨(27, 27), by decide⟩ then 1 else if p = ⟨(0, 27), by decide⟩ then 2 else if p = ⟨(0, 28), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then 1 else 0) := by unfold rowCoefficient; rfl
  have hright : rowCoefficient (fun i => f (ports i)) 16 = (fun p => if p = ⟨(15, 15), by decide⟩ then (-1) else if p = ⟨(0, 15), by decide⟩ then (-2) else if p = ⟨(27, 27), by decide⟩ then 1 else if p = ⟨(0, 27), by decide⟩ then 2 else if p = ⟨(0, 28), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then 1 else 0) := by unfold rowCoefficient; rfl
  rw [hleft, hright]
  dsimp only
  simp only [mapIte, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 16000 in
set_option linter.unusedSimpArgs false in
private theorem mapRowCoefficient17 (f : A →+* B) (ports : Fin 4 → A)
    (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports 17 p) = rowCoefficient (fun i => f (ports i)) 17 p := by
  have hleft : rowCoefficient ports 17 = (fun p => if p = ⟨(7, 24), by decide⟩ then (-1) else if p = ⟨(0, 7), by decide⟩ then (-1) else if p = ⟨(0, 24), by decide⟩ then (-1) else if p = ⟨(0, 29), by decide⟩ then 1 else 0) := by unfold rowCoefficient; rfl
  have hright : rowCoefficient (fun i => f (ports i)) 17 = (fun p => if p = ⟨(7, 24), by decide⟩ then (-1) else if p = ⟨(0, 7), by decide⟩ then (-1) else if p = ⟨(0, 24), by decide⟩ then (-1) else if p = ⟨(0, 29), by decide⟩ then 1 else 0) := by unfold rowCoefficient; rfl
  rw [hleft, hright]
  dsimp only
  simp only [mapIte, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 16000 in
set_option linter.unusedSimpArgs false in
private theorem mapRowCoefficient18 (f : A →+* B) (ports : Fin 4 → A)
    (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports 18 p) = rowCoefficient (fun i => f (ports i)) 18 p := by
  have hleft : rowCoefficient ports 18 = (fun p => if p = ⟨(29, 29), by decide⟩ then (-1) else if p = ⟨(0, 29), by decide⟩ then (-2) else if p = ⟨(0, 30), by decide⟩ then 1 else 0) := by unfold rowCoefficient; rfl
  have hright : rowCoefficient (fun i => f (ports i)) 18 = (fun p => if p = ⟨(29, 29), by decide⟩ then (-1) else if p = ⟨(0, 29), by decide⟩ then (-2) else if p = ⟨(0, 30), by decide⟩ then 1 else 0) := by unfold rowCoefficient; rfl
  rw [hleft, hright]
  dsimp only
  simp only [mapIte, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 16000 in
set_option linter.unusedSimpArgs false in
private theorem mapRowCoefficient19 (f : A →+* B) (ports : Fin 4 → A)
    (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports 19 p) = rowCoefficient (fun i => f (ports i)) 19 p := by
  have hleft : rowCoefficient ports 19 = (fun p => if p = ⟨(26, 31), by decide⟩ then (-1) else if p = ⟨(0, 26), by decide⟩ then (-1) else if p = ⟨(0, 30), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then 1 else 0) := by unfold rowCoefficient; rfl
  have hright : rowCoefficient (fun i => f (ports i)) 19 = (fun p => if p = ⟨(26, 31), by decide⟩ then (-1) else if p = ⟨(0, 26), by decide⟩ then (-1) else if p = ⟨(0, 30), by decide⟩ then 1 else if p = ⟨(0, 0), by decide⟩ then 1 else 0) := by unfold rowCoefficient; rfl
  rw [hleft, hright]
  dsimp only
  simp only [mapIte, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 16000 in
set_option linter.unusedSimpArgs false in
private theorem mapRowCoefficient20 (f : A →+* B) (ports : Fin 4 → A)
    (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports 20 p) = rowCoefficient (fun i => f (ports i)) 20 p := by
  have hleft : rowCoefficient ports 20 = (fun p => if p = ⟨(15, 15), by decide⟩ then 1 else if p = ⟨(0, 15), by decide⟩ then 2 else if p = ⟨(28, 30), by decide⟩ then (-1) else if p = ⟨(0, 28), by decide⟩ then (-1) else if p = ⟨(0, 30), by decide⟩ then (-1) else if p = ⟨(0, 0), by decide⟩ then (-1) else 0) := by unfold rowCoefficient; rfl
  have hright : rowCoefficient (fun i => f (ports i)) 20 = (fun p => if p = ⟨(15, 15), by decide⟩ then 1 else if p = ⟨(0, 15), by decide⟩ then 2 else if p = ⟨(28, 30), by decide⟩ then (-1) else if p = ⟨(0, 28), by decide⟩ then (-1) else if p = ⟨(0, 30), by decide⟩ then (-1) else if p = ⟨(0, 0), by decide⟩ then (-1) else 0) := by unfold rowCoefficient; rfl
  rw [hleft, hright]
  dsimp only
  simp only [mapIte, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 16000 in
set_option linter.unusedSimpArgs false in
private theorem mapRowCoefficient21 (f : A →+* B) (ports : Fin 4 → A)
    (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports 21 p) = rowCoefficient (fun i => f (ports i)) 21 p := by
  have hleft : rowCoefficient ports 21 = (fun p => if p = ⟨(18, 22), by decide⟩ then 1 else if p = ⟨(0, 18), by decide⟩ then 2 else if p = ⟨(21, 22), by decide⟩ then (-1) else if p = ⟨(0, 21), by decide⟩ then (-1) else if p = ⟨(0, 0), by decide⟩ then 1 else 0) := by unfold rowCoefficient; rfl
  have hright : rowCoefficient (fun i => f (ports i)) 21 = (fun p => if p = ⟨(18, 22), by decide⟩ then 1 else if p = ⟨(0, 18), by decide⟩ then 2 else if p = ⟨(21, 22), by decide⟩ then (-1) else if p = ⟨(0, 21), by decide⟩ then (-1) else if p = ⟨(0, 0), by decide⟩ then 1 else 0) := by unfold rowCoefficient; rfl
  rw [hleft, hright]
  dsimp only
  simp only [mapIte, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero]

theorem map_rowCoefficient (f : A →+* B) (ports : Fin 4 → A)
    (k : Fin 22) (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports k p) = rowCoefficient (fun i => f (ports i)) k p := by
  fin_cases k
  · change f (rowCoefficient ports 0 p) = rowCoefficient (fun i => f (ports i)) 0 p
    exact mapRowCoefficient0 f ports p
  · change f (rowCoefficient ports 1 p) = rowCoefficient (fun i => f (ports i)) 1 p
    exact mapRowCoefficient1 f ports p
  · change f (rowCoefficient ports 2 p) = rowCoefficient (fun i => f (ports i)) 2 p
    exact mapRowCoefficient2 f ports p
  · change f (rowCoefficient ports 3 p) = rowCoefficient (fun i => f (ports i)) 3 p
    exact mapRowCoefficient3 f ports p
  · change f (rowCoefficient ports 4 p) = rowCoefficient (fun i => f (ports i)) 4 p
    exact mapRowCoefficient4 f ports p
  · change f (rowCoefficient ports 5 p) = rowCoefficient (fun i => f (ports i)) 5 p
    exact mapRowCoefficient5 f ports p
  · change f (rowCoefficient ports 6 p) = rowCoefficient (fun i => f (ports i)) 6 p
    exact mapRowCoefficient6 f ports p
  · change f (rowCoefficient ports 7 p) = rowCoefficient (fun i => f (ports i)) 7 p
    exact mapRowCoefficient7 f ports p
  · change f (rowCoefficient ports 8 p) = rowCoefficient (fun i => f (ports i)) 8 p
    exact mapRowCoefficient8 f ports p
  · change f (rowCoefficient ports 9 p) = rowCoefficient (fun i => f (ports i)) 9 p
    exact mapRowCoefficient9 f ports p
  · change f (rowCoefficient ports 10 p) = rowCoefficient (fun i => f (ports i)) 10 p
    exact mapRowCoefficient10 f ports p
  · change f (rowCoefficient ports 11 p) = rowCoefficient (fun i => f (ports i)) 11 p
    exact mapRowCoefficient11 f ports p
  · change f (rowCoefficient ports 12 p) = rowCoefficient (fun i => f (ports i)) 12 p
    exact mapRowCoefficient12 f ports p
  · change f (rowCoefficient ports 13 p) = rowCoefficient (fun i => f (ports i)) 13 p
    exact mapRowCoefficient13 f ports p
  · change f (rowCoefficient ports 14 p) = rowCoefficient (fun i => f (ports i)) 14 p
    exact mapRowCoefficient14 f ports p
  · change f (rowCoefficient ports 15 p) = rowCoefficient (fun i => f (ports i)) 15 p
    exact mapRowCoefficient15 f ports p
  · change f (rowCoefficient ports 16 p) = rowCoefficient (fun i => f (ports i)) 16 p
    exact mapRowCoefficient16 f ports p
  · change f (rowCoefficient ports 17 p) = rowCoefficient (fun i => f (ports i)) 17 p
    exact mapRowCoefficient17 f ports p
  · change f (rowCoefficient ports 18 p) = rowCoefficient (fun i => f (ports i)) 18 p
    exact mapRowCoefficient18 f ports p
  · change f (rowCoefficient ports 19 p) = rowCoefficient (fun i => f (ports i)) 19 p
    exact mapRowCoefficient19 f ports p
  · change f (rowCoefficient ports 20 p) = rowCoefficient (fun i => f (ports i)) 20 p
    exact mapRowCoefficient20 f ports p
  · change f (rowCoefficient ports 21 p) = rowCoefficient (fun i => f (ports i)) 21 p
    exact mapRowCoefficient21 f ports p

theorem map_kernelValue (f : A →+* B) (ports : Fin 4 → A) (base : A) :
    f (kernelValue ports base) = kernelValue (fun i => f (ports i)) (f base) := by
  simp only [kernelValue, map_sum, map_mul, map_pow, map_rowCoefficient,
    QuadraticCoding.correction, mapIte, map_ofNat, map_one]

theorem map_ratioValue (f : A →+* B) (R N b g cap h s w phi i j n : A) :
    f (ratioValue R N b g cap h s w phi i j n) =
      ratioValue (f R) (f N) (f b) (f g) (f cap) (f h) (f s) (f w) (f phi) (f i) (f j) (f n) := by
  simp only [ratioValue, NearSquareFinalizer.norm, map_add, map_sub, map_mul,
    map_pow, map_ofNat, map_one]

theorem map_sourceRank (f : A →+* B) (ports : Fin 4 → A) (base b g : A) :
    f (sourceRank ports base b g) = sourceRank (fun i => f (ports i)) (f base) (f b) (f g) := by
  simp only [sourceRank, sourceN, sourceHigh, sourceMask, sourceHighMask,
    map_kernelValue, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, map_sum]

theorem map_value (f : A →+* B) (ports : Fin 4 → A) (height : A) (x : Fin 9 → A) :
    f (value ports height x) = value (fun i => f (ports i)) (f height) (fun i => f (x i)) := by
  simp only [value, sourceBase, sourceN, sourceCap, map_ratioValue, map_sourceRank,
    map_mul, map_pow, map_ofNat]

/-- Natural witness packing follows the documented nine-coordinate order. -/
def witnessVector (b g : ℕ) (v : NativeNineRatio52.NewVars) (n : ℕ) : Fin 9 → ℕ :=
  ![b, g, v.h, v.s, v.w, v.phi, v.i, v.j, n]

/-- The source cast bridge is deliberately explicit, so no truncation is
smuggled into the polynomial data or hidden in a rank definition. -/
theorem value_eq_finalValue (ports : Fin 4 → ℤ) (height : ℤ)
    (b g : ℕ) (v : NativeNineRatio52.NewVars) (n R N cap : ℕ)
    (hR : sourceRank ports (sourceBase height b) b g = (R : ℤ))
    (hN : sourceN (sourceBase height b) = (N : ℤ))
    (hcap : sourceCap (sourceBase height b) b = (cap : ℤ)) :
    value ports height (fun i => (witnessVector b g v n i : ℤ)) = v.finalValue R N b g cap n := by
  change ratioValue (sourceRank ports (sourceBase height b) b g)
    (sourceN (sourceBase height b)) b g (sourceCap (sourceBase height b) b)
      v.h v.s v.w v.phi v.i v.j n = _
  rw [hR, hN, hcap]
  exact ratioValue_nat R N b g cap v n

/-- The actual fixed ordinary polynomial for any supplied four-port tuple
and height. No existential polynomial is selected. -/
noncomputable def polynomial (ports : Fin 4 → ℤ) (height : ℤ) : MvPolynomial (Fin 9) ℤ :=
  value (fun i => MvPolynomial.C (ports i)) (MvPolynomial.C height) MvPolynomial.X

theorem eval_polynomial (ports : Fin 4 → ℤ) (height : ℤ) (x : Fin 9 → ℤ) :
    MvPolynomial.eval x (polynomial ports height) = value ports height x := by
  unfold polynomial
  rw [map_value]
  simp only [MvPolynomial.eval_C, MvPolynomial.eval_X]

end DiophantineConsistency.NativeNinePolynomial52
