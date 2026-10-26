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

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem map_rowCoefficient (f : A →+* B) (ports : Fin 4 → A)
    (k : Fin 22) (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports k p) = rowCoefficient (fun i => f (ports i)) k p := by
  fin_cases k <;> dsimp only [rowCoefficient, Fin.reduceFinMk, Matrix.cons_val]
  all_goals
    simp only [mapIte, map_add, map_sub, map_mul, map_pow,
      map_neg, map_ofNat, map_one, map_zero]

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
