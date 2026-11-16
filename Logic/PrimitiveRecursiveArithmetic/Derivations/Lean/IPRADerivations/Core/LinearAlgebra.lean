import IPRADerivations.Core.Tactic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.CrossProduct

/-!
# Vectors, matrices and determinants of integer terms

Integer-term versions of finite sums, dot and cross products, matrix products,
traces, determinants (Laplace expansion along the first row) and adjugates
(cofactors), together with the lemmas that `ZT.toZ` maps each of them to the
corresponding Mathlib operation over the ring `Groth (Q Γ)`.

A matrix equation `M = N` of size `k` is the iPRA formula `Mat.eqFm M N`, the
conjunction of the `k²` integer equations between entries. `Mat.derive` derives
it from the equality of the evaluated Mathlib matrices.

So an identity of linear algebra can be proved once over an arbitrary
commutative ring with Mathlib, and then read as an iPRA derivation.
-/

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open Matrix

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Finite conjunctions -/

/-- The conjunction of a finite family of formulas (`0 ≐ 0` when empty). -/
def conjFin : {k : ℕ} → (Fin k → Fm PTm n) → Fm PTm n
  | 0, _ => Fm.eq ConciseIPRA.PTm.zero ConciseIPRA.PTm.zero
  | 1, f => f 0
  | k + 2, f => Fm.and (f 0) (conjFin fun i : Fin (k + 1) => f i.succ)

theorem conjFin_intro {k : ℕ} {f : Fin k → Fm PTm n} (h : ∀ i, Γ ⊢[PRAAx] f i) :
    Γ ⊢[PRAAx] conjFin f := by
  match k, f, h with
  | 0, _, _ => exact .eqRefl _
  | 1, _, h => exact h 0
  | _ + 2, _, h => exact .andI (h 0) (conjFin_intro fun i => h i.succ)

/-! ## Sums and signs of integer terms -/

namespace ZT

/-- `∑ i, f i` for integer terms. -/
def sumFin : {k : ℕ} → (Fin k → ZT n) → ZT n
  | 0, _ => natLit 0
  | k + 1, f => f 0 + sumFin fun i : Fin k => f i.succ

@[simp] theorem toZ_sumFin : {k : ℕ} → (f : Fin k → ZT n) →
    toZ Γ (sumFin f) = ∑ i, toZ Γ (f i)
  | 0, f => by simp [sumFin]
  | k + 1, f => by rw [sumFin, toZ_add, toZ_sumFin, Fin.sum_univ_succ]

/-- `(-1)ʲ x`. -/
def signPow (j : ℕ) (x : ZT n) : ZT n := if Even j then x else -x

@[simp] theorem toZ_signPow (j : ℕ) (x : ZT n) : toZ Γ (signPow j x) = (-1) ^ j * toZ Γ x := by
  unfold signPow
  split_ifs with h
  · simp [h.neg_one_pow]
  · simp [(Nat.not_even_iff_odd.mp h).neg_one_pow]

end ZT

/-! ## Vectors -/

/-- Integer vectors of length `k`. -/
abbrev Vec (k n : ℕ) := Fin k → ZT n

namespace Vec

def toZ (Γ : List (Fm PTm n)) {k : ℕ} (v : Vec k n) : Fin k → Groth (Q Γ) := fun i => ZT.toZ Γ (v i)

def add {k : ℕ} (u v : Vec k n) : Vec k n := fun i => u i + v i
def sub {k : ℕ} (u v : Vec k n) : Vec k n := fun i => u i - v i
def smul {k : ℕ} (c : ZT n) (v : Vec k n) : Vec k n := fun i => c * v i
def dot {k : ℕ} (u v : Vec k n) : ZT n := ZT.sumFin fun i => u i * v i

/-- The cross product of integer 3-vectors. -/
def cross (u v : Vec 3 n) : Vec 3 n :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

/-- The triple product `[u v w] = u ⬝ (v × w)`. -/
def triple (u v w : Vec 3 n) : ZT n := dot u (cross v w)

/-- Equality of integer vectors, as a conjunction of integer equations. -/
def eqFm {k : ℕ} (u v : Vec k n) : Fm PTm n := conjFin fun i => ZT.eq (u i) (v i)

variable {k : ℕ}

@[simp] theorem toZ_apply (v : Vec k n) (i : Fin k) : toZ Γ v i = ZT.toZ Γ (v i) := rfl
@[simp] theorem toZ_add (u v : Vec k n) : toZ Γ (add u v) = toZ Γ u + toZ Γ v := by
  funext i; simp [toZ, add]
@[simp] theorem toZ_sub (u v : Vec k n) : toZ Γ (sub u v) = toZ Γ u - toZ Γ v := by
  funext i; simp [toZ, sub]
@[simp] theorem toZ_smul (c : ZT n) (v : Vec k n) :
    toZ Γ (smul c v) = ZT.toZ Γ c • toZ Γ v := by
  funext i; simp [toZ, smul]
@[simp] theorem toZ_dot (u v : Vec k n) : ZT.toZ Γ (dot u v) = toZ Γ u ⬝ᵥ toZ Γ v := by
  simp [dot, toZ, dotProduct]
@[simp] theorem toZ_cross (u v : Vec 3 n) : toZ Γ (cross u v) = toZ Γ u ⨯₃ toZ Γ v := by
  funext i; fin_cases i <;> simp [cross, toZ, crossProduct]
@[simp] theorem toZ_triple (u v w : Vec 3 n) :
    ZT.toZ Γ (triple u v w) = toZ Γ u ⬝ᵥ (toZ Γ v ⨯₃ toZ Γ w) := by
  simp [triple]

theorem derive {u v : Vec k n} (h : toZ Γ u = toZ Γ v) : Γ ⊢[PRAAx] eqFm u v :=
  conjFin_intro fun i => ZT.derive (congrFun h i)

end Vec

/-! ## Matrices -/

/-- Integer `k × k` matrices. -/
abbrev Mat (k n : ℕ) := Fin k → Fin k → ZT n

namespace Mat

variable {k : ℕ}

def toZ (Γ : List (Fm PTm n)) (M : Mat k n) : Matrix (Fin k) (Fin k) (Groth (Q Γ)) :=
  Matrix.of fun i j => ZT.toZ Γ (M i j)

def add (M N : Mat k n) : Mat k n := fun i j => M i j + N i j
def sub (M N : Mat k n) : Mat k n := fun i j => M i j - N i j
def smul (c : ZT n) (M : Mat k n) : Mat k n := fun i j => c * M i j
def mul (M N : Mat k n) : Mat k n := fun i j => ZT.sumFin fun l => M i l * N l j
def transpose (M : Mat k n) : Mat k n := fun i j => M j i
def one : Mat k n := fun i j => if i = j then ZT.natLit 1 else ZT.natLit 0
def zero : Mat k n := fun _ _ => ZT.natLit 0
def trace (M : Mat k n) : ZT n := ZT.sumFin fun i => M i i
def mulVec (M : Mat k n) (v : Vec k n) : Vec k n := fun i => ZT.sumFin fun j => M i j * v j

/-- The determinant, by Laplace expansion along the first row. -/
def det : {k : ℕ} → Mat k n → ZT n
  | 0, _ => ZT.natLit 1
  | _ + 1, M => ZT.sumFin fun j =>
      ZT.signPow j (M 0 j * det fun a b => M a.succ (j.succAbove b))

/-- The adjugate (transposed cofactor matrix). -/
def adj : {k : ℕ} → Mat k n → Mat k n
  | 0, _ => fun i => i.elim0
  | _ + 1, M => fun i j => ZT.signPow (j + i) (det fun a b => M (j.succAbove a) (i.succAbove b))

/-- Equality of integer matrices, as a conjunction of integer equations. -/
def eqFm (M N : Mat k n) : Fm PTm n := conjFin fun i => conjFin fun j => ZT.eq (M i j) (N i j)

@[simp] theorem toZ_apply (M : Mat k n) (i j : Fin k) : toZ Γ M i j = ZT.toZ Γ (M i j) := rfl

@[simp] theorem toZ_add (M N : Mat k n) : toZ Γ (add M N) = toZ Γ M + toZ Γ N := by
  ext i j; simp [toZ, add]
@[simp] theorem toZ_sub (M N : Mat k n) : toZ Γ (sub M N) = toZ Γ M - toZ Γ N := by
  ext i j; simp [toZ, sub]
@[simp] theorem toZ_smul (c : ZT n) (M : Mat k n) : toZ Γ (smul c M) = ZT.toZ Γ c • toZ Γ M := by
  ext i j; simp [toZ, smul]
@[simp] theorem toZ_mul (M N : Mat k n) : toZ Γ (mul M N) = toZ Γ M * toZ Γ N := by
  ext i j; simp [toZ, mul, Matrix.mul_apply]
@[simp] theorem toZ_transpose (M : Mat k n) : toZ Γ (transpose M) = (toZ Γ M)ᵀ := by
  ext i j; simp [toZ, transpose]
@[simp] theorem toZ_one : toZ Γ (one : Mat k n) = 1 := by
  ext i j; by_cases h : i = j <;> simp [toZ, one, h, Matrix.one_apply]
@[simp] theorem toZ_zero : toZ Γ (zero : Mat k n) = 0 := by
  ext i j; simp [toZ, zero]
@[simp] theorem toZ_trace (M : Mat k n) : ZT.toZ Γ (trace M) = (toZ Γ M).trace := by
  simp [trace, toZ, Matrix.trace]
@[simp] theorem toZ_mulVec (M : Mat k n) (v : Vec k n) :
    Vec.toZ Γ (mulVec M v) = toZ Γ M *ᵥ Vec.toZ Γ v := by
  funext i; simp [mulVec, toZ, Vec.toZ, Matrix.mulVec, dotProduct]

@[simp] theorem toZ_det : {k : ℕ} → (M : Mat k n) → ZT.toZ Γ (det M) = (toZ Γ M).det
  | 0, M => by simp [det]
  | k + 1, M => by
    rw [det, ZT.toZ_sumFin, Matrix.det_succ_row_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ZT.toZ_signPow, ZT.toZ_mul, toZ_det, ← _root_.mul_assoc]
    rfl

@[simp] theorem toZ_adj : {k : ℕ} → (M : Mat k n) → toZ Γ (adj M) = (toZ Γ M).adjugate
  | 0, M => by ext i; exact i.elim0
  | k + 1, M => by
    ext i j
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    simp only [toZ_apply, adj, ZT.toZ_signPow, toZ_det]
    rfl

theorem derive {M N : Mat k n} (h : toZ Γ M = toZ Γ N) : Γ ⊢[PRAAx] eqFm M N :=
  conjFin_intro fun i => conjFin_intro fun j => ZT.derive (congrFun (congrFun h i) j)

end Mat

/-- The integer vector of length `k` whose entries are the integer variables read
from the natural-number variables `o, o + 1, …, o + 2k − 1`. -/
def Vec.vars (k o : ℕ) {n : ℕ} (h : o + 2 * k ≤ n) : Vec k n := fun i =>
  ZT.var2 ⟨o + 2 * i, by have := i.isLt; omega⟩ ⟨o + 2 * i + 1, by have := i.isLt; omega⟩

/-- A hypothesis that is an integer equation, as an equation of evaluations. -/
theorem ZT.toZ_mem {u v : ZT n} (h : ZT.eq u v ∈ Γ) : ZT.toZ Γ u = ZT.toZ Γ v :=
  ZT.toZ_eq (.hyp h)

/-- `k` integer variables read from `2k` natural-number variables: the `i`-th
integer has positive part `2i` and negative part `2i + 1`, after an offset. -/
def intVar (off : ℕ) (i : ℕ) (h : off + 2 * i + 1 < n) : ZT n :=
  ZT.var2 ⟨off + 2 * i, by omega⟩ ⟨off + 2 * i + 1, h⟩

end LeanProofs.IPRA
