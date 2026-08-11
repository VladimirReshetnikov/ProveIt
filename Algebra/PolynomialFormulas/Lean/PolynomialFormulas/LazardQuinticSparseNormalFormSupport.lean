import Mathlib.Tactic

/-!
# Sparse normal-form support for the Lazard quintic coinvariant certificate

This module contains only the five-variable sparse polynomial representation,
its executable normalization procedure, and the evaluation lemmas needed by
the Lazard coinvariant certificate.  Its namespace is deliberately independent
of the Dummit-coefficient implementation.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuinticSparseNormalFormSupport

/-- Exponents of a monomial in five variables. -/
structure Powers where
  p0 : ℕ
  p1 : ℕ
  p2 : ℕ
  p3 : ℕ
  p4 : ℕ
deriving Repr, DecidableEq

/-- One integer-coefficient monomial in the sparse representation. -/
structure SparseTerm where
  coeff : ℤ
  powers : Powers
deriving Repr, DecidableEq

/-- A sparse polynomial is a list of integer-coefficient monomials. -/
abbrev SparsePolynomial := List SparseTerm

def SparseTerm.eval {R : Type*} [CommRing R]
    (t : SparseTerm) (x : Fin 5 → R) : R :=
  t.coeff * x 0 ^ t.powers.p0 * x 1 ^ t.powers.p1 *
    x 2 ^ t.powers.p2 * x 3 ^ t.powers.p3 * x 4 ^ t.powers.p4

def SparsePolynomial.eval {R : Type*} [CommRing R] :
    SparsePolynomial → (Fin 5 → R) → R
  | [], _ => 0
  | t :: q, x => t.eval x + SparsePolynomial.eval q x

def Powers.add (a b : Powers) : Powers :=
  ⟨a.p0 + b.p0, a.p1 + b.p1, a.p2 + b.p2, a.p3 + b.p3, a.p4 + b.p4⟩

def SparseTerm.mul (a b : SparseTerm) : SparseTerm :=
  ⟨a.coeff * b.coeff, a.powers.add b.powers⟩

@[simp] theorem SparseTerm.eval_mul {R : Type*} [CommRing R]
    (a b : SparseTerm) (x : Fin 5 → R) :
    (a.mul b).eval x = a.eval x * b.eval x := by
  simp [SparseTerm.mul, SparseTerm.eval, Powers.add, pow_add]
  ring

theorem SparsePolynomial.eval_append {R : Type*} [CommRing R]
    (p q : SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (p ++ q) x =
      SparsePolynomial.eval p x + SparsePolynomial.eval q x := by
  induction p with
  | nil => simp [SparsePolynomial.eval]
  | cons t p ih => simp [SparsePolynomial.eval, ih, add_assoc]

/-! ## Executable normalization -/

def SparsePolynomial.finish (t : SparseTerm) : SparsePolynomial :=
  if t.coeff = 0 then [] else [t]

def SparsePolynomial.combineAux (t : SparseTerm) :
    SparsePolynomial → SparsePolynomial
  | [] => finish t
  | u :: q =>
      if t.powers = u.powers then
        combineAux ⟨t.coeff + u.coeff, t.powers⟩ q
      else
        finish t ++ combineAux u q

def SparsePolynomial.combine : SparsePolynomial → SparsePolynomial
  | [] => []
  | t :: q => combineAux t q

theorem SparsePolynomial.eval_finish {R : Type*} [CommRing R]
    (t : SparseTerm) (x : Fin 5 → R) :
    SparsePolynomial.eval (finish t) x = t.eval x := by
  simp only [finish]
  split
  · rename_i h
    simp [SparsePolynomial.eval, SparseTerm.eval, h]
  · simp [SparsePolynomial.eval]

theorem SparseTerm.eval_add_of_powers_eq {R : Type*} [CommRing R]
    (t u : SparseTerm) (x : Fin 5 → R) (h : t.powers = u.powers) :
    SparseTerm.eval ⟨t.coeff + u.coeff, t.powers⟩ x =
      t.eval x + u.eval x := by
  rcases t with ⟨tc, tp⟩
  rcases u with ⟨uc, up⟩
  simp only at h
  subst up
  simp [SparseTerm.eval]
  ring

theorem SparsePolynomial.eval_combineAux {R : Type*} [CommRing R]
    (t : SparseTerm) (q : SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (combineAux t q) x =
      t.eval x + SparsePolynomial.eval q x := by
  induction q generalizing t with
  | nil => simp [combineAux, eval_finish, SparsePolynomial.eval]
  | cons u q ih =>
      simp only [combineAux]
      split
      · rename_i h
        rw [ih, SparseTerm.eval_add_of_powers_eq t u x h]
        simp [SparsePolynomial.eval, add_assoc]
      · rw [SparsePolynomial.eval_append, eval_finish, ih]
        simp [SparsePolynomial.eval]

theorem SparsePolynomial.eval_combine {R : Type*} [CommRing R]
    (q : SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (combine q) x = SparsePolynomial.eval q x := by
  cases q with
  | nil => rfl
  | cons t q =>
      simp [combine, eval_combineAux, SparsePolynomial.eval]

def SparsePolynomial.addToBucket :
    ℕ → SparseTerm → List SparsePolynomial → List SparsePolynomial
  | 0, t, [] => [[t]]
  | 0, t, b :: bs => (t :: b) :: bs
  | k + 1, t, [] => [] :: addToBucket k t []
  | k + 1, t, b :: bs => b :: addToBucket k t bs

def SparsePolynomial.bucketize (key : SparseTerm → ℕ) :
    SparsePolynomial → List SparsePolynomial
  | [] => []
  | t :: q => addToBucket (key t) t (bucketize key q)

def SparsePolynomial.flattenBuckets : List SparsePolynomial → SparsePolynomial
  | [] => []
  | b :: bs => b ++ flattenBuckets bs

theorem SparsePolynomial.eval_flattenBuckets_addToBucket
    {R : Type*} [CommRing R] (k : ℕ) (t : SparseTerm)
    (bs : List SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (flattenBuckets (addToBucket k t bs)) x =
      t.eval x + SparsePolynomial.eval (flattenBuckets bs) x := by
  induction k generalizing bs with
  | zero =>
      cases bs <;>
        simp [addToBucket, flattenBuckets, SparsePolynomial.eval, eval_append]
  | succ k ih =>
      cases bs with
      | nil => simp [addToBucket, flattenBuckets, ih, SparsePolynomial.eval]
      | cons b bs =>
          simp [addToBucket, flattenBuckets, eval_append, ih]
          ring

def SparsePolynomial.radixPass (key : SparseTerm → ℕ)
    (q : SparsePolynomial) : SparsePolynomial :=
  flattenBuckets (bucketize key q)

theorem SparsePolynomial.eval_radixPass {R : Type*} [CommRing R]
    (key : SparseTerm → ℕ) (q : SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (radixPass key q) x = SparsePolynomial.eval q x := by
  induction q with
  | nil => rfl
  | cons t q ih =>
      change SparsePolynomial.eval (flattenBuckets (bucketize key q)) x =
        SparsePolynomial.eval q x at ih
      rw [radixPass, bucketize, eval_flattenBuckets_addToBucket, ih]
      rfl

/-- Stable least-significant-coordinate-first radix sort of the five powers. -/
def SparsePolynomial.sort (q : SparsePolynomial) : SparsePolynomial :=
  radixPass (fun t ↦ t.powers.p0)
    (radixPass (fun t ↦ t.powers.p1)
      (radixPass (fun t ↦ t.powers.p2)
        (radixPass (fun t ↦ t.powers.p3)
          (radixPass (fun t ↦ t.powers.p4) q))))

theorem SparsePolynomial.eval_sort {R : Type*} [CommRing R]
    (q : SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (sort q) x = SparsePolynomial.eval q x := by
  simp [sort, eval_radixPass]

def SparsePolynomial.normalize (q : SparsePolynomial) : SparsePolynomial :=
  combine (sort q)

theorem SparsePolynomial.eval_normalize {R : Type*} [CommRing R]
    (q : SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (normalize q) x = SparsePolynomial.eval q x := by
  rw [normalize, eval_combine]
  exact eval_sort q x

/-! ## Arithmetic needed by the certificate reconstruction -/

def SparsePolynomial.rawMul :
    SparsePolynomial → SparsePolynomial → SparsePolynomial
  | [], _ => []
  | t :: p, q => q.map (SparseTerm.mul t) ++ rawMul p q

theorem SparsePolynomial.eval_map_mul {R : Type*} [CommRing R]
    (t : SparseTerm) (q : SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (q.map (SparseTerm.mul t)) x =
      t.eval x * SparsePolynomial.eval q x := by
  induction q with
  | nil => simp [SparsePolynomial.eval]
  | cons u q ih =>
      simp [SparsePolynomial.eval, ih, mul_add]

theorem SparsePolynomial.eval_rawMul {R : Type*} [CommRing R]
    (p q : SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (rawMul p q) x =
      SparsePolynomial.eval p x * SparsePolynomial.eval q x := by
  induction p with
  | nil => simp [rawMul, SparsePolynomial.eval]
  | cons t p ih =>
      simp [rawMul, eval_append, eval_map_mul, ih,
        SparsePolynomial.eval, add_mul]

def SparsePolynomial.add (p q : SparsePolynomial) : SparsePolynomial :=
  normalize (p ++ q)

def SparsePolynomial.mul (p q : SparsePolynomial) : SparsePolynomial :=
  normalize (rawMul p q)

@[simp] theorem SparsePolynomial.eval_add {R : Type*} [CommRing R]
    (p q : SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (add p q) x =
      SparsePolynomial.eval p x + SparsePolynomial.eval q x := by
  simp [add, eval_normalize, eval_append]

@[simp] theorem SparsePolynomial.eval_mul {R : Type*} [CommRing R]
    (p q : SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (mul p q) x =
      SparsePolynomial.eval p x * SparsePolynomial.eval q x := by
  simp [mul, eval_normalize, eval_rawMul]

def SparsePolynomial.sum : List SparsePolynomial → SparsePolynomial
  | [] => []
  | p :: ps => add p (sum ps)

@[simp] theorem SparsePolynomial.eval_sum {R : Type*} [CommRing R]
    (ps : List SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (sum ps) x =
      (ps.map (fun p ↦ SparsePolynomial.eval p x)).sum := by
  induction ps with
  | nil => simp [sum, SparsePolynomial.eval]
  | cons p ps ih => simp [sum, ih]

/-- Equal executable normal forms certify equal evaluation over every
commutative ring. -/
theorem SparsePolynomial.eval_eq_of_normalize_eq
    {R : Type*} [CommRing R] {p q : SparsePolynomial}
    (h : normalize p = normalize q) (x : Fin 5 → R) :
    SparsePolynomial.eval p x = SparsePolynomial.eval q x := by
  calc
    SparsePolynomial.eval p x = SparsePolynomial.eval (normalize p) x :=
      (eval_normalize p x).symm
    _ = SparsePolynomial.eval (normalize q) x :=
      congrArg (fun s ↦ eval s x) h
    _ = SparsePolynomial.eval q x := eval_normalize q x

end LeanProofs.PolynomialFormulas.LazardQuinticSparseNormalFormSupport
