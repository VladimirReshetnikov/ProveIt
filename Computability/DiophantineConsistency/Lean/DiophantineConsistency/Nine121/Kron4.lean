import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.BigOperators.Fin
import DiophantineConsistency.Nine121.SparsePoly4

/-! # Polynomial identities in four variables by one Kronecker evaluation

`NE` are polynomial expressions with natural coefficients (powers of the four variables, natural
literals, sums, products and literal term lists); `ZE` are their integer counterparts with
subtraction. `split e = (e⁺, e⁻)` writes an integer expression as a difference of two natural ones
(`eval_split`).

`kcheck D₀ D₁ D₂ D₃ X e₁ e₂` asks that every variable degree of `e₁, e₂` (computed syntactically
by `deg`) is below `Dₖ`, that the sums of coefficients `e₁(1,1,1,1), e₂(1,1,1,1)` are below `X`,
and that `e₁` and `e₂` agree at the Kronecker point `(X, X^{D₀}, X^{D₀D₁}, X^{D₀D₁D₂})`. Then
`kcheck_sound`: `e₁ = e₂` in every commutative semiring. The proof: the expansions of `e₁, e₂` are
`MvPolynomial (Fin 4) ℕ`s with exponents in the box and coefficients `< X`; the Kronecker map to
`ℕ[X]` is injective on such polynomials and the value at `X` determines a polynomial with
coefficients `< X` (base-`X` digits).

All computational definitions use the bare recursors, so `decide +kernel` evaluates `kcheck` with
the kernel's GMP arithmetic on a few large numbers instead of term-by-term list arithmetic. -/
set_option autoImplicit false
noncomputable section
namespace Nine121.Kron
open SP4

/-- Selecting one of four values. -/
def sel {R : Type*} (k : Fin 4) (a c i z : R) : R :=
  match k with
  | 0 => a
  | 1 => c
  | 2 => i
  | 3 => z

def mexp (k : Fin 4) (m : Mon) : ℕ :=
  match k with
  | 0 => m.e0
  | 1 => m.e1
  | 2 => m.e2
  | 3 => m.e3

/-- A binary tree of terms `c·m` with natural coefficients. -/
inductive NT where
  | leaf (m : Mon) (c : ℕ)
  | node (l r : NT)

/-- A binary tree of terms `c·m` with integer coefficients. -/
inductive TT where
  | leaf (m : Mon) (c : ℤ)
  | node (l r : TT)

def TT.toList (t : TT) : List (Mon × ℤ) :=
  TT.rec (motive := fun _ => List (Mon × ℤ)) (fun m c => [(m, c)]) (fun _ _ x y => x ++ y) t

theorem TT.toList_leaf (m : Mon) (c : ℤ) : (TT.leaf m c).toList = [(m, c)] := rfl
theorem TT.toList_node (l r : TT) : (TT.node l r).toList = l.toList ++ r.toList := rfl

/-- Natural polynomial expressions. -/
inductive NE where
  | pw (k : Fin 4) (n : ℕ)
  | lit (n : ℕ)
  | add (x y : NE)
  | mul (x y : NE)
  | terms (t : NT)

/-- Integer polynomial expressions. -/
inductive ZE where
  | pw (k : Fin 4) (n : ℕ)
  | lit (n : ℤ)
  | add (x y : ZE)
  | sub (x y : ZE)
  | mul (x y : ZE)
  | terms (t : TT)

section Eval
variable {R : Type*} [CommSemiring R] (a c i z : R)

def evMs (m : Mon) : R := a ^ m.e0 * c ^ m.e1 * i ^ m.e2 * z ^ m.e3

def evTs (t : NT) : R :=
  NT.rec (motive := fun _ => R) (fun m n => (n : R) * evMs a c i z m) (fun _ _ x y => x + y) t

def NE.eval (e : NE) : R :=
  NE.rec (motive := fun _ => R) (fun k n => sel k a c i z ^ n) (fun n => (n : R))
    (fun _ _ x y => x + y) (fun _ _ x y => x * y) (fun l => evTs a c i z l) e

theorem evTs_leaf (m : Mon) (n : ℕ) : evTs a c i z (NT.leaf m n) = (n : R) * evMs a c i z m := rfl
theorem evTs_node (l r : NT) : evTs a c i z (NT.node l r) = evTs a c i z l + evTs a c i z r := rfl
theorem eval_pw (k : Fin 4) (n : ℕ) : (NE.pw k n).eval a c i z = sel k a c i z ^ n := rfl
theorem eval_lit (n : ℕ) : (NE.lit n).eval a c i z = (n : R) := rfl
theorem eval_add (x y : NE) : (NE.add x y).eval a c i z = x.eval a c i z + y.eval a c i z := rfl
theorem eval_mul (x y : NE) : (NE.mul x y).eval a c i z = x.eval a c i z * y.eval a c i z := rfl
theorem eval_terms (t : NT) : (NE.terms t).eval a c i z = evTs a c i z t := rfl

end Eval

section ZEval
variable {R : Type*} [CommRing R] (a c i z : R)

def ZE.eval (e : ZE) : R :=
  ZE.rec (motive := fun _ => R) (fun k n => sel k a c i z ^ n) (fun n => (n : R))
    (fun _ _ x y => x + y) (fun _ _ x y => x - y) (fun _ _ x y => x * y)
    (fun t => SP4.evL a c i z t.toList) e

theorem zeval_pw (k : Fin 4) (n : ℕ) : (ZE.pw k n).eval a c i z = sel k a c i z ^ n := rfl
theorem zeval_lit (n : ℤ) : (ZE.lit n).eval a c i z = (n : R) := rfl
theorem zeval_add (x y : ZE) : (ZE.add x y).eval a c i z = x.eval a c i z + y.eval a c i z := rfl
theorem zeval_sub (x y : ZE) : (ZE.sub x y).eval a c i z = x.eval a c i z - y.eval a c i z := rfl
theorem zeval_mul (x y : ZE) : (ZE.mul x y).eval a c i z = x.eval a c i z * y.eval a c i z := rfl
theorem zeval_terms (t : TT) : (ZE.terms t).eval a c i z = SP4.evL a c i z t.toList := rfl

end ZEval

/-! ## The positive/negative split -/

def posTs (t : TT) : NT := TT.rec (motive := fun _ => NT) (fun m c => NT.leaf m c.toNat)
  (fun _ _ x y => NT.node x y) t
def negTs (t : TT) : NT := TT.rec (motive := fun _ => NT) (fun m c => NT.leaf m (-c).toNat)
  (fun _ _ x y => NT.node x y) t

def split (e : ZE) : NE × NE :=
  ZE.rec (motive := fun _ => NE × NE)
    (fun k n => (NE.pw k n, NE.lit 0))
    (fun n => (NE.lit n.toNat, NE.lit (-n).toNat))
    (fun _ _ x y => (NE.add x.1 y.1, NE.add x.2 y.2))
    (fun _ _ x y => (NE.add x.1 y.2, NE.add x.2 y.1))
    (fun _ _ x y => (NE.add (NE.mul x.1 y.1) (NE.mul x.2 y.2), NE.add (NE.mul x.1 y.2) (NE.mul x.2 y.1)))
    (fun l => (NE.terms (posTs l), NE.terms (negTs l))) e

theorem evL_split {R : Type*} [CommRing R] (a c i z : R) (t : TT) :
    SP4.evL a c i z t.toList = evTs a c i z (posTs t) - evTs a c i z (negTs t) := by
  induction t with
  | leaf m k =>
    show SP4.evL a c i z [(m, k)] = ((k.toNat : ℕ) : R) * evMs a c i z m -
      (((-k).toNat : ℕ) : R) * evMs a c i z m
    have e : ((k : ℤ) : R) = ((k.toNat : ℕ) : R) - (((-k).toNat : ℕ) : R) := by
      have h := Int.toNat_sub_toNat_neg k
      conv_lhs => rw [← h]
      push_cast; ring
    simp only [SP4.evL, e, evMs, SP4.evM]; ring
  | node l r hl hr =>
    rw [TT.toList_node, SP4.evL_append, hl, hr]
    show _ = evTs a c i z (NT.node (posTs l) (posTs r)) - evTs a c i z (NT.node (negTs l) (negTs r))
    rw [evTs_node, evTs_node]; ring

theorem eval_split {R : Type*} [CommRing R] (a c i z : R) (e : ZE) :
    e.eval a c i z = (split e).1.eval a c i z - (split e).2.eval a c i z := by
  induction e with
  | pw k n => simp [split, ZE.eval, NE.eval]
  | lit n =>
    simp only [split, zeval_lit, eval_lit]
    have h := Int.toNat_sub_toNat_neg n
    conv_lhs => rw [← h]
    push_cast; ring
  | add x y hx hy =>
    simp only [zeval_add, hx, hy]; simp only [split, eval_add]; ring
  | sub x y hx hy =>
    simp only [zeval_sub, hx, hy]; simp only [split, eval_add]; ring
  | mul x y hx hy =>
    simp only [zeval_mul, hx, hy]; simp only [split, eval_add, eval_mul]; ring
  | terms l => simp only [split, zeval_terms, eval_terms]; exact evL_split a c i z l

/-! ## Kernel-side evaluation and degrees -/

def evMN (a c i z : ℕ) (m : Mon) : ℕ :=
  Nat.mul (Nat.mul (Nat.mul (Nat.pow a m.e0) (Nat.pow c m.e1)) (Nat.pow i m.e2)) (Nat.pow z m.e3)

def evTN (a c i z : ℕ) (t : NT) : ℕ :=
  NT.rec (motive := fun _ => ℕ) (fun m n => Nat.mul n (evMN a c i z m)) (fun _ _ x y => Nat.add x y) t

def selN (k : Fin 4) (a c i z : ℕ) : ℕ := sel k a c i z

def NE.evalN (a c i z : ℕ) (e : NE) : ℕ :=
  NE.rec (motive := fun _ => ℕ) (fun k n => Nat.pow (selN k a c i z) n) (fun n => n)
    (fun _ _ x y => Nat.add x y) (fun _ _ x y => Nat.mul x y) (fun l => evTN a c i z l) e

theorem evTN_eq (a c i z : ℕ) (t : NT) : evTN a c i z t = evTs a c i z t := by
  induction t with
  | leaf m n => show Nat.mul n (evMN a c i z m) = _; rw [evTs_leaf]; simp [evMN, evMs]
  | node l r hl hr => show Nat.add (evTN a c i z l) (evTN a c i z r) = _; rw [hl, hr, evTs_node]; rfl

theorem evalN_add (a c i z : ℕ) (x y : NE) :
    (NE.add x y).evalN a c i z = Nat.add (x.evalN a c i z) (y.evalN a c i z) := rfl
theorem evalN_mul (a c i z : ℕ) (x y : NE) :
    (NE.mul x y).evalN a c i z = Nat.mul (x.evalN a c i z) (y.evalN a c i z) := rfl

theorem evalN_eq (a c i z : ℕ) (e : NE) : e.evalN a c i z = e.eval a c i z := by
  induction e with
  | pw k n => rfl
  | lit n => rfl
  | add x y hx hy => rw [evalN_add, hx, hy]; rfl
  | mul x y hx hy => rw [evalN_mul, hx, hy]; rfl
  | terms l => exact evTN_eq a c i z l

def tdeg (k : Fin 4) (t : NT) : ℕ :=
  NT.rec (motive := fun _ => ℕ) (fun m _ => mexp k m) (fun _ _ x y => Nat.max x y) t

def NE.deg (k : Fin 4) (e : NE) : ℕ :=
  NE.rec (motive := fun _ => ℕ) (fun j n => bif Nat.beq j.val k.val then n else 0) (fun _ => 0)
    (fun _ _ x y => Nat.max x y) (fun _ _ x y => Nat.add x y) (fun l => tdeg k l) e

/-- The Kronecker check. -/
def kcheck (D0 D1 D2 D3 X : ℕ) (e1 e2 : NE) : Bool :=
  Nat.blt 1 X &&
  (Nat.blt (e1.deg 0) D0 && Nat.blt (e1.deg 1) D1 && Nat.blt (e1.deg 2) D2 && Nat.blt (e1.deg 3) D3) &&
  (Nat.blt (e2.deg 0) D0 && Nat.blt (e2.deg 1) D1 && Nat.blt (e2.deg 2) D2 && Nat.blt (e2.deg 3) D3) &&
  (Nat.blt (e1.evalN 1 1 1 1) X && Nat.blt (e2.evalN 1 1 1 1) X) &&
  Nat.beq (e1.evalN X (Nat.pow X D0) (Nat.pow X (D0 * D1)) (Nat.pow X (D0 * D1 * D2)))
    (e2.evalN X (Nat.pow X D0) (Nat.pow X (D0 * D1)) (Nat.pow X (D0 * D1 * D2)))

/-! ## Packed evaluation of term trees at a power-of-two Kronecker point

At `X = 2^K` a term `c·a^{e₀}c^{e₁}i^{e₂}z^{e₃}` is `c·2^{K·idx}`; `pkT` evaluates a tree as a pair
(base index, value relative to the base), so that each node's number only spans the indices of its
own leaves (for a tree built over terms sorted by index). -/

def idxM (D0 D1 D2 : ℕ) (m : Mon) : ℕ := m.e0 + D0 * (m.e1 + D1 * (m.e2 + D2 * m.e3))

def pkT (K D0 D1 D2 : ℕ) (t : NT) : ℕ × ℕ :=
  NT.rec (motive := fun _ => ℕ × ℕ) (fun m n => (idxM D0 D1 D2 m, n))
    (fun _ _ A B => (Nat.min A.1 B.1, Nat.add (Nat.shiftLeft A.2 (Nat.mul K (Nat.sub A.1 (Nat.min A.1 B.1))))
      (Nat.shiftLeft B.2 (Nat.mul K (Nat.sub B.1 (Nat.min A.1 B.1)))))) t

/-- The Kronecker point `(X, X^{D₀}, X^{D₀D₁}, X^{D₀D₁D₂})` at `X = 2^K`. -/
def NE.evalK (K D0 D1 D2 : ℕ) (e : NE) : ℕ :=
  NE.rec (motive := fun _ => ℕ)
    (fun k n => Nat.pow (selN k (Nat.pow 2 K) (Nat.pow (Nat.pow 2 K) D0) (Nat.pow (Nat.pow 2 K) (D0 * D1))
      (Nat.pow (Nat.pow 2 K) (D0 * D1 * D2))) n) (fun n => n)
    (fun _ _ x y => Nat.add x y) (fun _ _ x y => Nat.mul x y)
    (fun t => Nat.shiftLeft (pkT K D0 D1 D2 t).2 (Nat.mul K (pkT K D0 D1 D2 t).1)) e

theorem shl (a b : ℕ) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

theorem evalK_add (K D0 D1 D2 : ℕ) (x y : NE) :
    (NE.add x y).evalK K D0 D1 D2 = Nat.add (x.evalK K D0 D1 D2) (y.evalK K D0 D1 D2) := rfl
theorem evalK_mul (K D0 D1 D2 : ℕ) (x y : NE) :
    (NE.mul x y).evalK K D0 D1 D2 = Nat.mul (x.evalK K D0 D1 D2) (y.evalK K D0 D1 D2) := rfl

theorem pkT_spec (K D0 D1 D2 : ℕ) (t : NT) :
    (pkT K D0 D1 D2 t).2 * 2 ^ (K * (pkT K D0 D1 D2 t).1) =
      evTN (Nat.pow 2 K) (Nat.pow (Nat.pow 2 K) D0) (Nat.pow (Nat.pow 2 K) (D0 * D1))
        (Nat.pow (Nat.pow 2 K) (D0 * D1 * D2)) t := by
  induction t with
  | leaf m n =>
    show n * 2 ^ (K * idxM D0 D1 D2 m) = Nat.mul n (evMN _ _ _ _ m)
    simp only [evMN, Nat.pow_eq, Nat.mul_eq, ← pow_mul, ← pow_add, idxM]
    congr 2; ring
  | node l r hl hr =>
    show (Nat.add (Nat.shiftLeft (pkT K D0 D1 D2 l).2
        (Nat.mul K (Nat.sub (pkT K D0 D1 D2 l).1 (Nat.min (pkT K D0 D1 D2 l).1 (pkT K D0 D1 D2 r).1))))
      (Nat.shiftLeft (pkT K D0 D1 D2 r).2
        (Nat.mul K (Nat.sub (pkT K D0 D1 D2 r).1 (Nat.min (pkT K D0 D1 D2 l).1 (pkT K D0 D1 D2 r).1))))) *
      2 ^ (K * Nat.min (pkT K D0 D1 D2 l).1 (pkT K D0 D1 D2 r).1) =
      Nat.add (evTN _ _ _ _ l) (evTN _ _ _ _ r)
    rw [← hl, ← hr]
    set A := pkT K D0 D1 D2 l
    set B := pkT K D0 D1 D2 r
    have hA : Nat.min A.1 B.1 ≤ A.1 := Nat.min_le_left _ _
    have hB : Nat.min A.1 B.1 ≤ B.1 := Nat.min_le_right _ _
    rw [shl, shl, Nat.add_eq, Nat.mul_eq, Nat.mul_eq, Nat.sub_eq, Nat.sub_eq, add_mul, mul_assoc,
      mul_assoc, ← pow_add, ← pow_add, ← Nat.mul_add, ← Nat.mul_add, Nat.sub_add_cancel hA,
      Nat.sub_add_cancel hB]
    rfl

theorem evalK_eq (K D0 D1 D2 : ℕ) (e : NE) :
    e.evalK K D0 D1 D2 = e.evalN (Nat.pow 2 K) (Nat.pow (Nat.pow 2 K) D0) (Nat.pow (Nat.pow 2 K) (D0 * D1))
      (Nat.pow (Nat.pow 2 K) (D0 * D1 * D2)) := by
  induction e with
  | pw k n => rfl
  | lit n => rfl
  | add x y hx hy => rw [evalK_add, evalN_add, hx, hy]
  | mul x y hx hy => rw [evalK_mul, evalN_mul, hx, hy]
  | terms t =>
    show Nat.shiftLeft (pkT K D0 D1 D2 t).2 (Nat.mul K (pkT K D0 D1 D2 t).1) = evTN _ _ _ _ t
    rw [shl, Nat.mul_eq, pkT_spec]

/-- The Kronecker check at `X = 2^K`, with the packed evaluation of term trees. -/
def kcheckK (D0 D1 D2 D3 K : ℕ) (e1 e2 : NE) : Bool :=
  Nat.blt 1 (Nat.pow 2 K) &&
  (Nat.blt (e1.deg 0) D0 && Nat.blt (e1.deg 1) D1 && Nat.blt (e1.deg 2) D2 && Nat.blt (e1.deg 3) D3) &&
  (Nat.blt (e2.deg 0) D0 && Nat.blt (e2.deg 1) D1 && Nat.blt (e2.deg 2) D2 && Nat.blt (e2.deg 3) D3) &&
  (Nat.blt (e1.evalN 1 1 1 1) (Nat.pow 2 K) && Nat.blt (e2.evalN 1 1 1 1) (Nat.pow 2 K)) &&
  Nat.beq (e1.evalK K D0 D1 D2) (e2.evalK K D0 D1 D2)

theorem kcheck_of_kcheckK (D0 D1 D2 D3 K : ℕ) (e1 e2 : NE) (h : kcheckK D0 D1 D2 D3 K e1 e2 = true) :
    kcheck D0 D1 D2 D3 (Nat.pow 2 K) e1 e2 = true := by
  unfold kcheckK at h
  unfold kcheck
  rw [evalK_eq, evalK_eq] at h
  exact h

/-! ## Expansion into `MvPolynomial` -/

open MvPolynomial

abbrev MP := MvPolynomial (Fin 4) ℕ

def toMv (e : NE) : MP := e.eval (X 0) (X 1) (X 2) (X 3)

theorem sel_hom {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) (k : Fin 4)
    (a c i z : R) : φ (sel k a c i z) = sel k (φ a) (φ c) (φ i) (φ z) := by
  fin_cases k <;> rfl

theorem eval_hom {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) (a c i z : R)
    (e : NE) : φ (e.eval a c i z) = e.eval (φ a) (φ c) (φ i) (φ z) := by
  induction e with
  | pw k n => simp only [eval_pw, map_pow, sel_hom]
  | lit n => simp only [eval_lit, map_natCast]
  | add x y hx hy => simp only [eval_add, map_add, hx, hy]
  | mul x y hx hy => simp only [eval_mul, map_mul, hx, hy]
  | terms l =>
    simp only [eval_terms]
    induction l with
    | leaf m n => simp only [evTs_leaf, map_mul, map_natCast, evMs, map_pow]
    | node l r hl hr => simp only [evTs_node, map_add, hl, hr]

theorem eval_toMv {R : Type*} [CommSemiring R] (a c i z : R) (e : NE) :
    aeval (fun k => sel k a c i z) (toMv e) = e.eval a c i z := by
  have h := eval_hom (aeval (R := ℕ) (fun k => sel k a c i z)).toRingHom (X 0) (X 1) (X 2) (X 3) e
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X] at h
  exact h

theorem degreeOf_Xpow (k j : Fin 4) (n : ℕ) :
    degreeOf k ((X j : MP) ^ n) ≤ if k = j then n else 0 := by
  have h1 := degreeOf_pow_le k (X j : MP) n
  rw [degreeOf_X] at h1
  split_ifs with h
  · rw [if_pos h, mul_one] at h1; exact h1
  · rw [if_neg h, mul_zero] at h1; exact h1

theorem degreeOf_pw (k j : Fin 4) (n : ℕ) :
    degreeOf k ((X j : MP) ^ n) ≤ bif Nat.beq j.val k.val then n else 0 := by
  have h1 := degreeOf_Xpow k j n
  cases h : Nat.beq j.val k.val
  · have hne : k ≠ j := by
      intro hk
      have : Nat.beq j.val k.val = true := Nat.beq_eq.mpr (by rw [hk])
      rw [h] at this; exact absurd this (by decide)
    rw [if_neg hne] at h1; exact h1
  · have hk : k = j := (Fin.ext (Nat.beq_eq.mp h)).symm
    rw [if_pos hk] at h1; exact h1

theorem degreeOf_mono (k : Fin 4) (m : Mon) :
    degreeOf k (evMs (X 0 : MP) (X 1) (X 2) (X 3) m) ≤ mexp k m := by
  unfold evMs
  have h0 := degreeOf_Xpow k 0 m.e0
  have h1 := degreeOf_Xpow k 1 m.e1
  have h2 := degreeOf_Xpow k 2 m.e2
  have h3 := degreeOf_Xpow k 3 m.e3
  have s1 := degreeOf_mul_le k ((X 0 : MP) ^ m.e0 * X 1 ^ m.e1 * X 2 ^ m.e2) (X 3 ^ m.e3)
  have s2 := degreeOf_mul_le k ((X 0 : MP) ^ m.e0 * X 1 ^ m.e1) (X 2 ^ m.e2)
  have s3 := degreeOf_mul_le k ((X 0 : MP) ^ m.e0) (X 1 ^ m.e1)
  have e : ((if k = 0 then m.e0 else 0) + (if k = 1 then m.e1 else 0) + (if k = 2 then m.e2 else 0) +
      (if k = 3 then m.e3 else 0)) = mexp k m := by
    fin_cases k <;> simp [mexp]
  omega

theorem degreeOf_toMv (k : Fin 4) (e : NE) : degreeOf k (toMv e) ≤ e.deg k := by
  unfold toMv
  induction e with
  | pw j n =>
    rw [eval_pw]
    have : sel j (X 0 : MP) (X 1) (X 2) (X 3) = X j := by fin_cases j <;> rfl
    rw [this]; exact degreeOf_pw k j n
  | lit n =>
    rw [eval_lit, ← map_natCast (C : ℕ →+* MP), degreeOf_C]; exact Nat.zero_le _
  | add x y hx hy =>
    rw [eval_add]
    exact le_trans (degreeOf_add_le _ _ _) (max_le_max hx hy)
  | mul x y hx hy =>
    rw [eval_mul]
    exact le_trans (degreeOf_mul_le _ _ _) (add_le_add hx hy)
  | terms l =>
    rw [eval_terms]
    show _ ≤ tdeg k l
    induction l with
    | leaf m n =>
      rw [evTs_leaf]
      refine le_trans (degreeOf_mul_le _ _ _) ?_
      rw [← map_natCast (C : ℕ →+* MP), degreeOf_C, zero_add]
      exact degreeOf_mono k m
    | node l r hl hr =>
      rw [evTs_node]
      exact le_trans (degreeOf_add_le _ _ _) (max_le_max hl hr)

theorem coeff_le_eval_one (p : MP) (m : Fin 4 →₀ ℕ) : coeff m p ≤ eval (fun _ => 1) p := by
  rw [eval_eq]
  simp only [one_pow, Finset.prod_const_one, mul_one]
  by_cases hm : m ∈ p.support
  · exact Finset.single_le_sum (f := fun d => coeff d p) (fun _ _ => Nat.zero_le _) hm
  · rw [notMem_support_iff.mp hm]; exact Nat.zero_le _

theorem eval_one_toMv (e : NE) : eval (fun _ => 1) (toMv e) = e.evalN 1 1 1 1 := by
  rw [evalN_eq, ← eval_toMv]
  have : (fun k : Fin 4 => sel k (1 : ℕ) 1 1 1) = fun _ => 1 := by funext k; fin_cases k <;> rfl
  rw [this]; rfl

/-! ## Injectivity of the Kronecker evaluation -/

theorem digit_eq {D a b a' b' : ℕ} (ha : a < D) (ha' : a' < D) (h : a + D * b = a' + D * b') :
    a = a' ∧ b = b' := by
  have hD : 0 < D := by omega
  have h1 : (a + D * b) % D = a := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  have h2 : (a' + D * b') % D = a' := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha']
  have h3 : (a + D * b) / D = b := by rw [Nat.add_mul_div_left _ _ hD, Nat.div_eq_of_lt ha, zero_add]
  have h4 : (a' + D * b') / D = b' := by
    rw [Nat.add_mul_div_left _ _ hD, Nat.div_eq_of_lt ha', zero_add]
  exact ⟨by rw [← h1, h, h2], by rw [← h3, h, h4]⟩

theorem digits_inj (b : ℕ) (hb : 1 < b) : ∀ (N : ℕ) (d e : ℕ → ℕ), (∀ j, d j < b) → (∀ j, e j < b) →
    ∑ j ∈ Finset.range N, d j * b ^ j = ∑ j ∈ Finset.range N, e j * b ^ j → ∀ j < N, d j = e j
  | 0, _, _, _, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | N + 1, d, e, hd, he, h, j, hj => by
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
    have hs : ∀ f : ℕ → ℕ, ∑ x ∈ Finset.range N, f (x + 1) * b ^ (x + 1) =
        b * ∑ x ∈ Finset.range N, f (x + 1) * b ^ x := by
      intro f; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun x _ => ?_); ring
    rw [hs d, hs e, pow_zero, mul_one, mul_one] at h
    have h' : d 0 + b * ∑ x ∈ Finset.range N, d (x + 1) * b ^ x =
        e 0 + b * ∑ x ∈ Finset.range N, e (x + 1) * b ^ x := by omega
    obtain ⟨h0, hrest⟩ := digit_eq (hd 0) (he 0) h'
    cases j with
    | zero => exact h0
    | succ j =>
      exact digits_inj b hb N (fun x => d (x + 1)) (fun x => e (x + 1)) (fun x => hd _) (fun x => he _)
        hrest j (by omega)

theorem poly_inj {b : ℕ} (hb : 1 < b) {f g : Polynomial ℕ} (hf : ∀ n, f.coeff n < b)
    (hg : ∀ n, g.coeff n < b) (h : f.eval b = g.eval b) : f = g := by
  set N := max f.natDegree g.natDegree + 1
  rw [Polynomial.eval_eq_sum_range' (n := N) (by omega),
    Polynomial.eval_eq_sum_range' (n := N) (by omega)] at h
  have hc := digits_inj b hb N (fun j => f.coeff j) (fun j => g.coeff j) hf hg h
  ext n
  by_cases hn : n < N
  · exact hc n hn
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

section Box
variable (D0 D1 D2 : ℕ)

def strd (k : Fin 4) : ℕ :=
  match k with
  | 0 => 1
  | 1 => D0
  | 2 => D0 * D1
  | 3 => D0 * D1 * D2

def idx (m : Fin 4 →₀ ℕ) : ℕ := m 0 + D0 * (m 1 + D1 * (m 2 + D2 * m 3))

/-- The Kronecker map to `ℕ[X]`. -/
def kmap (p : MP) : Polynomial ℕ := aeval (fun k => (Polynomial.X : Polynomial ℕ) ^ strd D0 D1 D2 k) p

theorem kmap_monomial (m : Fin 4 →₀ ℕ) (r : ℕ) :
    kmap D0 D1 D2 (monomial m r) = Polynomial.C r * Polynomial.X ^ idx D0 D1 D2 m := by
  rw [kmap, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_four,
    Polynomial.algebraMap_eq]
  simp only [strd, ← pow_mul, ← pow_add, idx]
  congr 2
  ring

theorem kmap_sum (p : MP) : kmap D0 D1 D2 p =
    ∑ v ∈ p.support, Polynomial.C (coeff v p) * Polynomial.X ^ idx D0 D1 D2 v := by
  conv_lhs => rw [p.as_sum]
  rw [kmap, map_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  exact kmap_monomial D0 D1 D2 v (coeff v p)

theorem coeff_kmap_le (p : MP) (n : ℕ) : (kmap D0 D1 D2 p).coeff n ≤ eval (fun _ => 1) p := by
  rw [kmap_sum, Polynomial.finsetSum_coeff, eval_eq]
  simp only [one_pow, Finset.prod_const_one, mul_one, Polynomial.coeff_C_mul_X_pow]
  refine Finset.sum_le_sum (fun m _ => ?_)
  split_ifs <;> simp

theorem idx_inj {m m' : Fin 4 →₀ ℕ} (h0 : m 0 < D0) (h1 : m 1 < D1) (h2 : m 2 < D2)
    (h0' : m' 0 < D0) (h1' : m' 1 < D1) (h2' : m' 2 < D2)
    (h : idx D0 D1 D2 m = idx D0 D1 D2 m') : m = m' := by
  unfold idx at h
  obtain ⟨e0, h⟩ := digit_eq h0 h0' h
  obtain ⟨e1, h⟩ := digit_eq h1 h1' h
  obtain ⟨e2, h⟩ := digit_eq h2 h2' h
  ext k; fin_cases k
  · exact e0
  · exact e1
  · exact e2
  · exact h

theorem coeff_kmap (p : MP) (hp0 : degreeOf 0 p < D0) (hp1 : degreeOf 1 p < D1)
    (hp2 : degreeOf 2 p < D2) (m : Fin 4 →₀ ℕ) (h0 : m 0 < D0) (h1 : m 1 < D1) (h2 : m 2 < D2) :
    (kmap D0 D1 D2 p).coeff (idx D0 D1 D2 m) = coeff m p := by
  rw [kmap_sum, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  have key : ∀ d ∈ p.support, idx D0 D1 D2 m = idx D0 D1 D2 d → d = m := by
    intro d hd he
    exact (idx_inj D0 D1 D2 h0 h1 h2 (lt_of_le_of_lt (monomial_le_degreeOf 0 hd) hp0)
      (lt_of_le_of_lt (monomial_le_degreeOf 1 hd) hp1) (lt_of_le_of_lt (monomial_le_degreeOf 2 hd) hp2)
      he).symm
  by_cases hm : m ∈ p.support
  · rw [Finset.sum_eq_single m]
    · simp
    · intro d hd hne; rw [if_neg]; intro he; exact hne (key d hd he)
    · intro h; exact absurd hm h
  · rw [notMem_support_iff.mp hm]
    refine Finset.sum_eq_zero (fun d hd => ?_)
    rw [if_neg]; intro he; exact hm (key d hd he ▸ hd)

theorem eval_kmap (X0 : ℕ) (p : MP) :
    (kmap D0 D1 D2 p).eval X0 = aeval (fun k => X0 ^ strd D0 D1 D2 k) p := by
  rw [kmap, ← Polynomial.coe_aeval_eq_eval, ← AlgHom.comp_apply, comp_aeval]
  have : (fun k => Polynomial.aeval X0 ((Polynomial.X : Polynomial ℕ) ^ strd D0 D1 D2 k)) =
      fun k => X0 ^ strd D0 D1 D2 k := by
    funext k; simp
  rw [this]

end Box

theorem kron_inj (D0 D1 D2 D3 X0 : ℕ) (hX : 1 < X0) {p q : MP}
    (hp : ∀ k : Fin 4, degreeOf k p < sel k D0 D1 D2 D3)
    (hq : ∀ k : Fin 4, degreeOf k q < sel k D0 D1 D2 D3)
    (hpb : eval (fun _ => 1) p < X0) (hqb : eval (fun _ => 1) q < X0)
    (h : aeval (fun k => X0 ^ strd D0 D1 D2 k) p = aeval (fun k => X0 ^ strd D0 D1 D2 k) q) :
    p = q := by
  have hk : kmap D0 D1 D2 p = kmap D0 D1 D2 q := by
    refine poly_inj hX (fun n => lt_of_le_of_lt (coeff_kmap_le D0 D1 D2 p n) hpb)
      (fun n => lt_of_le_of_lt (coeff_kmap_le D0 D1 D2 q n) hqb) ?_
    rw [eval_kmap, eval_kmap, h]
  have p0 : degreeOf 0 p < D0 := hp 0
  have p1 : degreeOf 1 p < D1 := hp 1
  have p2 : degreeOf 2 p < D2 := hp 2
  have q0 : degreeOf 0 q < D0 := hq 0
  have q1 : degreeOf 1 q < D1 := hq 1
  have q2 : degreeOf 2 q < D2 := hq 2
  ext m
  by_cases hb : m 0 < D0 ∧ m 1 < D1 ∧ m 2 < D2 ∧ m 3 < D3
  · obtain ⟨h0, h1, h2, -⟩ := hb
    rw [← coeff_kmap D0 D1 D2 p p0 p1 p2 m h0 h1 h2, ← coeff_kmap D0 D1 D2 q q0 q1 q2 m h0 h1 h2, hk]
  · have hout : ∀ r : MP, (∀ k : Fin 4, degreeOf k r < sel k D0 D1 D2 D3) → coeff m r = 0 := by
      intro r hr
      rw [← notMem_support_iff]
      intro hm
      apply hb
      exact ⟨lt_of_le_of_lt (monomial_le_degreeOf 0 hm) (hr 0),
        lt_of_le_of_lt (monomial_le_degreeOf 1 hm) (hr 1),
        lt_of_le_of_lt (monomial_le_degreeOf 2 hm) (hr 2),
        lt_of_le_of_lt (monomial_le_degreeOf 3 hm) (hr 3)⟩
    rw [hout p hp, hout q hq]

theorem deg_spec (e : NE) {D0 D1 D2 D3 : ℕ} (h0 : e.deg 0 < D0) (h1 : e.deg 1 < D1)
    (h2 : e.deg 2 < D2) (h3 : e.deg 3 < D3) (k : Fin 4) :
    degreeOf k (toMv e) < sel k D0 D1 D2 D3 := by
  refine lt_of_le_of_lt (degreeOf_toMv k e) ?_
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- **Soundness of the Kronecker check.** -/
theorem kcheck_sound (D0 D1 D2 D3 X0 : ℕ) (e1 e2 : NE) (h : kcheck D0 D1 D2 D3 X0 e1 e2 = true)
    {R : Type*} [CommSemiring R] (a c i z : R) : e1.eval a c i z = e2.eval a c i z := by
  simp only [kcheck, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨hX, ⟨⟨⟨a0, a1⟩, a2⟩, a3⟩⟩, ⟨⟨⟨b0, b1⟩, b2⟩, b3⟩⟩, hb1, hb2⟩, hv⟩ := h
  have hm : toMv e1 = toMv e2 := by
    refine kron_inj D0 D1 D2 D3 X0 hX (deg_spec e1 a0 a1 a2 a3) (deg_spec e2 b0 b1 b2 b3)
      (by rw [eval_one_toMv]; exact hb1) (by rw [eval_one_toMv]; exact hb2) ?_
    have hpt : (fun k => X0 ^ strd D0 D1 D2 k) =
        fun k => sel k X0 (Nat.pow X0 D0) (Nat.pow X0 (D0 * D1)) (Nat.pow X0 (D0 * D1 * D2)) := by
      funext k; fin_cases k <;> simp [strd, sel]
    rw [hpt, eval_toMv, eval_toMv, ← evalN_eq, ← evalN_eq]
    exact hv
  rw [← eval_toMv, ← eval_toMv, hm]

/-- An integer expression whose split passes the Kronecker check vanishes in every commutative
ring. -/
theorem zero_of_kcheck (D0 D1 D2 D3 X0 : ℕ) (e : ZE)
    (h : kcheck D0 D1 D2 D3 X0 (split e).1 (split e).2 = true)
    {R : Type*} [CommRing R] (a c i z : R) : e.eval a c i z = 0 := by
  rw [eval_split, kcheck_sound D0 D1 D2 D3 X0 _ _ h a c i z, sub_self]

/-- The same with the packed check at `X = 2^K`. -/
theorem zero_of_kcheckK (D0 D1 D2 D3 K : ℕ) (e : ZE)
    (h : kcheckK D0 D1 D2 D3 K (split e).1 (split e).2 = true)
    {R : Type*} [CommRing R] (a c i z : R) : e.eval a c i z = 0 :=
  zero_of_kcheck D0 D1 D2 D3 _ e (kcheck_of_kcheckK D0 D1 D2 D3 K _ _ h) a c i z

/-! ## Domination positivity on term trees -/

def TT.all (f : Mon × ℤ → Bool) (t : TT) : Bool :=
  TT.rec (motive := fun _ => Bool) (fun m c => f (m, c)) (fun _ _ x y => x && y) t

def TT.topSum (top : Mon) (t : TT) : ℤ :=
  TT.rec (motive := fun _ => ℤ) (fun m c => bif m.beq top then c else 0) (fun _ _ x y => x + y) t

def TT.negSum (top : Mon) (t : TT) : ℤ :=
  TT.rec (motive := fun _ => ℤ) (fun m c => bif m.beq top then 0 else bif isNonneg c then 0 else c)
    (fun _ _ x y => x + y) t

def posCheckT (top : Mon) (M : ℕ) (t : TT) : Bool :=
  t.all (domOk top) && Nat.ble 1 top.e0 && isPos (t.topSum top * M + t.negSum top)

theorem topSum_append (top : Mon) (l1 l2 : List (Mon × ℤ)) :
    topSum top (l1 ++ l2) = topSum top l1 + topSum top l2 := by
  induction l1 with
  | nil => simp [topSum]
  | cons t l ih => simp only [List.cons_append, topSum, ih]; ring

theorem negSum_append (top : Mon) (l1 l2 : List (Mon × ℤ)) :
    negSum top (l1 ++ l2) = negSum top l1 + negSum top l2 := by
  induction l1 with
  | nil => simp [negSum]
  | cons t l ih => simp only [List.cons_append, negSum, ih]; ring

theorem posCheckT_eq (top : Mon) (M : ℕ) (t : TT) :
    posCheckT top M t = posCheck top M ⟨t.toList⟩ := by
  have hall : ∀ t : TT, t.all (domOk top) = t.toList.all (domOk top) := by
    intro t
    induction t with
    | leaf m c => simp [TT.all, TT.toList]
    | node l r hl hr =>
      show (l.all (domOk top) && r.all (domOk top)) = _
      rw [TT.toList_node, List.all_append, hl, hr]
  have htop : ∀ t : TT, t.topSum top = topSum top t.toList := by
    intro t
    induction t with
    | leaf m c => simp [TT.topSum, TT.toList, topSum]
    | node l r hl hr =>
      show l.topSum top + r.topSum top = _
      rw [TT.toList_node, topSum_append, hl, hr]
  have hneg : ∀ t : TT, t.negSum top = negSum top t.toList := by
    intro t
    induction t with
    | leaf m c => simp [TT.negSum, TT.toList, negSum]
    | node l r hl hr =>
      show l.negSum top + r.negSum top = _
      rw [TT.toList_node, negSum_append, hl, hr]
  simp only [posCheckT, posCheck, hall, htop, hneg]

end Nine121.Kron
