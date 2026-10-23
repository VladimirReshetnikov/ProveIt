import Mathlib.Computability.Primrec.List

/-!
# Executable primitive recursive programs

`PRCode` is the data-valued counterpart of `Nat.Primrec'`. Its five
constructors store a finite program rather than an existence proof. Evaluation
is computable and is certified primitive recursive. No program is selected
from a proposition.
-/

namespace DiophantineConsistency

/-- Primitive recursive syntax on fixed-length vectors of natural numbers. -/
inductive PRCode : ℕ → Type
  | zero : PRCode 0
  | succ : PRCode 1
  | get {n : ℕ} (index : Fin n) : PRCode n
  | comp {m n : ℕ} (outer : PRCode n) (inner : Fin n → PRCode m) : PRCode m
  | prec {n : ℕ} (base : PRCode n) (step : PRCode (n + 2)) : PRCode (n + 1)

namespace PRCode

/-- The standard primitive recursion semantics, in the same coordinate order
as `Nat.Primrec'`: the step receives the index, previous result, parameters. -/
def eval {n : ℕ} : PRCode n → List.Vector ℕ n → ℕ
  | .zero, _ => 0
  | .succ, v => v.head.succ
  | .get i, v => v.get i
  | .comp f g, v => f.eval (List.Vector.ofFn (fun i => (g i).eval v))
  | .prec f g, v =>
      v.head.rec (f.eval v.tail) (fun i acc => g.eval (i ::ᵥ acc ::ᵥ v.tail))

@[simp] theorem eval_zero (v : List.Vector ℕ 0) : zero.eval v = 0 := rfl
@[simp] theorem eval_succ (v : List.Vector ℕ 1) : succ.eval v = v.head.succ := rfl
@[simp] theorem eval_get {n : ℕ} (i : Fin n) (v : List.Vector ℕ n) :
    (get i).eval v = v.get i := rfl
@[simp] theorem eval_comp {m n : ℕ} (f : PRCode n) (g : Fin n → PRCode m)
    (v : List.Vector ℕ m) :
    (comp f g).eval v = f.eval (List.Vector.ofFn (fun i => (g i).eval v)) := rfl
@[simp] theorem eval_rec {n : ℕ} (f : PRCode n) (g : PRCode (n + 2))
    (v : List.Vector ℕ (n + 1)) :
    (prec f g).eval v =
      v.head.rec (f.eval v.tail) (fun i acc => g.eval (i ::ᵥ acc ::ᵥ v.tail)) := rfl

/-- Each supplied program computes a primitive recursive function. -/
theorem primrec {n : ℕ} (c : PRCode n) : Nat.Primrec' c.eval := by
  induction c with
  | zero => exact Nat.Primrec'.zero
  | succ => exact Nat.Primrec'.succ
  | get i => exact Nat.Primrec'.get i
  | comp f g hf hg => exact Nat.Primrec'.comp (fun i => (g i).eval) hf hg
  | prec f g hf hg => exact Nat.Primrec'.prec hf hg

/-- Constants are explicit programs at every arity. -/
def constant (n : ℕ) : ℕ → PRCode n
  | 0 => .comp .zero Fin.elim0
  | k + 1 => .comp .succ (fun _ => constant n k)

@[simp] theorem eval_constant (n k : ℕ) (v : List.Vector ℕ n) :
    (constant n k).eval v = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simpa only [constant, eval_comp, eval_succ, List.Vector.head_ofFn] using
        (congrArg Nat.succ ih)

/-- A program paired with its checked specification. In particular, an
elaboration-time extractor can return code and a kernel-checked equality. -/
def Realizes {n : ℕ} (f : List.Vector ℕ n → ℕ) :=
  {c : PRCode n // ∀ v, c.eval v = f v}

namespace Realizes

def zero : Realizes (fun _ : List.Vector ℕ 0 => 0) := ⟨.zero, fun _ => rfl⟩
def succ : Realizes (fun v : List.Vector ℕ 1 => v.head.succ) := ⟨.succ, fun _ => rfl⟩
def get {n : ℕ} (i : Fin n) : Realizes (fun v : List.Vector ℕ n => v.get i) :=
  ⟨.get i, fun _ => rfl⟩

def comp {m n : ℕ} {f : List.Vector ℕ n → ℕ}
    {g : Fin n → List.Vector ℕ m → ℕ} (p : Realizes f) (q : ∀ i, Realizes (g i)) :
    Realizes (fun v => f (List.Vector.ofFn (fun i => g i v))) := by
  refine ⟨.comp p.val (fun i => (q i).val), ?_⟩
  intro v
  exact (p.property _).trans
    (congrArg (fun h => f (List.Vector.ofFn h)) (funext (fun i => (q i).property v)))

def prec {n : ℕ} {f : List.Vector ℕ n → ℕ} {g : List.Vector ℕ (n + 2) → ℕ}
    (p : Realizes f) (q : Realizes g) :
    Realizes (fun v : List.Vector ℕ (n + 1) =>
      v.head.rec (f v.tail) (fun i acc => g (i ::ᵥ acc ::ᵥ v.tail))) := by
  refine ⟨.prec p.val q.val, ?_⟩
  intro v
  have h (k : ℕ) :
      Nat.rec (motive := fun _ => ℕ) (p.val.eval v.tail)
          (fun i acc => q.val.eval (i ::ᵥ acc ::ᵥ v.tail)) k =
        Nat.rec (motive := fun _ => ℕ) (f v.tail)
          (fun i acc => g (i ::ᵥ acc ::ᵥ v.tail)) k := by
    induction k with
    | zero => exact p.property _
    | succ k ih =>
        change q.val.eval (k ::ᵥ _ ::ᵥ v.tail) = g (k ::ᵥ _ ::ᵥ v.tail)
        rw [q.property, ih]
  exact h v.head

/-- Keep program data and transport its specification using a supplied proof. -/
def ofEq {n : ℕ} {f g : List.Vector ℕ n → ℕ} (p : Realizes f)
    (h : ∀ v, f v = g v) : Realizes g :=
  ⟨p.val, fun v => (p.property v).trans (h v)⟩

end Realizes

end PRCode

end DiophantineConsistency
