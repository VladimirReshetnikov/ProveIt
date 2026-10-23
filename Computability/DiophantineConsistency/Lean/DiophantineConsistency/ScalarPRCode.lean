import Mathlib.Computability.Primrec.Basic

/-!
# Scalar primitive recursive programs

This data-valued syntax mirrors the seven constructors of `Nat.Primrec`.
Keeping pairing and its inverse projections as primitive program operations
avoids expanding all encoding proofs into vector primitive recursion.
-/

namespace DiophantineConsistency

inductive ScalarPRCode
  | zero
  | succ
  | left
  | right
  | pair (first second : ScalarPRCode)
  | comp (outer inner : ScalarPRCode)
  | prec (base step : ScalarPRCode)
  deriving Repr, DecidableEq

namespace ScalarPRCode

def eval : ScalarPRCode → ℕ → ℕ
  | .zero, _ => 0
  | .succ, n => n.succ
  | .left, n => n.unpair.1
  | .right, n => n.unpair.2
  | .pair f g, n => Nat.pair (f.eval n) (g.eval n)
  | .comp f g, n => f.eval (g.eval n)
  | .prec f g, n =>
      n.unpair.2.rec (f.eval n.unpair.1)
        (fun i acc => g.eval (Nat.pair n.unpair.1 (Nat.pair i acc)))

theorem primrec (c : ScalarPRCode) : Nat.Primrec c.eval := by
  induction c with
  | zero => exact Nat.Primrec.zero
  | succ => exact Nat.Primrec.succ
  | left => exact Nat.Primrec.left
  | right => exact Nat.Primrec.right
  | pair f g hf hg => exact hf.pair hg
  | comp f g hf hg => exact hf.comp hg
  | prec f g hf hg => exact hf.prec hg

/-- A supplied scalar program with a checked specification. -/
def Realizes (f : ℕ → ℕ) := {c : ScalarPRCode // ∀ n, c.eval n = f n}

namespace Realizes

def zero : Realizes (fun _ => 0) := ⟨.zero, fun _ => rfl⟩
def succ : Realizes Nat.succ := ⟨.succ, fun _ => rfl⟩
def left : Realizes (fun n => n.unpair.1) := ⟨.left, fun _ => rfl⟩
def right : Realizes (fun n => n.unpair.2) := ⟨.right, fun _ => rfl⟩

def pair {f g : ℕ → ℕ} (p : Realizes f) (q : Realizes g) :
    Realizes (fun n => Nat.pair (f n) (g n)) :=
  ⟨.pair p.val q.val, fun n => congrArg₂ Nat.pair (p.property n) (q.property n)⟩

def comp {f g : ℕ → ℕ} (p : Realizes f) (q : Realizes g) :
    Realizes (fun n => f (g n)) :=
  ⟨.comp p.val q.val, fun n => (p.property _).trans (congrArg f (q.property n))⟩

def prec {f g : ℕ → ℕ} (p : Realizes f) (q : Realizes g) :
    Realizes (Nat.unpaired (fun z n =>
      n.rec (f z) (fun i acc => g (Nat.pair z (Nat.pair i acc))))) := by
  refine ⟨.prec p.val q.val, ?_⟩
  intro packed
  have h (n : ℕ) :
      Nat.rec (motive := fun _ => ℕ) (p.val.eval packed.unpair.1)
          (fun i acc => q.val.eval (Nat.pair packed.unpair.1 (Nat.pair i acc))) n =
        Nat.rec (motive := fun _ => ℕ) (f packed.unpair.1)
          (fun i acc => g (Nat.pair packed.unpair.1 (Nat.pair i acc))) n := by
    induction n with
    | zero => exact p.property _
    | succ n ih =>
        change q.val.eval (Nat.pair packed.unpair.1 (Nat.pair n _)) =
          g (Nat.pair packed.unpair.1 (Nat.pair n _))
        rw [q.property, ih]
  exact h packed.unpair.2

def ofEq {f g : ℕ → ℕ} (p : Realizes f) (h : ∀ n, f n = g n) : Realizes g :=
  ⟨p.val, fun n => (p.property n).trans (h n)⟩

end Realizes
end ScalarPRCode
end DiophantineConsistency
