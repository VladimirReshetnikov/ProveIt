import DiophantineConsistency.ComposeRepresentation
import BusyBeaver.ZFC.EnumPerm
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring

/-!
# Quadratic graph data for the enumerator's Cantor pairing

The source pairing and its two inverse projections are represented directly
by a quadratic equality. No primitive-recursion trace for triangular
numbers or the inverse antidiagonal walk is needed.
-/

namespace DiophantineConsistency.CantorRepresentation

open SetTheory SetTheory.BusyBeaver.ZFC.Code254 SetTheory.BusyBeaver.ZFC.EnumPerm

theorem two_tri (n : ℕ) : 2 * Cantor.tri n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      2 * Cantor.tri (n + 1) = 2 * Cantor.tri n + 2 * n + 2 := by
        rw [Cantor.tri]
        ring
      _ = (n + 1) * ((n + 1) + 1) := by rw [ih]; ring

theorem two_pair (a b : ℕ) :
    2 * P a b = (a + b) * (a + b + 1) + 2 * b := by
  calc
    2 * P a b = 2 * b + 2 * Cantor.tri (a + b) := by
      rw [P, Cantor.toNat]
      ring
    _ = _ := by rw [two_tri]; ring

def pairCoordinates : GraphRep (fun v : Fin 2 → ℕ => P (v 0) (v 1)) := by
  let z : Expr (Option (Fin 2)) := .var none
  let a : Expr (Option (Fin 2)) := .var (some 0)
  let b : Expr (Option (Fin 2)) := .var (some 1)
  refine (Rep.equality (2 * z) ((a + b) * (a + b + 1) + 2 * b)).ofIff ?_
  intro v
  simp only [z, a, b, Expr.eval, ← Int.natCast_mul, ← Int.natCast_add,
    Int.natCast_inj, Function.comp_apply]
  rw [← two_pair]
  omega

@[simp] theorem pairCoordinates_witnessCount : pairCoordinates.witnessCount = 0 := rfl

def pair {σ : Type*} {f g : (σ → ℕ) → ℕ} (r : GraphRep f) (s : GraphRep g) :
    GraphRep (fun v => P (f v) (g v)) := by
  let arguments : ∀ i : Fin 2, GraphRep (![f, g] i) :=
    Fin.cases r (Fin.cases s (fun i => Fin.elim0 i))
  exact GraphRep.compose pairCoordinates arguments

def leftCoordinate : GraphRep (fun v : Fin 1 → ℕ => (unP (v 0)).1) := by
  let index : Option (Fin 2) → Option (Fin 1) ⊕ Fin 1
    | none => .inl (some 0)
    | some i => if i = 0 then .inl none else .inr 0
  refine ((Rep.reindex pairCoordinates index).existsBlock).ofIff ?_
  intro v
  change (∃ w : Fin 1 → ℕ, v (some 0) = P (v none) (w 0)) ↔
    v none = (unP (v (some 0))).1
  constructor
  · rintro ⟨w, h⟩
    rw [h, unP_P']
  · intro h
    refine ⟨fun _ => (unP (v (some 0))).2, ?_⟩
    rw [h]
    exact (Cantor.toNat_ofNat (v (some 0))).symm

def rightCoordinate : GraphRep (fun v : Fin 1 → ℕ => (unP (v 0)).2) := by
  let index : Option (Fin 2) → Option (Fin 1) ⊕ Fin 1
    | none => .inl (some 0)
    | some i => if i = 0 then .inr 0 else .inl none
  refine ((Rep.reindex pairCoordinates index).existsBlock).ofIff ?_
  intro v
  change (∃ w : Fin 1 → ℕ, v (some 0) = P (w 0) (v none)) ↔
    v none = (unP (v (some 0))).2
  constructor
  · rintro ⟨w, h⟩
    rw [h, unP_P']
  · intro h
    refine ⟨fun _ => (unP (v (some 0))).1, ?_⟩
    rw [h]
    exact (Cantor.toNat_ofNat (v (some 0))).symm

@[simp] theorem leftCoordinate_witnessCount : leftCoordinate.witnessCount = 1 := rfl
@[simp] theorem rightCoordinate_witnessCount : rightCoordinate.witnessCount = 1 := rfl

def left {σ : Type*} {f : (σ → ℕ) → ℕ} (r : GraphRep f) :
    GraphRep (fun v => (unP (f v)).1) :=
  GraphRep.compose leftCoordinate (fun _ => r)

def right {σ : Type*} {f : (σ → ℕ) → ℕ} (r : GraphRep f) :
    GraphRep (fun v => (unP (f v)).2) :=
  GraphRep.compose rightCoordinate (fun _ => r)

#print axioms leftCoordinate
#print axioms rightCoordinate

end DiophantineConsistency.CantorRepresentation
