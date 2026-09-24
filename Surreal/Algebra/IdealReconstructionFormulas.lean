import Surreal.Algebra.PredicateIdealReconstruction
import Surreal.Algebra.TailoredExistentialGraphFormulas

/-!
# Native reconstruction formulas from an arbitrary ideal definition

The syntax and satisfaction layer for `odg:def:cor:internal`, including its
number-field extension. The input is a native unary ring formula; all
quantifiers in the fraction-pair presentation range over the original ring.
-/

namespace Surreal.IdealReconstructionFormulas
open FirstOrder FirstOrder.Language

/-- Apply a unary formula to a term in any bounded-variable context. -/
def onTerm {α : Type*} {n : ℕ} (φ : Language.ring.Formula (Fin 1))
    (t : Language.ring.Term (α ⊕ Fin n)) : Language.ring.BoundedFormula α n :=
  BoundedFormula.relabel id (φ.subst fun _ => t)

/-- Extend a term's context by one fresh final bound variable. -/
def up {α : Type*} {n : ℕ} (t : Language.ring.Term (α ⊕ Fin n)) :
    Language.ring.Term (α ⊕ Fin (n + 1)) := t.relabel (Sum.map id Fin.castSucc)

/-- The universal-existential multiplier formula on two terms. -/
def mult {α : Type*} {n : ℕ} (φ : Language.ring.Formula (Fin 1))
    (a b : Language.ring.Term (α ⊕ Fin n)) : Language.ring.BoundedFormula α n :=
  let x : Language.ring.Term (α ⊕ Fin (n + 1)) := Term.var (Sum.inr (Fin.last n))
  let y : Language.ring.Term (α ⊕ Fin (n + 2)) := Term.var (Sum.inr (Fin.last (n + 1)))
  (b.bdEqual 0).not ⊓ ((onTerm φ x).imp
    ((onTerm φ y ⊓ (up (up a) * up x).bdEqual (up (up b) * y)).ex)).all

/-- Zero or a multiplier with multiplier inverse defines the coefficients. -/
def coeff {α : Type*} {n : ℕ} (φ : Language.ring.Formula (Fin 1))
    (a b : Language.ring.Term (α ⊕ Fin n)) : Language.ring.BoundedFormula α n :=
  (b.bdEqual 0).not ⊓ (a.bdEqual 0 ⊔
    ((a.bdEqual 0).not ⊓ mult φ a b ⊓ mult φ b a))

/-- An ideal element representing the fraction, with its denominator condition. -/
def idealFraction {α : Type*} {n : ℕ} (φ : Language.ring.Formula (Fin 1))
    (a b : Language.ring.Term (α ⊕ Fin n)) : Language.ring.BoundedFormula α n :=
  let y : Language.ring.Term (α ⊕ Fin (n + 1)) := Term.var (Sum.inr (Fin.last n))
  (b.bdEqual 0).not ⊓ (onTerm φ y ⊓ (up a).bdEqual (up b * y)).ex

/-- The coefficient graph, expressed entirely on fraction representatives. -/
def graph {α : Type*} {n : ℕ} (φ : Language.ring.Formula (Fin 1))
    (a b c d : Language.ring.Term (α ⊕ Fin n)) : Language.ring.BoundedFormula α n :=
  mult φ a b ⊓ coeff φ c d ⊓ idealFraction φ (a * d + -(c * b)) (b * d)

/-- Two free coordinates represent a fraction for the multiplier predicate. -/
def multFormula (φ : Language.ring.Formula (Fin 1)) : Language.ring.Formula (Fin 2) :=
  mult φ (Term.var (Sum.inl 0)) (Term.var (Sum.inl 1))

/-- Two free coordinates represent an embedded coefficient. -/
def coeffFormula (φ : Language.ring.Formula (Fin 1)) : Language.ring.Formula (Fin 2) :=
  coeff φ (Term.var (Sum.inl 0)) (Term.var (Sum.inl 1))

/-- Four free coordinates represent the input and output fractions. -/
def graphFormula (φ : Language.ring.Formula (Fin 1)) : Language.ring.Formula (Fin 4) :=
  graph φ (Term.var (Sum.inl 0)) (Term.var (Sum.inl 1))
    (Term.var (Sum.inl 2)) (Term.var (Sum.inl 3))

variable {R α : Type*} [CommRing R] [FirstOrder.Ring.CompatibleRing R]

@[simp] theorem realize_onTerm {n : ℕ} (φ : Language.ring.Formula (Fin 1))
    (t : Language.ring.Term (α ⊕ Fin n)) (v : α → R) (xs : Fin n → R) :
    (onTerm φ t).Realize v xs ↔ φ.Realize (fun _ => t.realize (Sum.elim v xs)) := by
  simp [onTerm, Formula.Realize]
  rw [Subsingleton.elim (xs ∘ Fin.natAdd n) (default : Fin 0 → R)]

@[simp] theorem realize_up {n : ℕ} (t : Language.ring.Term (α ⊕ Fin n))
    (v : α → R) (xs : Fin n → R) (x : R) :
    (up t).realize (Sum.elim v (Fin.snoc xs x)) = t.realize (Sum.elim v xs) := by
  simp [up, Sum.elim_comp_map]

/-- The native multiplier formula realizes the generic predicate formula. -/
theorem realize_mult {n : ℕ} (φ : Language.ring.Formula (Fin 1))
    (a b : Language.ring.Term (α ⊕ Fin n)) (v : α → R) (xs : Fin n → R) :
    (mult φ a b).Realize v xs ↔
      PredicateIdealReconstruction.Mult (fun x : R => φ.Realize (fun _ => x))
        (a.realize (Sum.elim v xs)) (b.realize (Sum.elim v xs)) := by
  simp [mult, PredicateIdealReconstruction.Mult]

/-- The native coefficient formula includes its separate zero branch. -/
theorem realize_coeff {n : ℕ} (φ : Language.ring.Formula (Fin 1))
    (a b : Language.ring.Term (α ⊕ Fin n)) (v : α → R) (xs : Fin n → R) :
    (coeff φ a b).Realize v xs ↔
      PredicateIdealReconstruction.Coeff (fun x : R => φ.Realize (fun _ => x))
        (a.realize (Sum.elim v xs)) (b.realize (Sum.elim v xs)) := by
  simp [coeff, PredicateIdealReconstruction.Coeff, realize_mult, and_assoc]

/-- Native satisfaction agrees with ideal membership of a represented fraction. -/
theorem realize_idealFraction {n : ℕ} (φ : Language.ring.Formula (Fin 1))
    (a b : Language.ring.Term (α ⊕ Fin n)) (v : α → R) (xs : Fin n → R) :
    (idealFraction φ a b).Realize v xs ↔
      PredicateIdealReconstruction.IdealFraction (fun x : R => φ.Realize (fun _ => x))
        (a.realize (Sum.elim v xs)) (b.realize (Sum.elim v xs)) := by
  simp [idealFraction, PredicateIdealReconstruction.IdealFraction]

/-- Native graph satisfaction matches the generic four-coordinate predicate. -/
theorem realize_graph {n : ℕ} (φ : Language.ring.Formula (Fin 1))
    (a b c d : Language.ring.Term (α ⊕ Fin n)) (v : α → R) (xs : Fin n → R) :
    (graph φ a b c d).Realize v xs ↔
      PredicateIdealReconstruction.Graph (fun x : R => φ.Realize (fun _ => x))
        (a.realize (Sum.elim v xs)) (b.realize (Sum.elim v xs))
        (c.realize (Sum.elim v xs)) (d.realize (Sum.elim v xs)) := by
  simp [graph, PredicateIdealReconstruction.Graph, realize_mult, realize_coeff,
    realize_idealFraction, sub_eq_add_neg, and_assoc]

/-- Satisfaction of the two-coordinate multiplier formula. -/
theorem realize_multFormula (φ : Language.ring.Formula (Fin 1)) (a : Fin 2 → R) :
    (multFormula φ).Realize a ↔
      PredicateIdealReconstruction.Mult (fun x : R => φ.Realize (fun _ => x)) (a 0) (a 1) := by
  simp [multFormula, Formula.Realize, realize_mult]

/-- Satisfaction of the two-coordinate coefficient formula. -/
theorem realize_coeffFormula (φ : Language.ring.Formula (Fin 1)) (a : Fin 2 → R) :
    (coeffFormula φ).Realize a ↔
      PredicateIdealReconstruction.Coeff (fun x : R => φ.Realize (fun _ => x)) (a 0) (a 1) := by
  simp [coeffFormula, Formula.Realize, realize_coeff]

/-- Satisfaction of the four-coordinate coefficient graph formula. -/
theorem realize_graphFormula (φ : Language.ring.Formula (Fin 1)) (a : Fin 4 → R) :
    (graphFormula φ).Realize a ↔
      PredicateIdealReconstruction.Graph (fun x : R => φ.Realize (fun _ => x))
        (a 0) (a 1) (a 2) (a 3) := by
  simp [graphFormula, Formula.Realize, realize_graph]

/-- The native multiplier formula is invariant under equivalent valid fraction pairs. -/
theorem multFormula_congr [IsDomain R] (φ : Language.ring.Formula (Fin 1))
    (a b : Fin 2 → R) (ha : a 1 ≠ 0) (hb : b 1 ≠ 0)
    (he : a 0 * b 1 = b 0 * a 1) :
    (multFormula φ).Realize a ↔ (multFormula φ).Realize b := by
  rw [realize_multFormula, realize_multFormula]
  exact PredicateIdealReconstruction.mult_congr _ ha hb he

/-- The native coefficient formula is invariant under equivalent valid fraction pairs. -/
theorem coeffFormula_congr [IsDomain R] (φ : Language.ring.Formula (Fin 1))
    (a b : Fin 2 → R) (ha : a 1 ≠ 0) (hb : b 1 ≠ 0)
    (he : a 0 * b 1 = b 0 * a 1) :
    (coeffFormula φ).Realize a ↔ (coeffFormula φ).Realize b := by
  rw [realize_coeffFormula, realize_coeffFormula]
  exact PredicateIdealReconstruction.coeff_congr _ ha hb he

/-- Both coordinates of the native graph descend through fraction equivalence. -/
theorem graphFormula_congr [IsDomain R] (φ : Language.ring.Formula (Fin 1))
    (a b : Fin 4 → R) (ha₁ : a 1 ≠ 0) (ha₃ : a 3 ≠ 0)
    (hb₁ : b 1 ≠ 0) (hb₃ : b 3 ≠ 0)
    (he₀ : a 0 * b 1 = b 0 * a 1) (he₂ : a 2 * b 3 = b 2 * a 3) :
    (graphFormula φ).Realize a ↔ (graphFormula φ).Realize b := by
  rw [realize_graphFormula, realize_graphFormula]
  exact PredicateIdealReconstruction.graph_congr _ ha₁ ha₃ hb₁ hb₃ he₀ he₂

end Surreal.IdealReconstructionFormulas
