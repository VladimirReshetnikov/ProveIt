import Surreal.Algebra.TailoredArithmeticGuard
import Surreal.Algebra.TailoredConstantTermGraph

/-!
# Native detector and prenex graph formulas

Native parameter-free ring formulas for the detector, universal ideal test
and both prenex constant-term graphs in `odg:def:thm:numberfield` and
`odg:def:rem:sigma2`. The displayed quantifier orders are retained literally.
-/

namespace Surreal.TailoredDetectorFormulas
open FirstOrder FirstOrder.Language ArithmeticGuards

/-- The tailored equations with arbitrary native terms in any variable context. -/
def equations {α : Type*} {n : ℕ} (p q : ℕ)
    (x u v w s t : Language.ring.Term (α ⊕ Fin n)) : Language.ring.BoundedFormula α n :=
  (x * (u * u + -(numeral 2 * (v * v)) + -1)).bdEqual 0 ⊓
    (x * (v + -(x * w))).bdEqual 0 ⊓
      (x * (v * s + -TailoredArithmeticGuard.certificate p q t)).bdEqual 0

/-- The quantifier-free two-witness detector equation. -/
def detectorMatrix (p q : ℕ) : Language.ring.BoundedFormula (Fin 1) 2 :=
  let x : Language.ring.Term (Fin 1 ⊕ Fin 2) := Term.var (Sum.inl 0)
  let s := Term.var (Sum.inr (0 : Fin 2))
  let t := Term.var (Sum.inr (1 : Fin 2))
  (x * s).bdEqual (TailoredArithmeticGuard.certificate p q t)

/-- The native two-existential-variable detector. -/
def detector (p q : ℕ) : Language.ring.Formula (Fin 1) := (detectorMatrix p q).exs

/-- The native two-universal-variable ideal test. -/
def ideal (p q : ℕ) : Language.ring.Formula (Fin 1) := (detectorMatrix p q).not.alls

/-- The quantifier-free graph matrix, with explicit witness and universal-variable positions. -/
def graphMatrix (p q : ℕ) (w : Fin 5 → Fin 7) (s t : Fin 7) :
    Language.ring.BoundedFormula (Fin 2) 7 :=
  let x := Term.var (Sum.inl 0)
  let n := Term.var (Sum.inl 1)
  let v (i : Fin 7) := Term.var (Sum.inr i)
  equations p q n (v (w 0)) (v (w 1)) (v (w 2)) (v (w 3)) (v (w 4)) ⊓
    (((x + -n) * v s).bdEqual (TailoredArithmeticGuard.certificate p q (v t))).not

/-- Five existential guard witnesses precede two universal detector variables. -/
def graphExistsForall (p q : ℕ) : Language.ring.Formula (Fin 2) :=
  ((graphMatrix p q ![0, 1, 2, 3, 4] 5 6).all.all).exs

/-- Two universal detector variables precede five existential guard witnesses. -/
def graphForallExists (p q : ℕ) : Language.ring.Formula (Fin 2) :=
  (graphMatrix p q ![2, 3, 4, 5, 6] 0 1).ex.ex.ex.ex.ex.all.all

variable {R : Type*} [CommRing R] [FirstOrder.Ring.CompatibleRing R]

@[simp] theorem realize_equations {α : Type*} {n : ℕ} (p q : ℕ)
    (x u v w s t : Language.ring.Term (α ⊕ Fin n)) (a : α → R) (b : Fin n → R) :
    (equations p q x u v w s t).Realize a b ↔
      TailoredDiophantineConstants.System p q
        (x.realize (Sum.elim a b)) (u.realize (Sum.elim a b)) (v.realize (Sum.elim a b))
        (w.realize (Sum.elim a b)) (s.realize (Sum.elim a b)) (t.realize (Sum.elim a b)) := by
  simp [equations, TailoredDiophantineConstants.System, pow_two, sub_eq_add_neg, and_assoc]

/-- The detector formula realizes exactly the algebraic certificate predicate. -/
theorem realize_detector (p q : ℕ) (a : Fin 1 → R) :
    (detector p q).Realize a ↔ TailoredIntersectivePolynomial.Detects p q (a 0) := by
  simp only [detector, BoundedFormula.realize_exs]
  simp [detectorMatrix]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w 0, w 1, hw⟩
  · rintro ⟨s, t, he⟩
    exact ⟨![s, t], he⟩

/-- The native universal ideal test says precisely that every certificate equation fails. -/
theorem realize_ideal (p q : ℕ) (a : Fin 1 → R) :
    (ideal p q).Realize a ↔ ∀ s t : R, a 0 * s ≠ TailoredIntersectivePolynomial.value p q t := by
  rw [ideal, BoundedFormula.realize_alls]
  simp only [BoundedFormula.realize_not]
  simp [detectorMatrix]
  constructor
  · intro h s t
    exact h ![s, t]
  · intro h w
    exact h (w 0) (w 1)

@[simp] theorem realize_graphMatrix (p q : ℕ) (w : Fin 5 → Fin 7) (s t : Fin 7)
    (a : Fin 2 → R) (b : Fin 7 → R) :
    (graphMatrix p q w s t).Realize a b ↔
      TailoredDiophantineConstants.System p q (a 1)
        (b (w 0)) (b (w 1)) (b (w 2)) (b (w 3)) (b (w 4)) ∧
      (a 0 - a 1) * b s ≠ TailoredIntersectivePolynomial.value p q (b t) := by
  simp [graphMatrix, sub_eq_add_neg]

/-- Exact semantics of the existential-universal native formula. -/
theorem realize_graphExistsForall (p q : ℕ) (a : Fin 2 → R) :
    (graphExistsForall p q).Realize a ↔ TailoredConstantTermGraph.Graph p q (a 0) (a 1) := by
  rw [graphExistsForall, BoundedFormula.realize_exs]
  simp only [BoundedFormula.realize_all, realize_graphMatrix]
  dsimp only [Fin.snoc, Matrix.cons_val_zero]
  rw [TailoredConstantTermGraph.graph_iff_exists_forall]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w 0, w 1, w 2, w 3, w 4, hw⟩
  · rintro ⟨u, v, w, s, t, h⟩
    exact ⟨![u, v, w, s, t], h⟩

/-- Exact semantics of the universal-existential native formula. -/
theorem realize_graphForallExists (p q : ℕ) (a : Fin 2 → R) :
    (graphForallExists p q).Realize a ↔ TailoredConstantTermGraph.Graph p q (a 0) (a 1) := by
  rw [graphForallExists, Formula.Realize]
  simp only [BoundedFormula.realize_all, BoundedFormula.realize_ex, realize_graphMatrix]
  dsimp only [Fin.snoc, Matrix.cons_val_zero]
  exact (TailoredConstantTermGraph.graph_iff_forall_exists p q (a 0) (a 1)).symm

end Surreal.TailoredDetectorFormulas
