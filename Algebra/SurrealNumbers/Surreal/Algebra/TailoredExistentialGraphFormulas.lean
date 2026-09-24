import Surreal.Algebra.TailoredDetectorFormulas

/-!
# Native one-witness ideals and six-witness existential graphs

The literal existential formulas of `odg:def:rem:numberfieldideal`.
The radicand is a natural numeral. No term names its square root in the
coefficient field, and all six graph witnesses are existential.
-/

namespace Surreal.TailoredExistentialGraphFormulas
open FirstOrder FirstOrder.Language ArithmeticGuards

/-- One quadratic equation with arbitrary native terms. -/
def quadratic {α : Type*} {n : ℕ} (δ : ℕ) (x y : Language.ring.Term (α ⊕ Fin n)) :
    Language.ring.BoundedFormula α n := (x * x).bdEqual (numeral δ * (y * y))

/-- The one-witness parameter-free ideal formula. -/
def ideal (δ : ℕ) : Language.ring.Formula (Fin 1) :=
  (quadratic δ (Term.var (Sum.inl 0)) (Term.var (Sum.inr (0 : Fin 1)))).ex

/-- The six-variable quantifier-free graph system. -/
def graphMatrix (p q δ : ℕ) : Language.ring.BoundedFormula (Fin 2) 6 :=
  let x := Term.var (Sum.inl 0)
  let n := Term.var (Sum.inl 1)
  let v (i : Fin 6) := Term.var (Sum.inr i)
  TailoredDetectorFormulas.equations p q n (v 0) (v 1) (v 2) (v 3) (v 4) ⊓
    quadratic δ (x + -n) (v 5)

/-- Five guard witnesses and one quadratic witness define the existential graph. -/
def graph (p q δ : ℕ) : Language.ring.Formula (Fin 2) := (graphMatrix p q δ).exs

variable {R : Type*} [CommRing R] [FirstOrder.Ring.CompatibleRing R]

@[simp] theorem realize_quadratic {α : Type*} {n : ℕ} (δ : ℕ)
    (x y : Language.ring.Term (α ⊕ Fin n)) (a : α → R) (b : Fin n → R) :
    (quadratic δ x y).Realize a b ↔
      (x.realize (Sum.elim a b)) ^ 2 = (δ : R) * (y.realize (Sum.elim a b)) ^ 2 := by
  simp [quadratic, pow_two]

/-- The ideal syntax has exactly the intended quadratic semantics. -/
theorem realize_ideal (δ : ℕ) (a : Fin 1 → R) :
    (ideal δ).Realize a ↔ ∃ y : R, a 0 ^ 2 = (δ : R) * y ^ 2 := by
  simp [ideal, Formula.Realize, BoundedFormula.realize_ex, Fin.snoc]

@[simp] theorem realize_graphMatrix (p q δ : ℕ) (a : Fin 2 → R) (b : Fin 6 → R) :
    (graphMatrix p q δ).Realize a b ↔
      TailoredDiophantineConstants.System p q (a 1) (b 0) (b 1) (b 2) (b 3) (b 4) ∧
      (a 0 - a 1) ^ 2 = (δ : R) * b 5 ^ 2 := by
  simp [graphMatrix, sub_eq_add_neg]

/-- Realizing the native graph is precisely the guard plus one quadratic witness. -/
theorem realize_graph (p q δ : ℕ) (a : Fin 2 → R) :
    (graph p q δ).Realize a ↔ TailoredDiophantineConstants.Xi p q (a 1) ∧
      ∃ y : R, (a 0 - a 1) ^ 2 = (δ : R) * y ^ 2 := by
  rw [graph, BoundedFormula.realize_exs]
  simp only [realize_graphMatrix]
  constructor
  · rintro ⟨b, hs, hq⟩
    exact ⟨⟨b 0, b 1, b 2, b 3, b 4, hs⟩, b 5, hq⟩
  · rintro ⟨⟨u, v, w, s, t, hs⟩, y, hy⟩
    exact ⟨![u, v, w, s, t, y], hs, hy⟩

end Surreal.TailoredExistentialGraphFormulas

namespace Surreal.TailoredConstantTermGraph

/-- Any natural quadratic kernel test combines with the tailored guard to give the exact graph. -/
theorem quadratic_graph_iff {R O : Type*} [CommRing R] [CommRing O]
    (p q δ : ℕ) (ct : R →+* O) (ι : O →+* R)
    (hsection : ∀ b : O, ct (ι b) = b)
    (hXi : ∀ n : R, TailoredDiophantineConstants.Xi p q n ↔ n ∈ ι.range)
    (hkernel : ∀ a : R, (∃ y : R, a ^ 2 = (δ : R) * y ^ 2) ↔ ct a = 0)
    (x n : R) :
    (TailoredDiophantineConstants.Xi p q n ∧ ∃ y : R, (x - n) ^ 2 = (δ : R) * y ^ 2) ↔
      n = ι (ct x) := by
  rw [hXi, hkernel, map_sub, sub_eq_zero]
  constructor
  · rintro ⟨⟨b, rfl⟩, he⟩
    rw [hsection] at he
    rw [he]
  · rintro rfl
    exact ⟨⟨ct x, rfl⟩, (hsection _).symm⟩

end Surreal.TailoredConstantTermGraph
