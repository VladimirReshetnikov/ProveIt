import DiophantineConsistency.NaturalExpression
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Lightweight syntax for the quartic gate compiler

These definitions are shared by the semantic gate proof and the polynomial
compiler, without importing the unrelated Jones arithmetic development. -/
namespace DiophantineConsistency.QuarticCompiler
namespace Gates
variable {σ : Type*}
/-- A leaf has one node; an operation adds its root before its two subtrees. -/
abbrev Wire : NatExpr σ → Type
  | .constant _ => Fin 1
  | .var _ => Fin 1
  | .add p q => Fin 1 ⊕ (Wire p ⊕ Wire q)
  | .mul p q => Fin 1 ⊕ (Wire p ⊕ Wire q)

def count : NatExpr σ → ℕ
  | .constant _ => 1
  | .var _ => 1
  | .add p q => 1 + (count p + count q)
  | .mul p q => 1 + (count p + count q)

/-- The finite indexing is literal sum indexing, rather than `Fintype.equivFin`. -/
def index : (e : NatExpr σ) → Wire e ≃ Fin (count e)
  | .constant _ => Equiv.refl _
  | .var _ => Equiv.refl _
  | .add p q =>
      ((Equiv.sumCongr (Equiv.refl (Fin 1)) (Equiv.sumCongr (index p) (index q))).trans
        (Equiv.sumCongr (Equiv.refl (Fin 1)) finSumFinEquiv)).trans finSumFinEquiv
  | .mul p q =>
      ((Equiv.sumCongr (Equiv.refl (Fin 1)) (Equiv.sumCongr (index p) (index q))).trans
        (Equiv.sumCongr (Equiv.refl (Fin 1)) finSumFinEquiv)).trans finSumFinEquiv

instance (e : NatExpr σ) : Fintype (Wire e) := Fintype.ofEquiv (Fin (count e)) (index e).symm

/-- The output root of an expression tree. -/
def root : (e : NatExpr σ) → Wire e
  | .constant _ => 0
  | .var _ => 0
  | .add _ _ => Sum.inl 0
  | .mul _ _ => Sum.inl 0

/-- Actual acyclic gate code, expressed by one quadratic residual per node. -/
def residualSyntax : (e : NatExpr σ) → Wire e → Expr (σ ⊕ Wire e)
  | .constant n, _ => .var (Sum.inr 0) - .constant (n : ℤ)
  | .var i, _ => .var (Sum.inr 0) - .var (Sum.inl i)
  | .add p q, Sum.inl _ =>
      .var (Sum.inr (Sum.inl 0)) - (.var (Sum.inr (Sum.inr (Sum.inl (root p)))) + .var (Sum.inr (Sum.inr (Sum.inr (root q)))))
  | .add p _, Sum.inr (Sum.inl k) =>
      (residualSyntax p k).rename (Sum.map id (fun j => Sum.inr (Sum.inl j)))
  | .add _ q, Sum.inr (Sum.inr k) =>
      (residualSyntax q k).rename (Sum.map id (fun j => Sum.inr (Sum.inr j)))
  | .mul p q, Sum.inl _ =>
      .var (Sum.inr (Sum.inl 0)) - .var (Sum.inr (Sum.inr (Sum.inl (root p)))) * .var (Sum.inr (Sum.inr (Sum.inr (root q))))
  | .mul p _, Sum.inr (Sum.inl k) =>
      (residualSyntax p k).rename (Sum.map id (fun j => Sum.inr (Sum.inl j)))
  | .mul _ q, Sum.inr (Sum.inr k) =>
      (residualSyntax q k).rename (Sum.map id (fun j => Sum.inr (Sum.inr j)))


end Gates

private def sumIndex {A B : Type*} {a b : ℕ} (f : A ≃ Fin a) (g : B ≃ Fin b) :
    A ⊕ B ≃ Fin (a + b) := (Equiv.sumCongr f g).trans finSumFinEquiv

/-- Original witnesses, left-tree nodes, right-tree nodes, and one normalization guard. -/
abbrev Witness {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :=
  Fin m ⊕ (Gates.Wire p ⊕ (Gates.Wire q ⊕ Fin 1))

/-- Guard, left-tree gates, right-tree gates, and equality of the two outputs. -/
abbrev Equation {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :=
  Fin 1 ⊕ (Gates.Wire p ⊕ (Gates.Wire q ⊕ Fin 1))

def witnessCount {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) : ℕ :=
  m + (Gates.count p + (Gates.count q + 1))

def witnessIndex {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    Witness p q ≃ Fin (witnessCount p q) :=
  sumIndex (Equiv.refl (Fin m))
    (sumIndex (Gates.index p) (sumIndex (Gates.index q) (Equiv.refl (Fin 1))))

def coordinate {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    Option (Witness p q) ≃ Fin (witnessCount p q + 1) :=
  (Equiv.optionCongr (witnessIndex p q)).trans (finSuccEquiv (witnessCount p q)).symm

@[simp] theorem coordinate_none {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    coordinate p q none = 0 := by simp [coordinate]

def initial {m : ℕ} {p q : NatExpr (Empty ⊕ Fin m)} :
    Empty ⊕ Fin m → Option (Witness p q) := Sum.elim Empty.elim (fun i => some (Sum.inl i))

def leftEmbedding {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    (Empty ⊕ Fin m) ⊕ Gates.Wire p → Option (Witness p q) :=
  Sum.elim initial (fun i => some (Sum.inr (Sum.inl i)))

def rightEmbedding {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    (Empty ⊕ Fin m) ⊕ Gates.Wire q → Option (Witness p q) :=
  Sum.elim initial (fun i => some (Sum.inr (Sum.inr (Sum.inl i))))

/-- Complete finite code for the quadratic residual system. -/
def residualSyntax {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    Equation p q → Expr (Option (Witness p q))
  | Sum.inl _ => .var (some (Sum.inr (Sum.inr (Sum.inr 0)))) - 1
  | Sum.inr (Sum.inl k) => (Gates.residualSyntax p k).rename (leftEmbedding p q)
  | Sum.inr (Sum.inr (Sum.inl k)) => (Gates.residualSyntax q k).rename (rightEmbedding p q)
  | Sum.inr (Sum.inr (Sum.inr _)) =>
      .var (some (Sum.inr (Sum.inl (Gates.root p)))) - .var (some (Sum.inr (Sum.inr (Sum.inl (Gates.root q)))))


end DiophantineConsistency.QuarticCompiler
