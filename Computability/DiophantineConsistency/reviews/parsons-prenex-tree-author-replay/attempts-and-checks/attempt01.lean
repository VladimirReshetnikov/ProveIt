import DiophantineConsistency.ParsonsPrenexTuple

/-! Normalize finite Boolean trees of tupled ∀∃ blocks. -/
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsPrenexTree
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule ParsonsPrenexTuple

inductive Tree : ℕ → ℕ → Type
  | leaf {n k : ℕ} (A : ArithmeticSemiformula ℕ (n+k)) : Tree n k
  | disj {n₁ k₁ n₂ k₂ : ℕ} (A : Tree n₁ k₁) (B : Tree n₂ k₂) : Tree (n₂+n₁) (k₂+k₁)
  | conj {n₁ k₁ n₂ k₂ : ℕ} (A : Tree n₁ k₁) (B : Tree n₂ k₂) : Tree (n₂+n₁) (k₂+k₁)

def matrix : {n k : ℕ} → Tree n k → ArithmeticSemiformula ℕ (n+k)
  | _, _, .leaf A => A
  | _, _, .disj A B => matrixOr (matrix A) (matrix B)
  | _, _, .conj A B => matrixAnd (matrix A) (matrix B)

def source : {n k : ℕ} → Tree n k → Proposition ℒₒᵣ
  | _, _, .leaf A => block A
  | _, _, .disj A B => source A ⋎ source B
  | _, _, .conj A B => source A ⋏ source B

def bounded : {n k : ℕ} → Tree n k → Prop
  | _, _, .leaf A => Hierarchy 𝚺 0 A
  | _, _, .disj A B => bounded A ∧ bounded B
  | _, _, .conj A B => bounded A ∧ bounded B

theorem matrix_bounded {n k : ℕ} (t : Tree n k) (h : bounded t) : Hierarchy 𝚺 0 (matrix t) := by
  induction t with
  | leaf A => exact h
  | disj A B ihA ihB => exact matrixOr_bounded _ _ (ihA h.1) (ihB h.2)
  | conj A B ihA ihB => exact matrixAnd_bounded _ _ (ihA h.1) (ihB h.2)

end DiophantineConsistency.ParsonsPrenexTree
