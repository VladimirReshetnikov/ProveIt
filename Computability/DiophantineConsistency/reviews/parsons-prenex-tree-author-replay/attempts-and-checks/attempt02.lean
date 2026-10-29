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

section models
variable {M : Type} [Nonempty M] [Structure ℒₒᵣ M]

theorem semantic {n k : ℕ} (t : Tree n k) (f : ℕ → M) :
    (source t).Eval ![] f ↔ (block (matrix t)).Eval ![] f := by
  induction t with
  | leaf A => rfl
  | disj A B ihA ihB =>
      change ((source A).Eval ![] f ∨ (source B).Eval ![] f) ↔
        (block (matrixOr (matrix A) (matrix B))).Eval ![] f
      rw [ihA, ihB]
      exact semantic_or (matrix A) (matrix B) f
  | conj A B ihA ihB =>
      change ((source A).Eval ![] f ∧ (source B).Eval ![] f) ↔
        (block (matrixAnd (matrix A) (matrix B))).Eval ![] f
      rw [ihA, ihB]
      exact semantic_and (matrix A) (matrix B) f

end models

noncomputable def forward {n k : ℕ} (t : Tree n k)
    (h : Proof 𝗣𝗔⁻ (source t)) : Proof 𝗣𝗔⁻ (block (matrix t)) := by
  apply Proof.mp (proofOfSemanticImplication (source t) (block (matrix t)) ?_) h
  intro M _ _ _ f hs
  exact (semantic t f).mp hs

noncomputable def backward {n k : ℕ} (t : Tree n k)
    (h : Proof 𝗣𝗔⁻ (block (matrix t))) : Proof 𝗣𝗔⁻ (source t) := by
  apply Proof.mp (proofOfSemanticImplication (block (matrix t)) (source t) ?_) h
  intro M _ _ _ f hs
  exact (semantic t f).mpr hs

end DiophantineConsistency.ParsonsPrenexTree
