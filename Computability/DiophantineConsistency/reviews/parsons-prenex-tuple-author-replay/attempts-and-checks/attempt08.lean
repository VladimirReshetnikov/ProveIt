import DiophantineConsistency.ParsonsPrenexPiTwoOr

/-! Tupled normalization for finite ∀∃ blocks, with free parameters. -/
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsPrenexTuple
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule ParsonsSpecialize
variable {L : Language} [L.ORing]

def leftIndex (n₁ k₁ n₂ k₂ : ℕ) (i : Fin (n₁+k₁)) : Fin ((n₂+n₁)+(k₂+k₁)) :=
  if h : i.val < k₁ then ⟨i.val, by omega⟩
  else ⟨(k₂+k₁) + (i.val-k₁), by omega⟩

def rightIndex (n₁ k₁ n₂ k₂ : ℕ) (i : Fin (n₂+k₂)) : Fin ((n₂+n₁)+(k₂+k₁)) :=
  if h : i.val < k₂ then ⟨k₁+i.val, by omega⟩
  else ⟨(k₂+k₁) + n₁ + (i.val-k₂), by omega⟩

def leftMap (n₁ k₁ n₂ k₂ : ℕ) : Rew L ℕ (n₁+k₁) ℕ ((n₂+n₁)+(k₂+k₁)) :=
  Rew.bind (fun i => .bvar (leftIndex n₁ k₁ n₂ k₂ i)) .fvar

def rightMap (n₁ k₁ n₂ k₂ : ℕ) : Rew L ℕ (n₂+k₂) ℕ ((n₂+n₁)+(k₂+k₁)) :=
  Rew.bind (fun i => .bvar (rightIndex n₁ k₁ n₂ k₂ i)) .fvar

def splitLeft {α : Type} {a b : ℕ} (e : Fin (b+a) → α) : Fin a → α := fun i => e (i.addCast b)
def splitRight {α : Type} {a b : ℕ} (e : Fin (b+a) → α) : Fin b → α := fun i => e (i.addNat a)

theorem appendr_left {α : Type} {a b : ℕ} (v : Fin a → α) (w : Fin b → α) :
    splitLeft (Matrix.appendr v w) = v := by
  funext i
  simp [splitLeft]

theorem appendr_right {α : Type} {a b : ℕ} (v : Fin a → α) (w : Fin b → α) :
    splitRight (Matrix.appendr v w) = w := by
  funext i
  simp [splitRight]

theorem left_projection {α : Type} (n₁ k₁ n₂ k₂ : ℕ)
    (w : Fin (k₂+k₁) → α) (x : Fin (n₂+n₁) → α) :
    (fun i => Matrix.appendr w x (leftIndex n₁ k₁ n₂ k₂ i)) =
      Matrix.appendr (splitLeft w) (splitLeft x) := by
  funext i
  simp only [Matrix.appendr, Matrix.vecAppend_eq_ite, leftIndex, splitLeft]
  split <;> split
  · congr 1
  · rename_i h₁ h₂
    exfalso
    apply h₂
    change i.val < k₂ + k₁
    omega
  · rename_i h₁ h₂
    exfalso
    change k₂ + k₁ + (i.val-k₁) < k₂+k₁ at h₂
    omega
  · congr 1
    apply Fin.ext
    simp

theorem right_projection {α : Type} (n₁ k₁ n₂ k₂ : ℕ)
    (w : Fin (k₂+k₁) → α) (x : Fin (n₂+n₁) → α) :
    (fun i => Matrix.appendr w x (rightIndex n₁ k₁ n₂ k₂ i)) =
      Matrix.appendr (splitRight w) (splitRight x) := by
  funext i
  simp only [Matrix.appendr, Matrix.vecAppend_eq_ite, rightIndex, splitRight]
  split <;> split
  · congr 1
    apply Fin.ext
    simp [Nat.add_comm]
  · rename_i h₁ h₂
    exfalso
    apply h₂
    change k₁+i.val < k₂+k₁
    omega
  · rename_i h₁ h₂
    exfalso
    change k₂+k₁+n₁+(i.val-k₂) < k₂+k₁ at h₂
    omega
  · congr 1
    apply Fin.ext
    simp
    omega

def block {n k : ℕ} (A : Semiproposition L (n+k)) : Proposition L :=
  ∀⁰* (∃⁰^[k] A)

def matrixOr {n₁ k₁ n₂ k₂ : ℕ} (A : Semiproposition L (n₁+k₁))
    (B : Semiproposition L (n₂+k₂)) : Semiproposition L ((n₂+n₁)+(k₂+k₁)) :=
  (leftMap n₁ k₁ n₂ k₂ ▹ A) ⋎ (rightMap n₁ k₁ n₂ k₂ ▹ B)

def matrixAnd {n₁ k₁ n₂ k₂ : ℕ} (A : Semiproposition L (n₁+k₁))
    (B : Semiproposition L (n₂+k₂)) : Semiproposition L ((n₂+n₁)+(k₂+k₁)) :=
  (leftMap n₁ k₁ n₂ k₂ ▹ A) ⋏ (rightMap n₁ k₁ n₂ k₂ ▹ B)

theorem matrixOr_bounded {n₁ k₁ n₂ k₂ : ℕ} (A : Semiproposition L (n₁+k₁))
    (B : Semiproposition L (n₂+k₂)) (hA : Hierarchy 𝚺 0 A) (hB : Hierarchy 𝚺 0 B) :
    Hierarchy 𝚺 0 (matrixOr A B) := by
  simp [matrixOr, Hierarchy.rew _ hA, Hierarchy.rew _ hB]

theorem matrixAnd_bounded {n₁ k₁ n₂ k₂ : ℕ} (A : Semiproposition L (n₁+k₁))
    (B : Semiproposition L (n₂+k₂)) (hA : Hierarchy 𝚺 0 A) (hB : Hierarchy 𝚺 0 B) :
    Hierarchy 𝚺 0 (matrixAnd A B) := by
  simp [matrixAnd, Hierarchy.rew _ hA, Hierarchy.rew _ hB]

section models
variable {M : Type} [Nonempty M] [Structure L M] [Structure.Eq L M]

omit [L.ORing] [Nonempty M] [Structure.Eq L M] in
theorem eval_block {n k : ℕ} (A : Semiproposition L (n+k)) (f : ℕ → M) :
    (block A).Eval ![] f ↔ ∀ x : Fin n → M, ∃ y : Fin k → M,
      A.Eval (Matrix.appendr y x) f := by
  simp [block]

omit [L.ORing] [Nonempty M] [Structure.Eq L M] in
theorem eval_matrixOr {n₁ k₁ n₂ k₂ : ℕ} (A : Semiproposition L (n₁+k₁))
    (B : Semiproposition L (n₂+k₂)) (w : Fin (k₂+k₁) → M) (x : Fin (n₂+n₁) → M) (f : ℕ → M) :
    (matrixOr A B).Eval (Matrix.appendr w x) f ↔
      A.Eval (Matrix.appendr (splitLeft w) (splitLeft x)) f ∨
        B.Eval (Matrix.appendr (splitRight w) (splitRight x)) f := by
  simp [matrixOr, Semiformula.eval_rew, leftMap, rightMap, Function.comp_def,
    left_projection, right_projection]

omit [L.ORing] [Nonempty M] [Structure.Eq L M] in
theorem eval_matrixAnd {n₁ k₁ n₂ k₂ : ℕ} (A : Semiproposition L (n₁+k₁))
    (B : Semiproposition L (n₂+k₂)) (w : Fin (k₂+k₁) → M) (x : Fin (n₂+n₁) → M) (f : ℕ → M) :
    (matrixAnd A B).Eval (Matrix.appendr w x) f ↔
      A.Eval (Matrix.appendr (splitLeft w) (splitLeft x)) f ∧
        B.Eval (Matrix.appendr (splitRight w) (splitRight x)) f := by
  simp [matrixAnd, Semiformula.eval_rew, leftMap, rightMap, Function.comp_def,
    left_projection, right_projection]

end models
end DiophantineConsistency.ParsonsPrenexTuple
