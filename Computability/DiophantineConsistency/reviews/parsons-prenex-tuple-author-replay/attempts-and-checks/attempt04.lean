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
  split <;> split <;> simp_all <;> try omega

theorem right_projection {α : Type} (n₁ k₁ n₂ k₂ : ℕ)
    (w : Fin (k₂+k₁) → α) (x : Fin (n₂+n₁) → α) :
    (fun i => Matrix.appendr w x (rightIndex n₁ k₁ n₂ k₂ i)) =
      Matrix.appendr (splitRight w) (splitRight x) := by
  funext i
  simp only [Matrix.appendr, Matrix.vecAppend_eq_ite, rightIndex, splitRight]
  split <;> split <;> simp_all <;> try omega

end DiophantineConsistency.ParsonsPrenexTuple
