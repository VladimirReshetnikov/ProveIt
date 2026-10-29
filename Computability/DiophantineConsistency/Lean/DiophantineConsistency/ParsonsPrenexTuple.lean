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

omit [L.ORing] [Structure.Eq L M] in
theorem semantic_or {n₁ k₁ n₂ k₂ : ℕ} (A : Semiproposition L (n₁+k₁))
    (B : Semiproposition L (n₂+k₂)) (f : ℕ → M) :
    ((block A).Eval ![] f ∨ (block B).Eval ![] f) ↔ (block (matrixOr A B)).Eval ![] f := by
  simp only [eval_block, eval_matrixOr]
  classical
  constructor
  · rintro (h | h) x
    · obtain ⟨y,hy⟩ := h (splitLeft x)
      refine ⟨Matrix.appendr y (fun _ => Classical.choice ‹Nonempty M›), ?_⟩
      left
      simpa [appendr_left] using hy
    · obtain ⟨v,hv⟩ := h (splitRight x)
      refine ⟨Matrix.appendr (fun _ => Classical.choice ‹Nonempty M›) v, ?_⟩
      right
      simpa [appendr_right] using hv
  · intro h
    by_contra hn
    push Not at hn
    obtain ⟨⟨x,hx⟩,⟨u,hu⟩⟩ := hn
    obtain ⟨w,hw⟩ := h (Matrix.appendr x u)
    simp only [appendr_left, appendr_right] at hw
    rcases hw with hw | hw
    · exact hx (splitLeft w) hw
    · exact hu (splitRight w) hw

omit [L.ORing] [Structure.Eq L M] in
theorem semantic_and {n₁ k₁ n₂ k₂ : ℕ} (A : Semiproposition L (n₁+k₁))
    (B : Semiproposition L (n₂+k₂)) (f : ℕ → M) :
    ((block A).Eval ![] f ∧ (block B).Eval ![] f) ↔ (block (matrixAnd A B)).Eval ![] f := by
  simp only [eval_block, eval_matrixAnd]
  classical
  constructor
  · rintro ⟨hA,hB⟩ x
    obtain ⟨y,hy⟩ := hA (splitLeft x)
    obtain ⟨v,hv⟩ := hB (splitRight x)
    refine ⟨Matrix.appendr y v, ?_⟩
    simpa [appendr_left, appendr_right] using And.intro hy hv
  · intro h
    constructor
    · intro x
      obtain ⟨w,hw⟩ := h (Matrix.appendr x (fun _ => Classical.choice ‹Nonempty M›))
      simp only [appendr_left, appendr_right] at hw
      exact ⟨splitLeft w, hw.1⟩
    · intro u
      obtain ⟨w,hw⟩ := h (Matrix.appendr (fun _ => Classical.choice ‹Nonempty M›) u)
      simp only [appendr_left, appendr_right] at hw
      exact ⟨splitRight w, hw.2⟩

end models

/-- Lift a pointwise semantic implication with free parameters to an actual
rule-calculus proof, using Foundation completeness in the Lean metatheory. -/
noncomputable def proofOfSemanticImplication (P Q : Proposition ℒₒᵣ)
    (H : ∀ (M : Type) [Nonempty M] [Structure ℒₒᵣ M] [Structure.Eq ℒₒᵣ M]
      (f : ℕ → M), P.Eval ![] f → Q.Eval ![] f) : Proof 𝗣𝗔⁻ (P 🡒 Q) := by
  let R : Proposition ℒₒᵣ := P 🡒 Q
  have h : 𝗣𝗔⁻ ⊢ R.univCl := by
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    simp only [models_iff_proposition]
    intro f
    change (P 🡒 Q).Eval ![] f
    simp only [Semiformula.imp_eq, Semiformula.Eval]
    classical
    by_cases hp : P.Eval ![] f
    · exact Or.inr (H M f hp)
    · left
      rw [Semiformula.EvalAux_neg]
      intro hx
      apply hp
      exact hx
  have hc : Proof 𝗣𝗔⁻ (R.univCl : Proposition ℒₒᵣ) :=
    ParsonsRuleEmbedding.embedTheory h.some
  exact specialize_univCl R hc

/-- Pair two arbitrary strict ∀∃ blocks under disjunction. -/
noncomputable def orForward {n₁ k₁ n₂ k₂ : ℕ}
    (A : ArithmeticSemiformula ℕ (n₁+k₁)) (B : ArithmeticSemiformula ℕ (n₂+k₂))
    (h : Proof 𝗣𝗔⁻ (block A ⋎ block B)) : Proof 𝗣𝗔⁻ (block (matrixOr A B)) := by
  apply Proof.mp (proofOfSemanticImplication (block A ⋎ block B) (block (matrixOr A B)) ?_) h
  intro M _ _ _ f hs
  exact (semantic_or A B f).mp hs

noncomputable def orBackward {n₁ k₁ n₂ k₂ : ℕ}
    (A : ArithmeticSemiformula ℕ (n₁+k₁)) (B : ArithmeticSemiformula ℕ (n₂+k₂))
    (h : Proof 𝗣𝗔⁻ (block (matrixOr A B))) : Proof 𝗣𝗔⁻ (block A ⋎ block B) := by
  apply Proof.mp (proofOfSemanticImplication (block (matrixOr A B)) (block A ⋎ block B) ?_) h
  intro M _ _ _ f hs
  exact (semantic_or A B f).mpr hs

/-- Pair two arbitrary strict ∀∃ blocks under conjunction. -/
noncomputable def andForward {n₁ k₁ n₂ k₂ : ℕ}
    (A : ArithmeticSemiformula ℕ (n₁+k₁)) (B : ArithmeticSemiformula ℕ (n₂+k₂))
    (h : Proof 𝗣𝗔⁻ (block A ⋏ block B)) : Proof 𝗣𝗔⁻ (block (matrixAnd A B)) := by
  apply Proof.mp (proofOfSemanticImplication (block A ⋏ block B) (block (matrixAnd A B)) ?_) h
  intro M _ _ _ f hs
  exact (semantic_and A B f).mp hs

noncomputable def andBackward {n₁ k₁ n₂ k₂ : ℕ}
    (A : ArithmeticSemiformula ℕ (n₁+k₁)) (B : ArithmeticSemiformula ℕ (n₂+k₂))
    (h : Proof 𝗣𝗔⁻ (block (matrixAnd A B))) : Proof 𝗣𝗔⁻ (block A ⋏ block B) := by
  apply Proof.mp (proofOfSemanticImplication (block (matrixAnd A B)) (block A ⋏ block B) ?_) h
  intro M _ _ _ f hs
  exact (semantic_and A B f).mpr hs

end DiophantineConsistency.ParsonsPrenexTuple
