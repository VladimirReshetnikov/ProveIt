import DiophantineConsistency.PRAUniversalCandidate
import DiophantineConsistency.PRAFormulaParameters
import DiophantineConsistency.PRAOpenOneInduction
set_option autoImplicit false
namespace DiophantineConsistency.PRAPiOneImplication
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory

def matrix (p q : Semisentence language 1) : Semiproposition language 1 :=
  (∼ (Rew.embSubsts ![#0] ▹ p)) ⋎ (Rew.embSubsts ![&0] ▹ q)

theorem matrix_open (p q : Semisentence language 1) (hp : p.Open) (hq : q.Open) :
    (matrix p q).Open := by
  change p.qr = 0 at hp
  change q.qr = 0 at hq
  simp [matrix, Semiformula.Open, PRAFormulaParameters.qr_rew, hp, hq]

def normal (p q : Semisentence language 1) : Sentence language :=
  (∃⁰ matrix p q).univCl

def implication (p q : Semisentence language 1) : Sentence language :=
  (∀⁰ p) 🡒 (∀⁰ q)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]

omit [Nonempty M] [Structure.Eq language M] in
theorem matrix_eval (p q : Semisentence language 1) (e : ℕ → M) (x : M) :
    (matrix p q).Eval ![x] e ↔ ¬ p.Eval ![x] Empty.elim ∨ q.Eval ![e 0] Empty.elim := by
  simp [matrix, Semiformula.eval_rew, Function.comp_def, Rew.embSubsts]
  have h₀ : (fun _ : Fin 1 => x) = ![x] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  have h₁ : (fun _ : Fin 1 => e 0) = ![e 0] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  have h₂ : (fun z : Empty => Semiterm.val (L := language) ![x] e z.elim) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  simp [h₀, h₁, h₂]

omit [Structure.Eq language M] in
theorem model_equiv (p q : Semisentence language 1) :
    M↓[language] ⊧ implication p q ↔ M↓[language] ⊧ normal p q := by
  simp only [models_iff, implication, normal, Semiformula.eval_univCl,
    Semantics.Imp.models_imply, Semiformula.eval_all, Semiformula.eval_ex, matrix_eval]
  classical
  constructor
  · intro h e
    by_cases hp : ∀ x : M, p.Eval ![x] Empty.elim
    · obtain ⟨d⟩ := ‹Nonempty M›
      exact ⟨d, Or.inr (h hp (e 0))⟩
    · push Not at hp
      obtain ⟨x,hx⟩ := hp
      exact ⟨x, Or.inl hx⟩
  · intro h hp y
    let e : ℕ → M := fun _ => y
    obtain ⟨x,hx⟩ := h e
    exact hx.resolve_left (fun hn => hn (hp x))
end models

theorem proves_normal_iff (p q : Semisentence language 1) :
    (PRA ⊢ implication p q) ↔ (PRA ⊢ normal p q) := by
  letI : 𝗘𝗤 language ⪯ PRA := Entailment.WeakerThan.ofSubset (fun _ h => Or.inl (Or.inl (Or.inl h)))
  constructor <;> intro h
  · apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ hM
    exact (model_equiv p q).mp (models_of_provable hM h)
  · apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ hM
    exact (model_equiv p q).mpr (models_of_provable hM h)

/-- Classical PRA proves the equivalence exactly when it proves both
open-existential normalizations. This does not itself establish either proof. -/
theorem proves_equivalence_iff (p q : Semisentence language 1) :
    (PRA ⊢ ((∀⁰ p) 🡘 (∀⁰ q))) ↔
      (PRA ⊢ normal p q) ∧ (PRA ⊢ normal q p) := by
  letI : 𝗘𝗤 language ⪯ PRA := Entailment.WeakerThan.ofSubset (fun _ h => Or.inl (Or.inl (Or.inl h)))
  constructor
  · intro h
    constructor <;> apply Theory.Proof.complete_on_eq_models.{0,0}
    · intro M _ _ _ hM
      have hm := models_of_provable hM h
      simp only [LogicalConnective.iff, Semantics.And.models_and] at hm
      have hi : M↓[language] ⊧ implication p q := by
        exact hm.1
      exact (model_equiv p q).mp hi
    · intro M _ _ _ hM
      have hm := models_of_provable hM h
      simp only [LogicalConnective.iff, Semantics.And.models_and] at hm
      have hi : M↓[language] ⊧ implication q p := by
        exact hm.2
      exact (model_equiv q p).mp hi
  · intro ⟨hp,hq⟩
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ hM
    have hmp := (model_equiv p q).mpr (models_of_provable hM hp)
    have hmq := (model_equiv q p).mpr (models_of_provable hM hq)
    simpa only [models_iff, LogicalConnective.iff, Semantics.And.models_and, implication] using ⟨hmp,hmq⟩

/-- Eliminate one closed open-Σ₁ induction instance from the equivalence of
 two unary, open-matrix Π₁ sentences. No use is made of standard-model truth. -/
theorem eliminate_one_from_equivalence (ψ : Semisentence language 3) (hψ : ψ.Open)
    (p q : Semisentence language 1) (hp : p.Open) (hq : q.Open)
    (h : (PRA ∪ {(succInd (PRAOpenOneInduction.openSigma ψ)).univCl}) ⊢
      ((∀⁰ p) 🡘 (∀⁰ q))) : PRA ⊢ ((∀⁰ p) 🡘 (∀⁰ q)) := by
  let T := PRA ∪ {(succInd (PRAOpenOneInduction.openSigma ψ)).univCl}
  letI : 𝗘𝗤 language ⪯ T := Entailment.WeakerThan.ofSubset (fun _ h => Or.inl (Or.inl (Or.inl (Or.inl h))))
  have hn₁ : T ⊢ normal p q := by
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ hM
    have hm := models_of_provable hM h
    simp only [LogicalConnective.iff, Semantics.And.models_and] at hm
    exact (model_equiv p q).mp hm.1
  have hn₂ : T ⊢ normal q p := by
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ hM
    have hm := models_of_provable hM h
    simp only [LogicalConnective.iff, Semantics.And.models_and] at hm
    exact (model_equiv q p).mp hm.2
  apply (proves_equivalence_iff p q).mpr
  exact ⟨PRAOpenOneInduction.PRA_proves_goal_of_openSuccInd ψ hψ (matrix p q) (matrix_open p q hp hq) hn₁,
    PRAOpenOneInduction.PRA_proves_goal_of_openSuccInd ψ hψ (matrix q p) (matrix_open q p hq hp) hn₂⟩
end DiophantineConsistency.PRAPiOneImplication
