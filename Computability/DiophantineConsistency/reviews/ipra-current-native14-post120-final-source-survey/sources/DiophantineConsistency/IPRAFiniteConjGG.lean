import DiophantineConsistency.IPRARelationGGLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
set_option autoImplicit false
namespace DiophantineConsistency.IPRAFiniteConjGG
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRAQuantifierFree
open IPRANativeTheory IPRANativeAxiomImage IPRANativeEquationImages IPRANativeBasicImages
open IPRATwoImpLogic IPRARelationGGLogic
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L}

def conjTail : (n : ℕ) → (Fin n → Propositionᵢ L) → Propositionᵢ L → Propositionᵢ L
  | 0, _, t => t
  | n+1, f, t => f 0 ⋏ conjTail n (Matrix.vecTail f) t

theorem conjTail_to_nnMatrix : (n : ℕ) → (f : Fin n → Propositionᵢ L) →
    (t : Propositionᵢ L) → Λ ⊢ conjTail n (fun i => ∼∼f i) t 🡒 ∼∼(Matrix.conj f)
  | 0, _, t => by
    have ht : Λ ⊢! ∼∼(⊤ : Propositionᵢ L) := Entailment.mdp Entailment.dni Entailment.verum
    exact ⟨Entailment.mdp (HilbertProofᵢ.implyK _ t) ht⟩
  | n+1, f, t => by
    obtain ⟨hi⟩ := conjTail_to_nnMatrix n (Matrix.vecTail f) t
    obtain ⟨hn⟩ := nnConj (Λ := Λ) (f 0) (Matrix.conj (Matrix.vecTail f))
    apply Nonempty.intro
    exact Entailment.cast (Entailment.C_trans (Entailment.CKK_of_C_of_C Entailment.C_id hi) hn)
      (by simp [conjTail, Matrix.conj, Matrix.vecTail, Function.comp_def])
omit [L.DecidableEq] in
theorem ggMatrixConj (n : ℕ) (f : Fin n → Proposition L) :
    (Matrix.conj f)ᴺ = conjTail n (fun i => (f i)ᴺ) (∼⊥) := by
  induction n with
  | zero => simp [Matrix.conj, conjTail, Semiformula.doubleNegation_verum]
  | succ n ih => simp only [Matrix.conj, conjTail, Semiformula.doubleNegation_and, ih,
      Matrix.vecTail, Function.comp_def]
theorem ggFiniteConj (n : ℕ) (f : Fin n → Proposition L) (g : Fin n → Propositionᵢ L)
    (h : ∀ i, (f i)ᴺ = ∼∼g i) : Λ ⊢ (Matrix.conj f)ᴺ 🡒 ∼∼(Matrix.conj g) := by
  have hh := conjTail_to_nnMatrix (Λ := Λ) n g (∼⊥)
  simpa only [ggMatrixConj, h] using hh
omit [L.DecidableEq] in
theorem openAll_matrix (n k : ℕ) (f : Fin k → Semipropositionᵢ L n) :
    openAll n (Matrix.conj f) = Matrix.conj (fun i => openAll n (f i)) := by
  induction k with
  | zero => simp [Matrix.conj, openAll_top]
  | succ k ih =>
    simp [Matrix.conj, Matrix.vecTail, openAll_and, Function.comp_def, ih]

omit [L.DecidableEq] in
theorem openAllC_matrix (n k : ℕ) (f : Fin k → Semiproposition L n) :
    openAllC n (Matrix.conj f) = Matrix.conj (fun i => openAllC n (f i)) := by
  induction k with
  | zero => simp [Matrix.conj, openAllC_top]
  | succ k ih =>
    simp [Matrix.conj, Matrix.vecTail, openAllC_and, Function.comp_def, ih]
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

theorem finite_atomic_imp_image (n k : ℕ) {j : ℕ} (r : language.Rel j)
    (v w : Fin k → Semiterm language ℕ n) (u : Fin j → Semiterm language ℕ n) :
    (𝗜𝗻𝘁¹ : Hilbertᵢ language) ⊢
      openAll n ((Matrix.conj fun i => Semiformulaᵢ.rel Language.ORing.Rel.eq ![v i,w i]) 🡒
        Semiformulaᵢ.rel r u) 🡒
      openAll n (((Matrix.conj fun i => Semiformula.rel Language.ORing.Rel.eq ![v i,w i]) 🡒
        Semiformula.rel r u)ᴺ) := by
  let A : Fin k → Propositionᵢ language := fun i =>
    openAll n (Semiformulaᵢ.rel Language.ORing.Rel.eq ![v i,w i])
  let AC : Fin k → Proposition language := fun i =>
    openAllC n (Semiformula.rel Language.ORing.Rel.eq ![v i,w i])
  let R := openAll n (Semiformulaᵢ.rel r u)
  let RC := openAllC n (Semiformula.rel r u)
  have ha : ∀ i, (AC i)ᴺ = ∼∼A i := by
    intro i
    dsimp [AC,A]
    rw [←openAll_gg]
    simp only [Semiformula.doubleNegation_rel, openAll_neg]
  have hr : RCᴺ = ∼∼R := by
    dsimp [RC,R]
    rw [←openAll_gg]
    simp only [Semiformula.doubleNegation_rel, openAll_neg]
  have hg := Derivation.imply_doubleNegation (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ language)) (Matrix.conj AC) RC
  rw [hr] at hg
  obtain ⟨hg⟩ := hg
  obtain ⟨hc⟩ := ggFiniteConj (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ language)) k AC A ha
  have h := Entailment.C_trans Entailment.CCCNNNN
    (Entailment.C_trans (Entailment.CCC_of_C_left hc) (Entailment.K_left hg))
  apply Nonempty.intro
  exact Entailment.cast h (by
    simp only [openAll_imp, openAll_gg, openAllC_imp, openAll_matrix, openAllC_matrix,
      A, AC, R, RC])
theorem emb_matrix (n k : ℕ) (f : Fin k → Semisentenceᵢ language n) :
    Rewriting.emb (Matrix.conj f) = (Matrix.conj fun i => Rewriting.emb (f i) : Semipropositionᵢ language n) := by
  induction k with
  | zero => simp [Matrix.conj]
  | succ k ih => simp [Matrix.conj, Matrix.vecTail, LogicalConnective.HomClass.map_and, Function.comp_def, ih]

theorem finite_atomic_imp_closure {n k j : ℕ} (r : language.Rel j)
    (v w : Fin k → TermN n) (u : Fin j → TermN n) : nativeTheory ⊢
      (∀⁰* ((Matrix.conj fun i => Semiformulaᵢ.rel Language.ORing.Rel.eq ![v i,w i]) 🡒
        Semiformulaᵢ.rel r u)) 🡒
      (∀⁰* ((Matrix.conj fun i => Semiformula.rel Language.ORing.Rel.eq ![v i,w i]) 🡒
        Semiformula.rel r u))ᴺ := by
  have h := finite_atomic_imp_image n k r (fun i => Rew.emb (v i))
    (fun i => Rew.emb (w i)) (fun i => Rew.emb (u i))
  have hh := allClosure_imp n _ _ h
  have hv (i : Fin k) : (fun j => (Rew.emb : Rew language Empty n ℕ n) (![v i,w i] j)) = ![Rew.emb (v i), Rew.emb (w i)] := by
    funext j
    cases j using Fin.cases with
    | zero => rfl
    | succ x => cases x using Fin.cases with
      | zero => rfl
      | succ x => exact Fin.elim0 x
  obtain ⟨hh⟩ := hh
  apply Nonempty.intro
  apply Theoryᵢ.ofHilbert
  simpa [gg_allClosure, LogicalConnective.HomClass.map_imply, Rewriting.emb,
    Semiformula.rew_doubleNegation, Semiformulaᵢ.rew_rel, Function.comp_def, emb_matrix, hv] using hh
def functionCongruenceI {k : ℕ} (f : language.Func k) : Sentenceᵢ language :=
  ∀⁰* (((Matrix.conj fun i => Semiformulaᵢ.rel Language.ORing.Rel.eq
    ![.bvar (Fin.addCast k i), .bvar (i.addNat k)]) 🡒
      Semiformulaᵢ.rel Language.ORing.Rel.eq
        ![.func f (fun i => .bvar (Fin.addCast k i)),
          .func f (fun i => .bvar (i.addNat k))]) : Semisentenceᵢ language (k+k))

theorem functionCongruence_adapter {k : ℕ} (f : language.Func k) :
    nativeTheory ⊢ functionCongruenceI f 🡒 (Theory.Eq.funcExt f)ᴺ := by
  have h := finite_atomic_imp_closure (n := k+k) Language.ORing.Rel.eq
    (fun i : Fin k => .bvar (Fin.addCast k i)) (fun i : Fin k => .bvar (i.addNat k))
    ![.func f (fun i => .bvar (Fin.addCast k i)), .func f (fun i => .bvar (i.addNat k))]
  simp only [functionCongruenceI, Theory.Eq.funcExt]
  convert h using 1
  congr 2
end DiophantineConsistency.IPRAFiniteConjGG
