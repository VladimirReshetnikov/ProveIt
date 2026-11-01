import DiophantineConsistency.HerbrandContextualTreeWitness
import DiophantineConsistency.HerbrandParameterizedWitness
import DiophantineConsistency.PRAContextualWitnessChoice
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandContextualTreeSelection
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAUniversalSyntax PRAUniversalCandidate
  PRAUniversalEquivalence PRAHerbrandSelection HerbrandSchedule HerbrandParameterizedWitness HerbrandUniversalTree
  PRAContextualWitnessChoice

def parameterSide {n : ℕ} (side : Semisentence language n) : Proposition language :=
  Rew.embSubsts (fun i : Fin n => .fvar i.val) ▹ side

/-- The embedded side reads its parameters from the corresponding free variables. -/
theorem parameterSide_eval {M : Type} [Structure language M] {n : ℕ}
    (side : Semisentence language n) (e : ℕ → M) :
    (parameterSide side).Eval ![] e ↔ side.Eval (fun i : Fin n => e i.val) Empty.elim := by
  unfold parameterSide
  rw [Semiformula.eval_rew]
  have hb : (Semiterm.val (L := language) ![] e ∘
      Rew.embSubsts (fun i : Fin n => .fvar i.val) ∘ Semiterm.bvar) =
      (fun i : Fin n => e i.val) := by
    funext i
    rfl
  have hf : (Semiterm.val (L := language) ![] e ∘
      Rew.embSubsts (fun i : Fin n => .fvar i.val) ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hb,hf]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* UniversalAxiom]

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* UniversalAxiom] in
theorem modelParameterSide {n : ℕ} (side : Semisentence language n) (e : Fin n → M) :
    (parameterSide side).Eval ![] (parameterEnv n e) ↔ side.Eval e Empty.elim := by
  rw [parameterSide_eval]
  have he : (fun i : Fin n => parameterEnv n e i.val) = e := by
    funext i
    simp [parameterEnv]
  rw [he]

end models

/-- Convert contextual syntactic term instances into a finite code list and
use candidate PRA's contextual selector. -/
theorem PRA_exists_contextualSelection {n : ℕ} (side : Semisentence language n)
    (φ : Semisentence language (n+1)) (hφ : φ.Open)
    (hside : UniversalTree (∼(parameterSide side)))
    (p : UniversalAxiom ⊢ ((parameterSide side) ⋎ (∃⁰ (parameterMatrix φ))).univCl) :
    ∃ c : Code n, Primrec (eval c) ∧ PRA ⊢ (∀⁰* (side ⋎ openMatrixAt φ c)) := by
  have hmatrix := parameterMatrix_open φ hφ
  have p' : UniversalAxiom ⊢ ((∼(∼parameterSide side)) ⋎ (∃⁰ (parameterMatrix φ))).univCl := by
    simpa using p
  obtain ⟨k,hk⟩ := HerbrandContextualTreeWitness.universal_proves_contextual (∼parameterSide side) hside
    (parameterMatrix φ) hmatrix p'
  let terms := (List.range k).map candidate
  let codes := terms.map (parameterCode n)
  have hc : PRA ⊢ (∀⁰* (side ⋎ openMatrixList φ (.zero n) codes)) := by
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M hM0 hM hEq hPRA
    letI : M↓[language] ⊧* UniversalAxiom := by
      constructor
      intro σ hσ
      exact models_of_provable hPRA (PRA_proves_universalAxiom hσ)
    have hpra := candidate_proves_universal hk
    have hh := models_of_provable hPRA hpra
    simp only [models_iff, Semiformula.eval_univCl] at hh
    simp only [models_iff, Semiformula.eval_allClosure]
    intro e
    have hval := hh (parameterEnv n e)
    change ((∼(∼parameterSide side)).Eval ![] (parameterEnv n e) ∨
      (HerbrandContextualTreeWitness.termOutput (parameterMatrix φ) (List.range k)).Eval ![] (parameterEnv n e)) at hval
    rw [LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_neg] at hval
    change side.Eval e Empty.elim ∨ (openMatrixList φ (.zero n) codes).Eval e Empty.elim
    rcases hval with hs | ht
    · exact Or.inl ((modelParameterSide side e).mp (Classical.not_not.mp hs))
    · obtain ⟨j,hj,hjval⟩ := (HerbrandContextualTreeWitness.output_eval (parameterMatrix φ) _ _).mp ht
      apply Or.inr
      apply modelListMember φ (.zero n) codes (parameterCode n (candidate j))
      · dsimp [codes, terms]
        exact List.mem_map.mpr ⟨candidate j, List.mem_map.mpr ⟨j,hj,rfl⟩, rfl⟩
      · exact modelParameterInstance φ (candidate j) e hjval
  exact PRA_exists_contextualWitness side φ hφ (.zero n) codes hc
/-- Existential side trees need no prenex rearrangement before contextual selection. -/
theorem PRA_exists_existentialSideSelection {n : ℕ} (side : Semisentence language n)
    (φ : Semisentence language (n+1)) (hφ : φ.Open)
    (hside : ExistentialTree (parameterSide side))
    (p : UniversalAxiom ⊢ ((parameterSide side) ⋎ (∃⁰ (parameterMatrix φ))).univCl) :
    ∃ c : Code n, Primrec (eval c) ∧ PRA ⊢ (∀⁰* (side ⋎ openMatrixAt φ c)) :=
  PRA_exists_contextualSelection side φ hφ (neg_tree hside) p
end DiophantineConsistency.HerbrandContextualTreeSelection
