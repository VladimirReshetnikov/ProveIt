import DiophantineConsistency.HerbrandTripleParameterized
import DiophantineConsistency.PRAInductionCounterexample
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandPackedTriple
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAFormulaParameters HerbrandTripleParameterized

def packedTriple (φ : Semiproposition language 3) : Semisentence language (φ.fvSup+3) := by
  exact cast (congrArg (Semisentence language) (Nat.add_comm 3 φ.fvSup)) (packParameters φ)

theorem packedTriple_open (φ : Semiproposition language 3) (h : φ.Open) : (packedTriple φ).Open := by
  have hc {a b : ℕ} (eq : a = b) (ψ : Semisentence language a) :
      ψ.Open → (cast (congrArg (Semisentence language) eq) ψ).Open := by
    cases eq
    exact id
  exact hc (Nat.add_comm 3 φ.fvSup) _ (packParameters_open φ h)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]

omit [Structure.Eq language M] in
theorem modelPackedTriple (φ : Semiproposition language 3)
    (h : M↓[language] ⊧ (∃⁰ ∃⁰ ∃⁰ φ).univCl) :
    M↓[language] ⊧ (∀⁰* ∃⁰ ∃⁰ ∃⁰ packedTriple φ) := by
  simp only [models_iff, Semiformula.eval_univCl, Semiformula.eval_ex] at h
  simp only [models_iff, Semiformula.eval_allClosure, Semiformula.eval_ex]
  intro e
  let fallback : M := Classical.choice (inferInstance : Nonempty M)
  let env : ℕ → M := fun i => if hi : i < φ.fvSup then e ⟨i,hi⟩ else fallback
  obtain ⟨x,y,z,hxyz⟩ := h env
  refine ⟨x,y,z,?_⟩
  unfold packedTriple
  have hc {a b : ℕ} (eq : a = b) (ψ : Semisentence language a) (v : Fin b → M) :
      (cast (congrArg (Semisentence language) eq) ψ).Eval v Empty.elim ↔
        ψ.Eval (fun i => v (Fin.cast eq i)) Empty.elim := by
    cases eq
    rfl
  rw [hc (Nat.add_comm 3 φ.fvSup), packParameters_eval φ _ (fun i => env (i + φ.fvSup))]
  have hv : (fun i => (z :> y :> x :> e) (Fin.cast (Nat.add_comm 3 φ.fvSup) (i.castAdd φ.fvSup))) = ![z,y,x] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun l => Fin.elim0 l) k
        rfl
  have he : (fun i => if hi : i < φ.fvSup then
      (z :> y :> x :> e) (Fin.cast (Nat.add_comm 3 φ.fvSup) (Fin.natAdd 3 ⟨i,hi⟩))
      else env ((i - φ.fvSup) + φ.fvSup)) = env := by
    funext i
    split
    · rename_i hi
      have hk : Fin.cast (Nat.add_comm 3 φ.fvSup) (Fin.natAdd 3 ⟨i,hi⟩) =
          (⟨i,hi⟩ : Fin φ.fvSup).succ.succ.succ := by
        apply Fin.ext
        simp
        omega
      rw [hk]
      simp [env, hi]
    · congr 1; omega
  rw [hv, he]
  exact hxyz
end models

theorem candidate_proves_packedTriple (φ : Semiproposition language 3)
    (h : PRA ⊢ (∃⁰ ∃⁰ ∃⁰ φ).univCl) : PRA ⊢ (∀⁰* ∃⁰ ∃⁰ ∃⁰ packedTriple φ) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelPackedTriple φ (models_of_provable (inferInstance : M↓[language] ⊧* PRA) h)
/-- A coded induction counterexample has a finite term-triple defeat disjunction. -/
theorem counterexample_finiteDefeat {n : ℕ} (pred : PRAFiniteFunctionCodes.Code (n+2))
    (base stop : PRAFiniteFunctionCodes.Code n) (q : PRAFiniteFunctionCodes.Code (n+3)) :
    let φ := PRAInductionCounterexample.counterexampleMatrix pred base stop q
    ∃ p : Theory.Proof PRAUniversalCandidate.UniversalAxiom
        (∀⁰* ∃⁰ ∃⁰ ∃⁰ packedTriple φ),
      PRA ⊢ (HerbrandTripleExtraction.tripleDisjunction (parameterTripleMatrix (packedTriple φ))
        (HerbrandExistentialSequents.existentialTerms
          (prepareAllTriple (packedTriple φ) (packedTriple_open φ
            (PRAInductionCounterexample.counterexampleMatrix_open pred base stop q)) p).derivation)).univCl := by
  exact candidate_proves_parameterTripleDisjunction _
    (packedTriple_open _ (PRAInductionCounterexample.counterexampleMatrix_open pred base stop q))
    (candidate_proves_packedTriple _
      (PRAInductionCounterexample.PRA_proves_counterexampleSentence pred base stop q))
end DiophantineConsistency.HerbrandPackedTriple
