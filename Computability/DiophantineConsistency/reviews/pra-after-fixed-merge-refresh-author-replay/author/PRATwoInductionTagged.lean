import DiophantineConsistency.PRAOneInductionCandidateTransfer
import DiophantineConsistency.PRAStageInductionSchema
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DiophantineConsistency.PRATwoInductionTagged
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAStageCodedInduction PRAOneInductionCandidateTransfer PRAAddOne

def substitutionEquation (combined original : Code 3) (encode : Code 1) : Sentence language :=
  ∀⁰* (Semiformula.rel Language.ORing.Rel.eq
    ![.func combined ![#0,#1,.func encode ![#2]], .func original ![#0,#1,#2]] : Semisentence language 3)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelSubstitutionEquation (combined original : Code 3) (encode : Code 1)
    (h : PRA ⊢ substitutionEquation combined original encode) (x y c : M) :
    Structure.func (L := language) combined
      ![x,y,Structure.func (L := language) encode ![c]] =
    Structure.func (L := language) original ![x,y,c] := by
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) h
  simp only [models_iff, substitutionEquation, Semiformula.eval_allClosure] at hm
  have hv := hm ![x,y,c]
  simp only [Semiformula.eval_rel, eqRel] at hv
  simpa using hv

theorem modelInductionOfSubstitution (combined original : Code 3) (encode : Code 1)
    (h : PRA ⊢ substitutionEquation combined original encode)
    (hcombined : M↓[language] ⊧ (inductionFormula combined).univCl) :
    M↓[language] ⊧ (inductionFormula original).univCl := by
  simp only [models_iff, Semiformula.eval_univCl] at hcombined ⊢
  intro e
  apply (modelInductionFormula original e).mpr
  intro c z
  dsimp only
  intro hInd
  have hc := (modelInductionFormula combined e).mp (hcombined e)
  have heq (x y : M) :
      Structure.func (L := language) combined (Fin.cases x (Fin.cases y
        (Fin.cases (Structure.func (L := language) encode ![c]) (fun i : Fin 0 => e i.val)))) =
      Structure.func (L := language) original (Fin.cases x (Fin.cases y
        (Fin.cases c (fun i : Fin 0 => e i.val)))) := by
    have h0 := modelSubstitutionEquation combined original encode h x y c
    have hleft : (Fin.cases x (Fin.cases y (Fin.cases (Structure.func (L := language) encode ![c])
        (fun i : Fin 0 => e i.val)))) = ![x,y,Structure.func (L := language) encode ![c]] := by
      funext i
      refine Fin.cases rfl (fun i => ?_) i
      refine Fin.cases rfl (fun i => ?_) i
      exact Fin.cases rfl (fun i => Fin.elim0 i) i
    have hright : (Fin.cases x (Fin.cases y (Fin.cases c (fun i : Fin 0 => e i.val)))) = ![x,y,c] := by
      funext i
      refine Fin.cases rfl (fun i => ?_) i
      refine Fin.cases rfl (fun i => ?_) i
      exact Fin.cases rfl (fun i => Fin.elim0 i) i
    rw [hleft,hright]
    exact h0
  have hbase : ∃ y, Structure.func (L := language) combined
      (Fin.cases (Structure.func (L := language) (Code.zero 0) Fin.elim0)
        (Fin.cases y (Fin.cases (Structure.func (L := language) encode ![c]) (fun i : Fin 0 => e i.val)))) =
      Structure.func (L := language) oneCode Fin.elim0 := by
    obtain ⟨y,hy⟩ := hInd.1
    exact ⟨y, (heq _ _).trans hy⟩
  have hstep : ∀ x, (∃ y, Structure.func (L := language) combined (Fin.cases x (Fin.cases y
        (Fin.cases (Structure.func (L := language) encode ![c]) (fun i : Fin 0 => e i.val)))) =
        Structure.func (L := language) oneCode Fin.elim0) →
      ∃ q, Structure.func (L := language) combined
        (Fin.cases (Structure.func (L := language) Code.succ (fun _ => x)) (Fin.cases q
          (Fin.cases (Structure.func (L := language) encode ![c]) (fun i : Fin 0 => e i.val)))) =
        Structure.func (L := language) oneCode Fin.elim0 := by
    intro x ⟨y,hy⟩
    have hy' := (heq x y).symm.trans hy
    obtain ⟨q,hq⟩ := hInd.2 x ⟨y,hy'⟩
    exact ⟨q,(heq _ _).trans hq⟩
  obtain ⟨w,hw⟩ := hc (Structure.func (L := language) encode ![c]) z ⟨hbase,hstep⟩
  exact ⟨w,(heq z w).symm.trans hw⟩
end models
/-- A single combined induction axiom supplies both original induction axioms,
provided their tagged substitution identities have actual candidate-PRA proofs. -/
theorem candidate_proves_with_combined (combined first second : Code 3) (encode0 encode1 : Code 1)
    (h0 : PRA ⊢ substitutionEquation combined first encode0)
    (h1 : PRA ⊢ substitutionEquation combined second encode1)
    (τ : Sentence language)
    (p : ((PRA ∪ {(inductionFormula first).univCl}) ∪ {(inductionFormula second).univCl}) ⊢ τ) :
    (PRA ∪ {(inductionFormula combined).univCl}) ⊢ τ := by
  letI : 𝗘𝗤 language ⪯ (PRA ∪ {(inductionFormula combined).univCl}) :=
    Entailment.WeakerThan.ofSubset (fun _ h => Or.inl (Or.inl (Or.inl (Or.inl h))))
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M hM0 hM hEq hBoth
  letI : M↓[language] ⊧* PRA := by
    constructor
    intro φ hφ
    exact hBoth.models _ (Or.inl hφ)
  have hc : M↓[language] ⊧ (inductionFormula combined).univCl := hBoth.models _ (Or.inr rfl)
  have hf : M↓[language] ⊧ (inductionFormula first).univCl := modelInductionOfSubstitution combined first encode0 h0 hc
  have hs : M↓[language] ⊧ (inductionFormula second).univCl := modelInductionOfSubstitution combined second encode1 h1 hc
  have hPlus : M↓[language] ⊧* ((PRA ∪ {(inductionFormula first).univCl}) ∪ {(inductionFormula second).univCl}) := by
    constructor
    intro φ hφ
    rcases hφ with (h | h) | h
    · exact (inferInstance : M↓[language] ⊧* PRA).models _ h
    · have he : φ = (inductionFormula first).univCl := h
      exact he.symm ▸ hf
    · have he : φ = (inductionFormula second).univCl := h
      exact he.symm ▸ hs
  exact models_of_provable hPlus p

/-- Two closed coded induction instances can be eliminated once a combined
code and its two actual candidate-PRA substitution proofs are supplied. -/
theorem PRA_proves_goal_of_two_tagged (combined first second : Code 3) (encode0 encode1 : Code 1)
    (h0 : PRA ⊢ substitutionEquation combined first encode0)
    (h1 : PRA ⊢ substitutionEquation combined second encode1)
    (θ : Semiproposition language 1) (hθ : θ.Open)
    (p : ((PRA ∪ {(inductionFormula first).univCl}) ∪ {(inductionFormula second).univCl}) ⊢ (∃⁰ θ).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := by
  apply PRA_proves_goal_of_candidate_plus_one combined θ hθ
  exact candidate_proves_with_combined combined first second encode0 encode1 h0 h1 _ p
end DiophantineConsistency.PRATwoInductionTagged
