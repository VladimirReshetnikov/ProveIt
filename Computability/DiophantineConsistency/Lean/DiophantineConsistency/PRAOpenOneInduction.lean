import DiophantineConsistency.PRAFoundationOneInduction
import DiophantineConsistency.PRABoundedWitness
/-! One induction instance with an arbitrary open matrix on x,y,c. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DiophantineConsistency.PRAOpenOneInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAEqualityCode PRAOpenFormulaCoverage
  PRABoundedCharacteristic PRABoundedWitness PRAStageInductionSchema PRAFoundationOneInduction
  PRAAddOne PRATermCompilation

/-- For ψ with inputs `[x,y,c]`, use c as the only free predicate parameter. -/
def openSigma (ψ : Semisentence language 3) : Semiproposition language 1 :=
  ∃⁰ (Rew.embSubsts ![#1,#0,&0] ▹ ψ)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem modelOpenSigma (ψ : Semisentence language 3) (e : ℕ → M) (x : M) :
    (openSigma ψ).Eval ![x] e ↔ ∃ y : M, ψ.Eval ![x,y,e 0] Empty.elim := by
  simp only [openSigma, Semiformula.eval_ex, Semiformula.eval_rew]
  apply exists_congr
  intro y
  have hb : (Semiterm.val (L := language) ![y,x] e ∘
      Rew.embSubsts ![#1,#0,&0] ∘ Semiterm.bvar) = ![x,y,e 0] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun l => Fin.elim0 l) k
  have hf : (Semiterm.val (L := language) ![y,x] e ∘
      Rew.embSubsts ![#1,#0,&0] ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hb,hf]

omit [M↓[language] ⊧* PRA] in
theorem modelSigmaCharacteristic (ψ : Semisentence language 3) (c : Code 3)
    (hc : M↓[language] ⊧ characteristicSentence c ψ) (e : ℕ → M) (x : M) :
    (openSigma ψ).Eval ![x] e ↔ (codedSigma c).Eval ![x] e := by
  rw [modelOpenSigma, modelCodedSigma]
  apply exists_congr
  intro y
  have hh : M↓[language] ⊧ oneCorrectSentence c ψ := hc
  have hm := modelCharacteristicMatrix c ψ hh ![x,y,e 0]
  have he : (characteristicMatrix c).Eval ![x,y,e 0] Empty.elim ↔
      Structure.func (L := language) c ![x,y,e 0] = Structure.func (L := language) oneCode Fin.elim0 := by
    simp [characteristicMatrix, Semiformula.eval_rel, eqRel, applyCode, vars, Function.comp_def]
    have hz : (fun i : Fin 0 => Semiterm.val ![x,y,e 0] Empty.elim (Fin.elim0 i : TermN 3)) =
        (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
    rw [hz]
  have hv : Fin.cases x (Fin.cases y (Fin.cases (e 0) (fun i : Fin 0 => e i.val))) = ![x,y,e 0] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun l => Fin.elim0 l) k
  rw [hv]
  exact hm.symm.trans he

omit [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem modelSuccInd_congr (φ ψ : Semiproposition language 1)
    (h : ∀ (e : ℕ → M) (x : M), φ.Eval ![x] e ↔ ψ.Eval ![x] e) :
    M↓[language] ⊧ (succInd φ).univCl ↔ M↓[language] ⊧ (succInd ψ).univCl := by
  simp only [models_iff, Semiformula.eval_univCl]
  apply forall_congr'
  intro e
  simp [succInd, Semiformula.eval_substs, h e]
end models
/-- Eliminate an induction instance when its matrix has a certified
characteristic code. -/
theorem PRA_proves_goal_of_characteristicSuccInd (ψ : Semisentence language 3) (c : Code 3)
    (hc : PRA ⊢ characteristicSentence c ψ) (θ : Semiproposition language 1) (hθ : θ.Open)
    (p : (PRA ∪ {(succInd (openSigma ψ)).univCl}) ⊢ (∃⁰ θ).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := by
  have hp : (PRA ∪ {(succInd (codedSigma c)).univCl}) ⊢ (∃⁰ θ).univCl := by
    letI : 𝗘𝗤 language ⪯ (PRA ∪ {(succInd (codedSigma c)).univCl}) :=
      Entailment.WeakerThan.ofSubset (fun _ h => Or.inl (Or.inl (Or.inl (Or.inl h))))
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ hBoth
    letI : M↓[language] ⊧* PRA := by
      constructor
      intro σ hσ
      exact hBoth.models _ (Or.inl hσ)
    have hchar := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hc
    have hcode : M↓[language] ⊧ (succInd (codedSigma c)).univCl := hBoth.models _ (Or.inr rfl)
    have hψ : M↓[language] ⊧ (succInd (openSigma ψ)).univCl := by
      apply (modelSuccInd_congr (openSigma ψ) (codedSigma c)
        (fun e x => modelSigmaCharacteristic ψ c hchar e x)).mpr
      exact hcode
    have hPlus : M↓[language] ⊧* (PRA ∪ {(succInd (openSigma ψ)).univCl}) := by
      constructor
      intro σ hσ
      rcases hσ with hσ | hσ
      · exact (inferInstance : M↓[language] ⊧* PRA).models _ hσ
      · simp only [Set.mem_singleton_iff] at hσ
        subst σ
        exact hψ
    exact models_of_provable hPlus p
  exact PRA_proves_goal_of_succInd c θ hθ hp

/-- Eliminate one actual successor-induction instance whose Σ₁ predicate has
an arbitrary open matrix ψ(x,y,c), with no external predicate parameters. -/
theorem PRA_proves_goal_of_openSuccInd (ψ : Semisentence language 3) (hψ : ψ.Open)
    (θ : Semiproposition language 1) (hθ : θ.Open)
    (p : (PRA ∪ {(succInd (openSigma ψ)).univCl}) ⊢ (∃⁰ θ).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := by
  obtain ⟨c,_,hc⟩ := PRA_proves_openCharacteristic ψ hψ
  exact PRA_proves_goal_of_characteristicSuccInd ψ c hc θ hθ p

end DiophantineConsistency.PRAOpenOneInduction
