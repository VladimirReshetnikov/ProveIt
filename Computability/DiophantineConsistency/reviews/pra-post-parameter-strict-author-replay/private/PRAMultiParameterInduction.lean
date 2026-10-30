import DiophantineConsistency.PRAParameterPackingIteration
import DiophantineConsistency.PRATwoParameterInductionTransfer
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DiophantineConsistency.PRAMultiParameterInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAOpenOneInduction PRABoundedOneInduction
open PRAParameterPackingN PRAParameterPackingIteration PRATwoParameterInductionTransfer

def multiSub (n : ℕ) : Fin (3+n) → Semiterm language ℕ 2 :=
  Fin.append ![#1,#0,&0] (fun i => .fvar (i.val+1))

def multiSigma (n : ℕ) (ψ : Semisentence language (3+n)) : Semiproposition language 1 :=
  ∃⁰ (Rew.embSubsts (multiSub n) ▹ ψ)

theorem modelMultiSigma {M : Type} [Structure language M] (n : ℕ)
    (ψ : Semisentence language (3+n)) (e : ℕ → M) (x : M) :
    (multiSigma n ψ).Eval ![x] e ↔ ∃ y : M,
      ψ.Eval (parameterVal n x y (fun i => e i.val)) Empty.elim := by
  simp only [multiSigma, Semiformula.eval_ex, Semiformula.eval_rew]
  apply exists_congr
  intro y
  have hb : (Semiterm.val (L := language) ![y,x] e ∘
      Rew.embSubsts (multiSub n) ∘ Semiterm.bvar) =
      parameterVal n x y (fun i => e i.val) := by
    funext i
    induction i using Fin.addCases with
    | left i =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [multiSub, parameterVal, Fin.append_left]
      · refine Fin.cases ?_ (fun k => ?_) j
        · simp [multiSub, parameterVal, Fin.append_left]
        · refine Fin.cases ?_ (fun l => Fin.elim0 l) k
          simp [multiSub, parameterVal, Fin.append_left]
    | right i => simp [multiSub, parameterVal, Fin.append_right]
  have hf : (Semiterm.val (L := language) ![y,x] e ∘
      Rew.embSubsts (multiSub n) ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hb,hf]
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelMultiInduction (n : ℕ) (ψ : Semisentence language (3+n))
    (h : M↓[language] ⊧ (succInd (openSigma (packAll n ψ))).univCl) :
    M↓[language] ⊧ (succInd (multiSigma n ψ)).univCl := by
  simp only [models_iff, Semiformula.eval_univCl] at h ⊢
  intro e
  obtain ⟨t,ht⟩ := modelPackAll n ψ (fun i => e i.val)
  let e' : ℕ → M := Function.update e 0 t
  have hc (x : M) : (openSigma (packAll n ψ)).Eval ![x] e' ↔
      (multiSigma n ψ).Eval ![x] e := by
    rw [modelOpenSigma, modelMultiSigma]
    simp only [e',Function.update_self]
    exact exists_congr (ht x)
  have hi := (modelSuccInd _ e').mp (h e')
  apply (modelSuccInd _ e).mpr
  intro hb hs x
  apply (hc x).mp
  apply hi ((hc _).mpr hb)
  intro z hz
  exact (hc _).mpr (hs z ((hc z).mp hz))
end models

/-- Eliminate one Σ₁-induction instance whose bounded matrix has any fixed
finite number of free predicate parameters, from an actual candidate-PRA proof
of a universally closed open-existential goal. -/
theorem PRA_proves_goal_of_finite_parameter_induction
    (n : ℕ) (ψ : Semisentence language (3+n)) (hψ : Hierarchy 𝚺 0 ψ)
    (θ : Semiproposition language 1) (hθ : θ.Open)
    (p : (PRA ∪ {(succInd (multiSigma n ψ)).univCl}) ⊢ (∃⁰ θ).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := by
  have hp : (PRA ∪ {(succInd (openSigma (packAll n ψ))).univCl}) ⊢ (∃⁰ θ).univCl := by
    letI : 𝗘𝗤 language ⪯ (PRA ∪ {(succInd (openSigma (packAll n ψ))).univCl}) :=
      Entailment.WeakerThan.ofSubset (fun _ h => Or.inl (Or.inl (Or.inl (Or.inl h))))
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ hBoth
    letI : M↓[language] ⊧* PRA := by
      constructor
      intro σ hσ
      exact hBoth.models _ (Or.inl hσ)
    have hpacked : M↓[language] ⊧ (succInd (openSigma (packAll n ψ))).univCl :=
      hBoth.models _ (Or.inr rfl)
    have horig := modelMultiInduction n ψ hpacked
    have hPlus : M↓[language] ⊧* (PRA ∪ {(succInd (multiSigma n ψ)).univCl}) := by
      constructor
      intro σ hσ
      rcases hσ with hσ | hσ
      · exact (inferInstance : M↓[language] ⊧* PRA).models _ hσ
      · simp only [Set.mem_singleton_iff] at hσ
        subst σ
        exact horig
    exact models_of_provable hPlus p
  exact PRA_proves_goal_of_boundedSuccInd (packAll n ψ) (packAll_bounded n ψ hψ) θ hθ hp
end DiophantineConsistency.PRAMultiParameterInduction
