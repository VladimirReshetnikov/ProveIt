import DiophantineConsistency.PRAFiniteMultiParameterInduction
import DiophantineConsistency.PRAISigmaOneFiniteTranslation
/-! Conditional bridge from arbitrary finite mapped Σ₁ axioms to strict
bounded-matrix instances. The normalization certificate is not constructed here. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DiophantineConsistency.PRAConditionalSigmaNormalization
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAParameterPackingN PRAMultiParameterInduction
  PRAFiniteMultiParameterInduction PRAISigmaOneFiniteTranslation

def strictAxiom (d : Descriptor) : Sentence language :=
  (succInd (multiSigma d.arity d.matrix)).univCl

def Certificate (φ : ArithmeticSemiformula ℕ 1) : Prop :=
  ∃ d : Descriptor, Hierarchy 𝚺 0 d.matrix ∧
    (PRA ∪ {strictAxiom d}) ⊢ mappedInduction φ

/-- The missing hypothesis is a genuine proof-producing normalization of
all listed mapped Σ₁ induction instances; this theorem does not supply it. -/
theorem PRA_proves_goal_of_certificates
    (Φ : List (ArithmeticSemiformula ℕ 1))
    (hcert : ∀ φ ∈ Φ, Certificate φ)
    (θ : Semiproposition language 1) (hθ : θ.Open)
    (p : (PRA ∪ mappedInductions Φ) ⊢ (∃⁰ θ).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := by
  classical
  let choose : {φ // φ ∈ Φ} → Descriptor := fun x => Classical.choose (hcert x.val x.property)
  let fs : List Descriptor := Φ.attach.map choose
  have hfs : ∀ d ∈ fs, Hierarchy 𝚺 0 d.matrix := by
    intro d hd
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hd
    exact (Classical.choose_spec (hcert x.val x.property)).1
  have hp : (PRA ∪ PRAFiniteMultiParameterInduction.inductionAxioms fs) ⊢ (∃⁰ θ).univCl := by
    letI : 𝗘𝗤 language ⪯ (PRA ∪ PRAFiniteMultiParameterInduction.inductionAxioms fs) :=
      Entailment.WeakerThan.ofSubset (fun _ h => Or.inl (Or.inl (Or.inl (Or.inl h))))
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ hBoth
    letI : M↓[language] ⊧* PRA := by
      constructor
      intro σ hσ
      exact hBoth.models _ (Or.inl hσ)
    have hPlus : M↓[language] ⊧* (PRA ∪ mappedInductions Φ) := by
      constructor
      intro σ hσ
      rcases hσ with hσ | hσ
      · exact (inferInstance : M↓[language] ⊧* PRA).models _ hσ
      · obtain ⟨φ,hφ,rfl⟩ := hσ
        let x : {φ // φ ∈ Φ} := ⟨φ,hφ⟩
        let d := choose x
        have hd : d ∈ fs := by
          apply List.mem_map.mpr
          refine ⟨x,?_,rfl⟩
          simp
        have hproof : (PRA ∪ {strictAxiom d}) ⊢ mappedInduction φ :=
          (Classical.choose_spec (hcert x.val x.property)).2
        have hstrict : M↓[language] ⊧ strictAxiom d :=
          hBoth.models _ (Or.inr ⟨d,hd,rfl⟩)
        have hSub : M↓[language] ⊧* (PRA ∪ {strictAxiom d}) := by
          constructor
          intro τ hτ
          rcases hτ with hτ | hτ
          · exact (inferInstance : M↓[language] ⊧* PRA).models _ hτ
          · simp only [Set.mem_singleton_iff] at hτ
            subst τ
            exact hstrict
        exact models_of_provable hSub hproof
    exact models_of_provable hPlus p
  exact PRA_proves_goal_of_finite_induction fs hfs θ hθ hp
/-- A finite IΣ₁ proof yields the candidate-PRA goal provided a certificate
exists for every Σ₁ induction formula. The normalization hypothesis remains
explicit and is not obtained from conservation. -/
theorem PRA_proves_goal_of_isigmaOne_certificates
    (σ : ArithmeticSentence) (p : Theory.Proof 𝗜𝚺₁ σ)
    (θ : Semiproposition language 1) (hθ : θ.Open)
    (hgoal : Semiformula.lMap embedding σ = (∃⁰ θ).univCl)
    (hnormalize : ∀ φ : ArithmeticSemiformula ℕ 1, Hierarchy 𝚺 1 φ → Certificate φ) :
    PRA ⊢ (∃⁰ θ).univCl := by
  obtain ⟨Φ,hΦ,hproof⟩ := finite_translation p
  rw [hgoal] at hproof
  exact PRA_proves_goal_of_certificates Φ (fun φ hφ => hnormalize φ (hΦ φ hφ)) θ hθ hproof
end DiophantineConsistency.PRAConditionalSigmaNormalization
