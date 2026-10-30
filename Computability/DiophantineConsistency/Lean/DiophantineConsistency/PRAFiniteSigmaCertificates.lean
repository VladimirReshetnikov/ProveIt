import DiophantineConsistency.PRAStrictTheoryComparison
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DiophantineConsistency.PRAFiniteSigmaCertificates
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAParameterPackingN PRAMultiParameterInduction
  PRAFiniteMultiParameterInduction PRAISigmaOneFiniteTranslation
  PRAConditionalSigmaNormalization PRAStrictSigmaFiniteClient PRAStrictTheoryComparison

def FiniteCertificate (φ : ArithmeticSemiformula ℕ 1) : Prop :=
  ∃ fs : List Descriptor, (∀ d ∈ fs, Hierarchy 𝚺 0 d.matrix) ∧
    (PRA ∪ PRAFiniteMultiParameterInduction.inductionAxioms fs) ⊢ mappedInduction φ

/-- Join the finite strict supports of the individual certificates. -/
theorem combine_support
    (Φ : List (ArithmeticSemiformula ℕ 1)) (hc : ∀ φ ∈ Φ, FiniteCertificate φ)
    (σ : Sentence language) (p : (PRA ∪ mappedInductions Φ) ⊢ σ) :
    ∃ fs : List Descriptor, (∀ d ∈ fs, Hierarchy 𝚺 0 d.matrix) ∧
      (PRA ∪ PRAFiniteMultiParameterInduction.inductionAxioms fs) ⊢ σ := by
  classical
  let choose : {φ // φ ∈ Φ} → List Descriptor := fun x => Classical.choose (hc x.val x.property)
  let fs : List Descriptor := Φ.attach.flatMap choose
  have hfs : ∀ d ∈ fs, Hierarchy 𝚺 0 d.matrix := by
    intro d hd
    obtain ⟨x,hx,hd⟩ := List.mem_flatMap.mp hd
    exact (Classical.choose_spec (hc x.val x.property)).1 d hd
  refine ⟨fs,hfs,?_⟩
  apply PRAOpenOneInduction.PRA_proof_of_model_theory_replacement _ _ _ ?_ p
  intro M _ _ _ _ hInductions
  constructor
  intro τ hτ
  obtain ⟨φ,hφ,rfl⟩ := hτ
  let x : {φ // φ ∈ Φ} := ⟨φ,hφ⟩
  have hproof : (PRA ∪ PRAFiniteMultiParameterInduction.inductionAxioms (choose x)) ⊢
      mappedInduction φ := (Classical.choose_spec (hc x.val x.property)).2
  have hSub : M↓[language] ⊧* (PRA ∪ PRAFiniteMultiParameterInduction.inductionAxioms (choose x)) := by
    constructor
    intro ρ hρ
    rcases hρ with hρ | ⟨d,hd,rfl⟩
    · exact (inferInstance : M↓[language] ⊧* PRA).models _ hρ
    · have hdf : d ∈ fs := by
        apply List.mem_flatMap.mpr
        exact ⟨x,by simp,hd⟩
      exact hInductions.models _ ⟨d,hdf,rfl⟩
  exact models_of_provable hSub hproof

theorem PRA_proves_goal_of_finite_certificates
    (Φ : List (ArithmeticSemiformula ℕ 1)) (hc : ∀ φ ∈ Φ, FiniteCertificate φ)
    (θ : Semiproposition language 1) (hθ : θ.Open)
    (p : (PRA ∪ mappedInductions Φ) ⊢ (∃⁰ θ).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := by
  obtain ⟨fs,hfs,hproof⟩ := combine_support Φ hc _ p
  exact PRA_proves_goal_of_finite_induction fs hfs θ hθ hproof
theorem single_to_finite (φ : ArithmeticSemiformula ℕ 1) (h : Certificate φ) : FiniteCertificate φ := by
  obtain ⟨d,hd,hproof⟩ := h
  refine ⟨[d], ?_, ?_⟩
  · intro e he
    simp only [List.mem_singleton] at he
    subst e
    exact hd
  · apply Entailment.weakening (Entailment.WeakerThan.ofSubset ?_) hproof
    intro σ hσ
    rcases hσ with hσ | hσ
    · exact Or.inl hσ
    · simp only [Set.mem_singleton_iff] at hσ
      subst σ
      exact Or.inr ⟨d,by simp,rfl⟩

/-- Any proof in the strict source theory yields a translated proof using a
finite list of strict bounded induction axioms. -/
theorem finite_support_of_strictProof (σ : ArithmeticSentence) (p : Theory.Proof strictTheory σ) :
    ∃ fs : List Descriptor, (∀ d ∈ fs, Hierarchy 𝚺 0 d.matrix) ∧
      (PRA ∪ PRAFiniteMultiParameterInduction.inductionAxioms fs) ⊢ Semiformula.lMap embedding σ := by
  obtain ⟨Φ,hΦ,hproof⟩ := PRAStrictTheoryComparison.finite_translation p
  exact combine_support Φ (fun φ hφ => single_to_finite φ (case_certificate φ (hΦ φ hφ))) _ hproof

/-- A strict-theory proof of an induction axiom yields its mapped finite-support
certificate; the support contains only bounded strict induction instances. -/
theorem finiteCertificate_of_strictProof (φ : ArithmeticSemiformula ℕ 1)
    (p : Theory.Proof strictTheory (succInd φ).univCl) : FiniteCertificate φ := by
  obtain ⟨fs,hfs,hproof⟩ := finite_support_of_strictProof _ p
  refine ⟨fs,hfs,?_⟩
  letI : 𝗘𝗤 language ⪯ (PRA ∪ PRAFiniteMultiParameterInduction.inductionAxioms fs) :=
    Entailment.WeakerThan.ofSubset (fun _ h => Or.inl (Or.inl (Or.inl (Or.inl h))))
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  have hm := models_of_provable hM hproof
  have horig := Semiformula.models_lMap.mp hm
  simp only [models_iff, Semiformula.eval_univCl] at horig
  unfold mappedInduction
  simp only [models_iff, Semiformula.eval_univCl]
  intro e
  exact Semiformula.eval_lMap.mpr (horig e)
/-- The remaining hypothesis is an actual strict-source proof of each Σ₁
induction axiom, not the original IΣ₁ axiom as an assumed dependency. -/
theorem PRA_proves_goal_of_strict_induction_normalization
    (σ : ArithmeticSentence) (p : Theory.Proof 𝗜𝚺₁ σ)
    (θ : Semiproposition language 1) (hθ : θ.Open)
    (hgoal : Semiformula.lMap embedding σ = (∃⁰ θ).univCl)
    (hnorm : ∀ φ : ArithmeticSemiformula ℕ 1, Hierarchy 𝚺 1 φ →
      Nonempty (Theory.Proof strictTheory (succInd φ).univCl)) :
    PRA ⊢ (∃⁰ θ).univCl := by
  obtain ⟨Φ,hΦ,hproof⟩ := PRAISigmaOneFiniteTranslation.finite_translation p
  rw [hgoal] at hproof
  apply PRA_proves_goal_of_finite_certificates Φ _ θ hθ hproof
  intro φ hφ
  obtain ⟨hp⟩ := hnorm φ (hΦ φ hφ)
  exact finiteCertificate_of_strictProof φ hp
end DiophantineConsistency.PRAFiniteSigmaCertificates
