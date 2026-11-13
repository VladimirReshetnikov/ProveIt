module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentDerivationStep
@[expose] public section

/-! Genuine full-PA course-of-values induction on the original numeric
relational derivation code. The explicit axiom certificate supplier remains
an assumption. This is not the original arithmetic PrfPA reduction. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
variable {T : Theory language} [T.Δ₁]

theorem derivation_certificate_of_axiom_supplier
    (ha : AxiomCertificateSupplier (V:=V) T) (d f lo z : V)
    (hd : Derivation T d) (hb : ProofEnvironment d f lo z) :
    ∃ code, verifyValue code=sequentCode (parameters 0 f lo z) (fstIdx d)+1 := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ n : V, ∀ d<n, Derivation T d → ∀ f lo z : V,
      ProofEnvironment d f lo z → ∃ code,
        verifyValue code=sequentCode (parameters 0 f lo z) (fstIdx d)+1 := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun n : V =>
      ∀ d<n, Derivation T d → ∀ f lo z : V, ProofEnvironment d f lo z →
        ∃ code, verifyValue code=sequentCode (parameters 0 f lo z) (fstIdx d)+1) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb (derivationTranslationInvariant T),by trivial,?_⟩
      intro n
      simpa using (derivationTranslation_invariant T n).symm
    · intro d hd
      exact False.elim (by simpa using hd)
    · intro n ih d hd
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp hd) with he | hlt
      · subst d
        exact derivation_certificate_step ha n ih
      · exact ih d hlt
  exact hall (d+1) d (lt_add_one d) hd f lo z hb

attribute [local irreducible] derivationCertificateGraph proofEnvironmentGraph axiomCertificateSupplier
noncomputable def conditionalDerivationSentence (T : Theory language) [T.Δ₁] : ArithmeticSentence :=
  “!(axiomCertificateSupplier T) → ∀ d f lo z, !(derivation T).sigma d →
    !proofEnvironmentGraph d f lo z → ∃ code, !derivationCertificateGraph code d f lo z”

theorem pa_proves_conditional_derivation (T : Theory language) [T.Δ₁] :
    theory ⊢ conditionalDerivationSentence T := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [conditionalDerivationSentence,models_iff,axiomCertificateSupplier_semantics,
    proofEnvironment_graph,derivationCertificate_graph,Matrix.comp_vecCons'']
  intro ha d f lo z hd hb
  exact derivation_certificate_of_axiom_supplier ha d f lo z hd hb

#print axioms derivation_certificate_of_axiom_supplier
#print axioms pa_proves_conditional_derivation
end M6.PA.RelationalSource.Numeric

