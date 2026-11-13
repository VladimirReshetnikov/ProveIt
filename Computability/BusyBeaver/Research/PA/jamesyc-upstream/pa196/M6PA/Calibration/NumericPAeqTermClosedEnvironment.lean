module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermSupportedValidity
@[expose] public section
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] valueSyntaxGraph parametersGraph freeSupportedGraph
noncomputable def closedEnvironmentGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “t b f g z. ∃ p q out, !parametersGraph p b f z ∧ !parametersGraph q b g z ∧
    !valueSyntaxGraph out p t ∧ !valueSyntaxGraph out q t”
theorem closedEnvironment_graph (t b f g z:V):closedEnvironmentGraph.val.Evalb ![t,b,f,g,z] ↔
    valueSyntax (parameters b f z) t=valueSyntax (parameters b g z) t := by
  simp [closedEnvironmentGraph,parameters_graph,valueSyntax_graph,Matrix.comp_vecCons'',eq_comm]
attribute [local irreducible] closedEnvironmentGraph
noncomputable def closedEnvironmentInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ t<k, !freeSupportedGraph 0 t → ∀ b f g z, !closedEnvironmentGraph t b f g z”
theorem closedEnvironment_invariant (k:V):closedEnvironmentInvariant.Evalb ![k] ↔
    ∀t<k, FreeSupported 0 t → ∀b f g z, valueSyntax (parameters b f z) t=valueSyntax (parameters b g z) t := by
  simp [closedEnvironmentInvariant,freeSupported_graph,closedEnvironment_graph,Matrix.comp_vecCons'']
private theorem closedEnvironment_step (t:V)
    (ih:∀u<t,FreeSupported 0 u→∀b f g z,valueSyntax (parameters b f z) u=valueSyntax (parameters b g z) u)
    (h:FreeSupported 0 t) :∀b f g z,valueSyntax (parameters b f z) t=valueSyntax (parameters b g z) t := by
  intro b f g z
  rcases IsUTerm.case_iff.mp h.1 with ⟨i,rfl⟩|⟨i,rfl⟩|⟨k,c,ts,hc,hv,rfl⟩
  · simp
  · have hi := h.2
    simp only [freeBound_fvar] at hi
    have : ¬i+1≤(0:V) := by simp
    exact False.elim (this hi)
  · have hs := (freeSupported_func hc hv).mp h
    rcases (Presentation.source_functions k c).mp hc with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,htag⟩
    · have hz :ts=0 :=IsUTermVec.empty_iff.mp hv
      subst ts; simp
    · obtain ⟨u,rfl⟩ :=eq_singleton_iff_len_eq_one.mp hv.lh.symm
      have hu : IsUTerm Presentation.language u := by simpa using hv.nth (show (0:V)<1 by simp)
      have hs' :FreeSupported 0 u :=by simpa using hs 0 (by simp)
      rw [valueSyntax_successor _ _ hu,valueSyntax_successor _ _ hu]
      simpa [childParameters,parameters] using congrArg (successorValue z) (ih u (unary_child_rank u) hs' (shiftTerms b) (shiftTerms f) (shiftTerms g) (qqBvar 0))
    · obtain ⟨u,v,hu,hv2,rfl⟩ :=IsUTermVec.two_iff.mp hv
      have hs0 :FreeSupported 0 u :=by simpa using hs 0 (by simp)
      have hs1 :FreeSupported 0 v :=by simpa using hs 1 (by simp)
      have iu :=ih u (binary_left_rank c u v) hs0
      have iv :=ih v (binary_right_rank c u v) hs1
      rcases htag with rfl|rfl
      · rw [valueSyntax_addition _ _ _ hu hv2,valueSyntax_addition _ _ _ hu hv2]
        simpa [binaryParameters,parameters] using congrArg₂ (additionValue z) (iu (shiftTerms (shiftTerms b)) (shiftTerms (shiftTerms f)) (shiftTerms (shiftTerms g)) (qqBvar 1)) (iv (shiftTerms (shiftTerms b)) (shiftTerms (shiftTerms f)) (shiftTerms (shiftTerms g)) (qqBvar 0))
      · rw [valueSyntax_multiplication _ _ _ hu hv2,valueSyntax_multiplication _ _ _ hu hv2]
        simpa [binaryParameters,parameters] using congrArg₂ (multiplicationValue z) (iu (shiftTerms (shiftTerms b)) (shiftTerms (shiftTerms f)) (shiftTerms (shiftTerms g)) (qqBvar 1)) (iv (shiftTerms (shiftTerms b)) (shiftTerms (shiftTerms f)) (shiftTerms (shiftTerms g)) (qqBvar 0))
attribute [local irreducible] closedEnvironmentInvariant
theorem valueSyntax_closed_environment {t:V} (h:FreeSupported 0 t) (b f g z:V):
    valueSyntax (parameters b f z) t=valueSyntax (parameters b g z) t := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall :∀k:V,∀t<k,FreeSupported 0 t→∀b f g z,valueSyntax (parameters b f z) t=valueSyntax (parameters b g z) t := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun k:V=>∀t<k,FreeSupported 0 t→∀b f g z,valueSyntax (parameters b f z) t=valueSyntax (parameters b g z) t) ?_ ?_ ?_
    · refine ⟨fun _=>0,Rewriting.emb closedEnvironmentInvariant,by trivial,?_⟩
      intro k;simpa using (closedEnvironment_invariant (V:=V) k).symm
    · intro t ht;exact False.elim (by simpa using ht)
    · intro k ih t ht hs
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp ht) with he|hlt
      · subst t;exact closedEnvironment_step k ih hs
      · exact ih t hlt hs
  exact hall (t+1) t (lt_add_one t) h b f g z
#print axioms closedEnvironment_graph
#print axioms closedEnvironment_invariant
#print axioms valueSyntax_closed_environment
end M6.PA.NumericPAeqTerm

