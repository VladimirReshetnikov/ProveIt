module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentAllocatorInvariant
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Full-PA accepted allocator relocation at a fixed reserve. Both source
coverage guards are retained throughout the model-length induction. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated
open ActualCertificateEquivalence PA196.Arithmetic.Checker

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

private theorem neg_value (a : V) : ActualArithmeticGraph.eval translationNeg a 0 0 0=wn a := by
  simp [translationNeg,PA196.Arithmetic.HeadGraphs.neg,wn,wim,implicationValue,
    PA196.Arithmetic.HeadGraphs.implicationExpr,PA196.Arithmetic.HeadGraphs.im,ActualArithmeticGraph.eval]
private theorem exs_value (v a : V) :
    ActualArithmeticGraph.eval translationExs v a 0 0=wn (wal v (wn a)) := by
  simp [translationExs,PA196.Arithmetic.HeadGraphs.ex,PA196.Arithmetic.HeadGraphs.al,PA196.Arithmetic.HeadGraphs.neg,
    wn,wal,wim,implicationValue,universalValue,PA196.Arithmetic.HeadGraphs.universalExpr,
    PA196.Arithmetic.HeadGraphs.implicationExpr,PA196.Arithmetic.HeadGraphs.im,ActualArithmeticGraph.eval]

private def Result (p b f lo other z : V) : Prop :=
  ∃ forward backward, BiCertificates forward backward (translate (parameters b f lo z) p)
    (translate (parameters b f other z) p)

private theorem allocator_source_step (p : V)
    (ih : ∀ q<p, ∀ b f lo other z : V, FormulaCovered b f lo z q → FormulaCovered b f other z q →
      Result q b f lo other z) :
    ∀ b f lo other z : V, FormulaCovered b f lo z p → FormulaCovered b f other z p →
      Result p b f lo other z := by
  intro b f lo other z hl hr
  rcases IsUFormula.case_iff.mp hl.2.1.isUFormula with
    ⟨k,r,ts,hrel,ht,rfl⟩ | ⟨k,r,ts,hrel,ht,rfl⟩ | rfl | rfl |
    ⟨p,q,hp,hq,rfl⟩ | ⟨p,q,hp,hq,rfl⟩ | ⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩
  · unfold Result
    rw [translate_rel _ _ _ _ hrel ht,translate_rel _ _ _ _ hrel ht,
      totalAtom_allocator b f lo other z k r ts]
    exact ⟨_,_,(BiWitness.refl _).accepted⟩
  · unfold Result
    rw [translate_nrel _ _ _ _ hrel ht,translate_nrel _ _ _ _ hrel ht,
      totalAtom_allocator b f lo other z k r ts]
    exact ⟨_,_,(BiWitness.refl _).accepted⟩
  · unfold Result
    rw [translate_verum,translate_verum]
    exact ⟨_,_,(BiWitness.refl _).accepted⟩
  · unfold Result
    rw [translate_falsum,translate_falsum]
    exact ⟨_,_,(BiWitness.refl _).accepted⟩
  · obtain ⟨a,d,ha,hd⟩ := ih p (lt_K!_left p q) b f lo other z (coverage_and hl).1 (coverage_and hr).1
    obtain ⟨e,j,he,hj⟩ := ih q (lt_K!_right p q) b f lo other z (coverage_and hl).2 (coverage_and hr).2
    let h : BiWitness (translate (parameters b f lo z) p) (translate (parameters b f other z) p) := ⟨⟨a,ha⟩,⟨d,hd⟩⟩
    let k : BiWitness (translate (parameters b f lo z) q) (translate (parameters b f other z) q) := ⟨⟨e,he⟩,⟨j,hj⟩⟩
    unfold Result
    rw [translate_and _ _ _ hp hq,translate_and _ _ _ hp hq,translationAnd_eq,translationAnd_eq]
    exact ⟨_,_,(h.imp k.neg).neg.accepted⟩
  · obtain ⟨a,d,ha,hd⟩ := ih p (lt_or_left p q) b f lo other z (coverage_or hl).1 (coverage_or hr).1
    obtain ⟨e,j,he,hj⟩ := ih q (lt_or_right p q) b f lo other z (coverage_or hl).2 (coverage_or hr).2
    let h : BiWitness (translate (parameters b f lo z) p) (translate (parameters b f other z) p) := ⟨⟨a,ha⟩,⟨d,hd⟩⟩
    let k : BiWitness (translate (parameters b f lo z) q) (translate (parameters b f other z) q) := ⟨⟨e,he⟩,⟨j,hj⟩⟩
    unfold Result
    rw [translate_or _ _ _ hp hq,translate_or _ _ _ hp hq,translationOr_eq,translationOr_eq]
    exact ⟨_,_,(h.neg.imp k).accepted⟩
  · let m := commonAllocator lo other
    have hc := common_coverage_all hl hr
    have hf := common_eigen_fresh hl hr (lt_forall p)
    obtain ⟨a,d,ha,hd⟩ := ih p (lt_forall p) (lo∷b) f (lo+1) m z (coverage_all hl) hc.1
    obtain ⟨e,j,he,hj⟩ := ih p (lt_forall p) (other∷b) f (other+1) m z (coverage_all hr) hc.2
    obtain ⟨mid,rev,hmid,hrev⟩ := bound_head_alpha_certificates p lo other b f m z hc.1 hf.1 hf.2
    let h : BiWitness (translate (parameters (lo∷b) f (lo+1) z) p)
      (translate (parameters (lo∷b) f m z) p) := ⟨⟨a,ha⟩,⟨d,hd⟩⟩
    let k : BiWitness (translate (parameters (other∷b) f (other+1) z) p)
      (translate (parameters (other∷b) f m z) p) := ⟨⟨e,he⟩,⟨j,hj⟩⟩
    let middle : BiWitness (wal lo (translate (parameters (lo∷b) f m z) p))
      (wal other (translate (parameters (other∷b) f m z) p)) := ⟨⟨mid,hmid⟩,⟨rev,hrev⟩⟩
    unfold Result
    rw [translate_all _ _ hp,translate_all _ _ hp,parameters_allocator,parameters_allocator,
      advance_parameters,advance_parameters]
    exact ⟨_,_,((BiWitness.all lo h).trans middle |>.trans (BiWitness.all other k).symm).accepted⟩
  · let m := commonAllocator lo other
    have hc := common_coverage_exs hl hr
    have hf := common_eigen_fresh hl hr (lt_exists p)
    obtain ⟨a,d,ha,hd⟩ := ih p (lt_exists p) (lo∷b) f (lo+1) m z (coverage_exs hl) hc.1
    obtain ⟨e,j,he,hj⟩ := ih p (lt_exists p) (other∷b) f (other+1) m z (coverage_exs hr) hc.2
    obtain ⟨mid,rev,hmid,hrev⟩ := bound_head_existential_alpha_certificates p lo other b f m z hc.1 hf.1 hf.2
    let h : BiWitness (translate (parameters (lo∷b) f (lo+1) z) p)
      (translate (parameters (lo∷b) f m z) p) := ⟨⟨a,ha⟩,⟨d,hd⟩⟩
    let k : BiWitness (translate (parameters (other∷b) f (other+1) z) p)
      (translate (parameters (other∷b) f m z) p) := ⟨⟨e,he⟩,⟨j,hj⟩⟩
    let middle : BiWitness (wn (wal lo (wn (translate (parameters (lo∷b) f m z) p))))
      (wn (wal other (wn (translate (parameters (other∷b) f m z) p)))) := ⟨⟨mid,hmid⟩,⟨rev,hrev⟩⟩
    unfold Result
    rw [translate_exs _ _ hp,translate_exs _ _ hp,parameters_allocator,parameters_allocator,
      advance_parameters,advance_parameters,exs_value,exs_value]
    exact ⟨_,_,((BiWitness.all lo h.neg).neg.trans middle |>.trans (BiWitness.all other k.neg).neg.symm).accepted⟩

theorem formula_allocator_certificates (p b f lo other z : V)
    (hl : FormulaCovered b f lo z p) (hr : FormulaCovered b f other z p) :
    ∃ forward backward, BiCertificates forward backward (translate (parameters b f lo z) p)
      (translate (parameters b f other z) p) := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ n : V, ∀ p<n, ∀ b f lo other z : V,
      FormulaCovered b f lo z p → FormulaCovered b f other z p → Result p b f lo other z := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun n : V =>
      ∀ p<n, ∀ b f lo other z : V, FormulaCovered b f lo z p →
        FormulaCovered b f other z p → Result p b f lo other z) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb allocatorInvariant,by trivial,?_⟩
      intro n
      simpa [Result] using (allocator_invariant (V:=V) n).symm
    · intro p hp
      exact False.elim (by simpa using hp)
    · intro n ih p hp
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp hp) with he | hlt
      · subst p
        exact allocator_source_step n ih
      · exact ih p hlt
  exact hall (p+1) p (lt_add_one p) b f lo other z hl hr

attribute [local irreducible] allocatorGraph coverageGraph
noncomputable def allocatorSentence : ArithmeticSentence :=
  “∀ p b f lo other z, !coverageGraph b f lo z p → !coverageGraph b f other z p →
    ∃ forward backward, !allocatorGraph forward backward p b f lo other z”

theorem pa_proves_allocator : theory ⊢ allocatorSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [allocatorSentence,models_iff,coverage_graph,allocator_graph,Matrix.comp_vecCons'']
  intro p b f lo other z hl hr
  exact formula_allocator_certificates p b f lo other z hl hr

#print axioms allocator_source_step
#print axioms formula_allocator_certificates
#print axioms pa_proves_allocator
end PA196.Arithmetic.Transport.RelationalSource.Numeric

