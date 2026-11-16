module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentReserveInvariant
@[expose] public section

/-! Full-PA accepted reserve relocation at a fixed allocator. Both source
coverage guards are retained throughout the model-length induction. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCertificateEquivalence ActualCheckerBlueprint

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

private theorem neg_value (a : V) : ActualArithmeticGraph.eval translationNeg a 0 0 0=wn a := by
  simp [translationNeg,ActualHeadGraphs.neg,wn,wim,implicationValue,
    ActualHeadGraphs.implicationExpr,ActualHeadGraphs.im,ActualArithmeticGraph.eval]
private theorem exs_value (v a : V) :
    ActualArithmeticGraph.eval translationExs v a 0 0=wn (wal v (wn a)) := by
  simp [translationExs,ActualHeadGraphs.ex,ActualHeadGraphs.al,ActualHeadGraphs.neg,
    wn,wal,wim,implicationValue,universalValue,ActualHeadGraphs.universalExpr,
    ActualHeadGraphs.implicationExpr,ActualHeadGraphs.im,ActualArithmeticGraph.eval]

private def Result (p b f lo z other : V) : Prop :=
  ∃ forward backward, BiCertificates forward backward (translate (parameters b f lo z) p)
    (translate (parameters b f lo other) p)

private theorem reserve_source_step (p : V)
    (ih : ∀ q<p, ∀ b f lo z other : V, FormulaCovered b f lo z q → FormulaCovered b f lo other q →
      Result q b f lo z other) :
    ∀ b f lo z other : V, FormulaCovered b f lo z p → FormulaCovered b f lo other p →
      Result p b f lo z other := by
  intro b f lo z other hl hr
  rcases IsUFormula.case_iff.mp hl.2.1.isUFormula with
    ⟨k,r,ts,hrel,ht,rfl⟩ | ⟨k,r,ts,hrel,ht,rfl⟩ | rfl | rfl |
    ⟨p,q,hp,hq,rfl⟩ | ⟨p,q,hp,hq,rfl⟩ | ⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩
  · unfold Result
    rw [translate_rel _ _ _ _ hrel ht,translate_rel _ _ _ _ hrel ht]
    exact reserve_atom_certificates b f lo z other k r ts (coverage_rel_atom hl) hr.1.1
  · obtain ⟨c,d,hc,hd⟩ := reserve_atom_certificates b f lo z other k r ts (coverage_nrel_atom hl) hr.1.1
    let h : BiWitness (totalAtom (parameters b f lo z) k r ts)
      (totalAtom (parameters b f lo other) k r ts) := ⟨⟨c,hc⟩,⟨d,hd⟩⟩
    unfold Result
    rw [translate_nrel _ _ _ _ hrel ht,translate_nrel _ _ _ _ hrel ht,neg_value,neg_value]
    exact ⟨_,_,h.neg.accepted⟩
  · unfold Result
    rw [translate_verum,translate_verum]
    exact ⟨_,_,(BiWitness.refl _).accepted⟩
  · unfold Result
    rw [translate_falsum,translate_falsum]
    exact ⟨_,_,(BiWitness.refl _).accepted⟩
  · obtain ⟨a,d,ha,hd⟩ := ih p (lt_K!_left p q) b f lo z other (coverage_and hl).1 (coverage_and hr).1
    obtain ⟨e,j,he,hj⟩ := ih q (lt_K!_right p q) b f lo z other (coverage_and hl).2 (coverage_and hr).2
    let h : BiWitness (translate (parameters b f lo z) p) (translate (parameters b f lo other) p) := ⟨⟨a,ha⟩,⟨d,hd⟩⟩
    let k : BiWitness (translate (parameters b f lo z) q) (translate (parameters b f lo other) q) := ⟨⟨e,he⟩,⟨j,hj⟩⟩
    unfold Result
    rw [translate_and _ _ _ hp hq,translate_and _ _ _ hp hq,translationAnd_eq,translationAnd_eq]
    exact ⟨_,_,(h.imp k.neg).neg.accepted⟩
  · obtain ⟨a,d,ha,hd⟩ := ih p (lt_or_left p q) b f lo z other (coverage_or hl).1 (coverage_or hr).1
    obtain ⟨e,j,he,hj⟩ := ih q (lt_or_right p q) b f lo z other (coverage_or hl).2 (coverage_or hr).2
    let h : BiWitness (translate (parameters b f lo z) p) (translate (parameters b f lo other) p) := ⟨⟨a,ha⟩,⟨d,hd⟩⟩
    let k : BiWitness (translate (parameters b f lo z) q) (translate (parameters b f lo other) q) := ⟨⟨e,he⟩,⟨j,hj⟩⟩
    unfold Result
    rw [translate_or _ _ _ hp hq,translate_or _ _ _ hp hq,translationOr_eq,translationOr_eq]
    exact ⟨_,_,(h.neg.imp k).accepted⟩
  · obtain ⟨c,d,hc,hd⟩ := ih p (lt_forall p) (lo∷b) f (lo+1) z other (coverage_all hl) (coverage_all hr)
    let h : BiWitness (translate (parameters (lo∷b) f (lo+1) z) p)
      (translate (parameters (lo∷b) f (lo+1) other) p) := ⟨⟨c,hc⟩,⟨d,hd⟩⟩
    unfold Result
    rw [translate_all _ _ hp,translate_all _ _ hp,parameters_allocator,parameters_allocator,
      advance_parameters,advance_parameters]
    exact ⟨_,_,(BiWitness.all lo h).accepted⟩
  · obtain ⟨c,d,hc,hd⟩ := ih p (lt_exists p) (lo∷b) f (lo+1) z other (coverage_exs hl) (coverage_exs hr)
    let h : BiWitness (translate (parameters (lo∷b) f (lo+1) z) p)
      (translate (parameters (lo∷b) f (lo+1) other) p) := ⟨⟨c,hc⟩,⟨d,hd⟩⟩
    unfold Result
    rw [translate_exs _ _ hp,translate_exs _ _ hp,parameters_allocator,parameters_allocator,
      advance_parameters,advance_parameters,exs_value,exs_value]
    exact ⟨_,_,(BiWitness.all lo h.neg).neg.accepted⟩

theorem formula_reserve_certificates (p b f lo z other : V)
    (hl : FormulaCovered b f lo z p) (hr : FormulaCovered b f lo other p) :
    ∃ forward backward, BiCertificates forward backward (translate (parameters b f lo z) p)
      (translate (parameters b f lo other) p) := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ n : V, ∀ p<n, ∀ b f lo z other : V,
      FormulaCovered b f lo z p → FormulaCovered b f lo other p → Result p b f lo z other := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun n : V =>
      ∀ p<n, ∀ b f lo z other : V, FormulaCovered b f lo z p →
        FormulaCovered b f lo other p → Result p b f lo z other) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb reserveInvariant,by trivial,?_⟩
      intro n
      simpa [Result] using (reserve_invariant (V:=V) n).symm
    · intro p hp
      exact False.elim (by simpa using hp)
    · intro n ih p hp
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp hp) with he | hlt
      · subst p
        exact reserve_source_step n ih
      · exact ih p hlt
  exact hall (p+1) p (lt_add_one p) b f lo z other hl hr

attribute [local irreducible] reserveGraph coverageGraph
noncomputable def reserveSentence : ArithmeticSentence :=
  “∀ p b f lo z other, !coverageGraph b f lo z p → !coverageGraph b f lo other p →
    ∃ forward backward, !reserveGraph forward backward p b f lo z other”

theorem pa_proves_reserve : theory ⊢ reserveSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [reserveSentence,models_iff,coverage_graph,reserve_graph,Matrix.comp_vecCons'']
  intro p b f lo z other hl hr
  exact formula_reserve_certificates p b f lo z other hl hr

#print axioms reserve_source_step
#print axioms formula_reserve_certificates
#print axioms pa_proves_reserve
end M6.PA.RelationalSource.Numeric

