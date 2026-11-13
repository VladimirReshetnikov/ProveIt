module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentRenameInvariant
@[expose] public section

/-! Full-PA source-code induction for conditional formula renaming under
explicit finite environment relations, at a common allocator and reserve. -/
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

private def Result (p x y b bb f ff lo z : V) : Prop :=
  ∃ forward backward, ConditionalBiCertificates forward backward (neighborhoodValue x y z)
    (translate (parameters b f lo z) p) (translate (parameters bb ff lo z) p)

private theorem rename_source_step (p : V)
    (ih : ∀ q<p, ∀ x y b bb f ff lo z : V, FormulaCovered b f lo z q →
      RenameEnvironment x y b bb → RenameEnvironment x y f ff → x<lo → y<lo →
      Result q x y b bb f ff lo z) :
    ∀ x y b bb f ff lo z : V, FormulaCovered b f lo z p →
      RenameEnvironment x y b bb → RenameEnvironment x y f ff → x<lo → y<lo →
      Result p x y b bb f ff lo z := by
  intro x y b bb f ff lo z hc hb hf hx hy
  have hzy : z≠y := Ne.symm (ne_of_lt (lt_of_lt_of_le hy hc.1.1.2.1))
  rcases IsUFormula.case_iff.mp hc.2.1.isUFormula with
    ⟨k,r,ts,hr,ht,rfl⟩ | ⟨k,r,ts,hr,ht,rfl⟩ | rfl | rfl |
    ⟨p,q,hp,hq,rfl⟩ | ⟨p,q,hp,hq,rfl⟩ | ⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩
  · unfold Result
    rw [translate_rel _ _ _ _ hr ht,translate_rel _ _ _ _ hr ht]
    exact rename_atom_certificates x y b bb f ff lo z k r ts hb hf hzy (coverage_rel_atom hc)
  · obtain ⟨a,d,ha,hd⟩ := rename_atom_certificates x y b bb f ff lo z k r ts hb hf hzy (coverage_nrel_atom hc)
    let h : ConditionalBiWitness (neighborhoodValue x y z)
      (totalAtom (parameters b f lo z) k r ts) (totalAtom (parameters bb ff lo z) k r ts) :=
      ⟨⟨a,ha⟩,⟨d,hd⟩⟩
    unfold Result
    rw [translate_nrel _ _ _ _ hr ht,translate_nrel _ _ _ _ hr ht,neg_value,neg_value]
    exact ⟨_,_,h.neg.accepted⟩
  · unfold Result
    rw [translate_verum,translate_verum]
    exact ⟨_,_,(ConditionalBiWitness.refl (neighborhoodValue x y z) 0).accepted⟩
  · unfold Result
    rw [translate_falsum,translate_falsum]
    exact ⟨_,_,(ConditionalBiWitness.refl (neighborhoodValue x y z) 1).accepted⟩
  · obtain ⟨a,d,ha,hd⟩ := ih p (lt_K!_left p q) x y b bb f ff lo z (coverage_and hc).1 hb hf hx hy
    obtain ⟨e,j,he,hj⟩ := ih q (lt_K!_right p q) x y b bb f ff lo z (coverage_and hc).2 hb hf hx hy
    let h : ConditionalBiWitness (neighborhoodValue x y z) (translate (parameters b f lo z) p)
      (translate (parameters bb ff lo z) p) := ⟨⟨a,ha⟩,⟨d,hd⟩⟩
    let k : ConditionalBiWitness (neighborhoodValue x y z) (translate (parameters b f lo z) q)
      (translate (parameters bb ff lo z) q) := ⟨⟨e,he⟩,⟨j,hj⟩⟩
    unfold Result
    rw [translate_and _ _ _ hp hq,translate_and _ _ _ hp hq,translationAnd_eq,translationAnd_eq]
    exact ⟨_,_,(h.imp k.neg).neg.accepted⟩
  · obtain ⟨a,d,ha,hd⟩ := ih p (lt_or_left p q) x y b bb f ff lo z (coverage_or hc).1 hb hf hx hy
    obtain ⟨e,j,he,hj⟩ := ih q (lt_or_right p q) x y b bb f ff lo z (coverage_or hc).2 hb hf hx hy
    let h : ConditionalBiWitness (neighborhoodValue x y z) (translate (parameters b f lo z) p)
      (translate (parameters bb ff lo z) p) := ⟨⟨a,ha⟩,⟨d,hd⟩⟩
    let k : ConditionalBiWitness (neighborhoodValue x y z) (translate (parameters b f lo z) q)
      (translate (parameters bb ff lo z) q) := ⟨⟨e,he⟩,⟨j,hj⟩⟩
    unfold Result
    rw [translate_or _ _ _ hp hq,translate_or _ _ _ hp hq,translationOr_eq,translationOr_eq]
    exact ⟨_,_,(h.neg.imp k).accepted⟩
  · have child := coverage_all hc
    obtain ⟨a,d,ha,hd⟩ := ih p (lt_forall p) x y (lo∷b) (lo∷bb) f ff (lo+1) z child
      (hb.adjoin_fixed (Ne.symm (ne_of_lt hx))) hf (lt_trans hx (lt_add_one lo)) (lt_trans hy (lt_add_one lo))
    let h : ConditionalBiWitness (neighborhoodValue x y z) (translate (parameters (lo∷b) f (lo+1) z) p)
      (translate (parameters (lo∷bb) ff (lo+1) z) p) := ⟨⟨a,ha⟩,⟨d,hd⟩⟩
    have hlz : lo<z := lt_of_lt_of_le (lt_add_one lo) child.1.1.2.1
    let hv := neighborhoodEqualityVacuity x y z lo (Ne.symm (ne_of_lt hx)) (Ne.symm (ne_of_lt hy)) (ne_of_lt hlz)
    unfold Result
    rw [translate_all _ _ hp,translate_all _ _ hp,parameters_allocator,parameters_allocator,
      advance_parameters,advance_parameters]
    exact ⟨_,_,(h.all lo hv).accepted⟩
  · have child := coverage_exs hc
    obtain ⟨a,d,ha,hd⟩ := ih p (lt_exists p) x y (lo∷b) (lo∷bb) f ff (lo+1) z child
      (hb.adjoin_fixed (Ne.symm (ne_of_lt hx))) hf (lt_trans hx (lt_add_one lo)) (lt_trans hy (lt_add_one lo))
    let h : ConditionalBiWitness (neighborhoodValue x y z) (translate (parameters (lo∷b) f (lo+1) z) p)
      (translate (parameters (lo∷bb) ff (lo+1) z) p) := ⟨⟨a,ha⟩,⟨d,hd⟩⟩
    have hlz : lo<z := lt_of_lt_of_le (lt_add_one lo) child.1.1.2.1
    let hv := neighborhoodEqualityVacuity x y z lo (Ne.symm (ne_of_lt hx)) (Ne.symm (ne_of_lt hy)) (ne_of_lt hlz)
    unfold Result
    rw [translate_exs _ _ hp,translate_exs _ _ hp,parameters_allocator,parameters_allocator,
      advance_parameters,advance_parameters,exs_value,exs_value]
    exact ⟨_,_,((h.neg.all lo hv).neg).accepted⟩

theorem formula_rename_certificates (p x y b bb f ff lo z : V) (hc : FormulaCovered b f lo z p)
    (hb : RenameEnvironment x y b bb) (hf : RenameEnvironment x y f ff) (hx : x<lo) (hy : y<lo) :
    ∃ forward backward, ConditionalBiCertificates forward backward (neighborhoodValue x y z)
      (translate (parameters b f lo z) p) (translate (parameters bb ff lo z) p) := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ n : V, ∀ p<n, ∀ x y b bb f ff lo z : V, FormulaCovered b f lo z p →
      RenameEnvironment x y b bb → RenameEnvironment x y f ff → x<lo → y<lo →
      Result p x y b bb f ff lo z := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun n : V =>
      ∀ p<n, ∀ x y b bb f ff lo z : V, FormulaCovered b f lo z p →
        RenameEnvironment x y b bb → RenameEnvironment x y f ff → x<lo → y<lo →
        Result p x y b bb f ff lo z) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb renameFormulaInvariant,by trivial,?_⟩
      intro n
      simpa [Result] using (renameFormula_invariant (V:=V) n).symm
    · intro p hp
      exact False.elim (by simpa using hp)
    · intro n ih p hp
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp hp) with he | hlt
      · subst p
        exact rename_source_step n ih
      · exact ih p hlt
  exact hall (p+1) p (lt_add_one p) x y b bb f ff lo z hc hb hf hx hy

attribute [local irreducible] renameFormulaGraph renameEnvironmentGraph coverageGraph
noncomputable def renameFormulaSentence : ArithmeticSentence :=
  “∀ p x y b bb f ff lo z, !coverageGraph b f lo z p →
    !renameEnvironmentGraph x y b bb → !renameEnvironmentGraph x y f ff → x<lo → y<lo →
    ∃ forward backward, !renameFormulaGraph forward backward p x y b bb f ff lo z”

theorem pa_proves_formula_rename : theory ⊢ renameFormulaSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [renameFormulaSentence,models_iff,coverage_graph,renameEnvironment_graph,
    renameFormula_graph,Matrix.comp_vecCons'']
  intro p x y b bb f ff lo z hc hb hf hx hy
  exact formula_rename_certificates p x y b bb f ff lo z hc hb hf hx hy

#print axioms rename_source_step
#print axioms formula_rename_certificates
#print axioms pa_proves_formula_rename
end M6.PA.RelationalSource.Numeric

