module
public import M6PA.Theory
public import M6PA.Calibration.ActualCertificateEquivalenceInvariant
@[expose] public section

/-! Full-PA model-length induction for the exact existential NNF certificate
relation. No external Nat structural induction or recipe-graph uniqueness. -/
namespace M6.PA.ActualCertificateEquivalence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open RelationalSource RelationalSource.Numeric

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem neg_value (a : V) : ActualArithmeticGraph.eval translationNeg a 0 0 0=wn a := by
  simp [translationNeg,ActualHeadGraphs.neg,wn,wim,implicationValue,
    ActualHeadGraphs.implicationExpr,ActualHeadGraphs.im,ActualArithmeticGraph.eval]
private theorem and_value (a b : V) :
    ActualArithmeticGraph.eval translationAnd a b 0 0=wn (wim a (wn b)) := by
  simp [translationAnd,ActualHeadGraphs.conj,ActualHeadGraphs.neg,wn,wim,implicationValue,
    ActualHeadGraphs.implicationExpr,ActualHeadGraphs.im,ActualArithmeticGraph.eval]
private theorem or_value (a b : V) : ActualArithmeticGraph.eval translationOr a b 0 0=wim (wn a) b := by
  simp [translationOr,ActualHeadGraphs.neg,wn,wim,implicationValue,
    ActualHeadGraphs.implicationExpr,ActualHeadGraphs.im,ActualArithmeticGraph.eval]
private theorem all_value (v a : V) : ActualArithmeticGraph.eval ActualHeadGraphs.universalExpr v a 0 0=wal v a := rfl
private theorem exs_value (v a : V) :
    ActualArithmeticGraph.eval translationExs v a 0 0=wn (wal v (wn a)) := by
  simp [translationExs,ActualHeadGraphs.ex,ActualHeadGraphs.al,ActualHeadGraphs.neg,
    wn,wal,wim,implicationValue,universalValue,ActualHeadGraphs.universalExpr,
    ActualHeadGraphs.implicationExpr,ActualHeadGraphs.im,ActualArithmeticGraph.eval]

private def Result (param p : V) : Prop :=
  ∃ c d, BiCertificates c d (translate param (Bootstrapping.neg language p)) (wn (translate param p))

variable [V↓[ℒₒᵣ] ⊧* theory]

/-- The source constructor step uses strict numeric child-code inequalities. -/
private theorem source_step (p : V) (hvalid : IsUFormula language p)
    (ih : ∀ q<p, IsUFormula language q → ∀ param, Result param q) :
    ∀ param, Result param p := by
  intro param
  rcases IsUFormula.case_iff.mp hvalid with
    ⟨k,r,ts,hr,ht,rfl⟩ | ⟨k,r,ts,hr,ht,rfl⟩ | rfl | rfl |
    ⟨p,q,hp,hq,rfl⟩ | ⟨p,q,hp,hq,rfl⟩ | ⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩
  · unfold Result
    rw [Bootstrapping.neg_rel hr ht,translate_nrel _ _ _ _ hr ht,
      translate_rel _ _ _ _ hr ht,neg_value]
    exact ⟨_,_,(BiWitness.refl _).accepted⟩
  · unfold Result
    rw [Bootstrapping.neg_nrel hr ht,translate_rel _ _ _ _ hr ht,
      translate_nrel _ _ _ _ hr ht,neg_value]
    exact ⟨_,_,(BiWitness.doubleNegation _).accepted⟩
  · unfold Result
    rw [Bootstrapping.neg_verum,translate_falsum,translate_verum]
    exact ⟨_,_,(trueNegation (V:=V)).accepted⟩
  · unfold Result
    rw [Bootstrapping.neg_falsum,translate_verum,translate_falsum]
    exact ⟨_,_,(falseNegation (V:=V)).accepted⟩
  · obtain ⟨c,d,hc,hd⟩ := ih p (lt_K!_left p q) hp param
    obtain ⟨e,f,he,hf⟩ := ih q (lt_K!_right p q) hq param
    let ha : BiWitness (translate param (Bootstrapping.neg language p)) (wn (translate param p)) :=
      ⟨⟨c,hc⟩,⟨d,hd⟩⟩
    let hb : BiWitness (translate param (Bootstrapping.neg language q)) (wn (translate param q)) :=
      ⟨⟨e,he⟩,⟨f,hf⟩⟩
    unfold Result
    rw [Bootstrapping.neg_and hp hq,translate_or _ _ _ hp.neg hq.neg,
      translate_and _ _ _ hp hq,or_value,and_value]
    exact ⟨_,_,(andNegation ha hb).accepted⟩
  · obtain ⟨c,d,hc,hd⟩ := ih p (lt_or_left p q) hp param
    obtain ⟨e,f,he,hf⟩ := ih q (lt_or_right p q) hq param
    let ha : BiWitness (translate param (Bootstrapping.neg language p)) (wn (translate param p)) :=
      ⟨⟨c,hc⟩,⟨d,hd⟩⟩
    let hb : BiWitness (translate param (Bootstrapping.neg language q)) (wn (translate param q)) :=
      ⟨⟨e,he⟩,⟨f,hf⟩⟩
    unfold Result
    rw [Bootstrapping.neg_or hp hq,translate_and _ _ _ hp.neg hq.neg,
      translate_or _ _ _ hp hq,and_value,or_value]
    exact ⟨_,_,(orNegation ha hb).accepted⟩
  · obtain ⟨c,d,hc,hd⟩ := ih p (lt_forall p) hp (advance param)
    let ha : BiWitness (translate (advance param) (Bootstrapping.neg language p))
        (wn (translate (advance param) p)) := ⟨⟨c,hc⟩,⟨d,hd⟩⟩
    unfold Result
    rw [Bootstrapping.neg_all hp,translate_exs _ _ hp.neg,translate_all _ _ hp,
      exs_value,all_value]
    exact ⟨_,_,(allNegation (nth param 2) ha).accepted⟩
  · obtain ⟨c,d,hc,hd⟩ := ih p (lt_exists p) hp (advance param)
    let ha : BiWitness (translate (advance param) (Bootstrapping.neg language p))
        (wn (translate (advance param) p)) := ⟨⟨c,hc⟩,⟨d,hd⟩⟩
    unfold Result
    rw [Bootstrapping.neg_ex hp,translate_all _ _ hp.neg,translate_exs _ _ hp,
      all_value,exs_value]
    exact ⟨_,_,(exsNegation (nth param 2) ha).accepted⟩

/-- Uniform in arbitrary model source and parameter codes. The displayed
arithmetic formula supplies full-PA induction, not a Sigma-one shortcut. -/
theorem nnf_certificates (p param : V) (hp : IsUFormula language p) :
    ∃ c d, BiCertificates c d (translate param (Bootstrapping.neg language p))
      (wn (translate param p)) := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ n : V, ∀ q<n, IsUFormula language q → ∀ param, Result param q := by
    refine InductionScheme.succ_induction (C:=Set.univ)
      (P:=fun n : V => ∀ q<n, IsUFormula language q → ∀ param, Result param q) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb nnfInvariant,by trivial,?_⟩
      intro n
      simpa [Result] using (nnf_invariant (V:=V) n).symm
    · intro q hq
      exact False.elim (by simpa using hq)
    · intro n ih q hq hvalid param
      have hle : q≤n := lt_succ_iff_le.mp hq
      rcases eq_or_lt_of_le hle with he | hlt
      · subst q
        exact source_step n hvalid ih param
      · exact ih q hlt hvalid param
  exact hall (p+1) p (lt_add_one p) hp param

theorem nnf_graph_exists (p param : V) (hp : IsUFormula language p) :
    ∃ c d, nnfGraph.val.Evalb ![c,d,param,p] := by
  obtain ⟨c,d,h⟩ := nnf_certificates p param hp
  exact ⟨c,d,(nnf_graph _ _ _ _).mpr h⟩

attribute [local irreducible] nnfGraph

noncomputable def nnfSentence : ArithmeticSentence :=
  “∀ p param, !((isUFormula language).sigma) p → ∃ c d, !nnfGraph c d param p”

/-- PA itself proves the paired actual-certificate existence statement. -/
theorem pa_proves_nnf : theory ⊢ nnfSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [nnfSentence,models_iff,nnf_graph,Matrix.comp_vecCons'']
  intro p param hp
  exact nnf_certificates p param hp

#print axioms pa_proves_nnf
#print axioms source_step
#print axioms nnf_certificates
#print axioms nnf_graph_exists
end M6.PA.ActualCertificateEquivalence

