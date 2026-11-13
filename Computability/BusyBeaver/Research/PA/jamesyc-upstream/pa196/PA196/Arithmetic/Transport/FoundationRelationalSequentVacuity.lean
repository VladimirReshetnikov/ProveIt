module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentVacuityInvariant
public import PA196.Arithmetic.Transport.CertificateInterface
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Full-PA model-length vacuity certificate existence for covered source
formulas with explicit fresh finite environments. Not allocator relocation. -/
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

private theorem atom_vacuity (c b f lo z k r ts : V)
    (h : ∃ a d, AtomHead (totalAtom (parameters b f lo z) k r ts) r a d z ∧
      c≠a ∧ c≠d ∧ c≠z) :
    ∃ code, verifyValue code=wim (totalAtom (parameters b f lo z) k r ts)
      (wal c (totalAtom (parameters b f lo z) k r ts))+1 := by
  obtain ⟨a,d,hhead,ha,hd,hz⟩ := h
  rcases hhead with ⟨_,he⟩ | ⟨_,he⟩
  · rw [he]
    exact neighborhood_vacuity_certificate a d z c ha hd hz
  · rw [he]
    have hv : ActualArithmeticGraph.eval membershipExpr a d z 0=wel d a := by
      simp [membershipExpr,wel,wim,implicationValue,PA196.Arithmetic.HeadGraphs.implicationExpr,
        PA196.Arithmetic.HeadGraphs.im,PA196.Arithmetic.HeadGraphs.mem,ActualArithmeticGraph.eval]
    rw [hv]
    exact ⟨(membershipVacuity d a c hd ha).code,(membershipVacuity d a c hd ha).accepted⟩

private def Vacuous (c b f lo z p : V) : Prop :=
  ∃ code, verifyValue code=wim (translate (parameters b f lo z) p)
    (wal c (translate (parameters b f lo z) p))+1

private theorem vacuity_source_step (p : V)
    (ih : ∀ q<p, ∀ c b f lo z : V, FormulaCovered b f lo z q → FreshEnvironment c b f lo z →
      Vacuous c b f lo z q) :
    ∀ c b f lo z : V, FormulaCovered b f lo z p → FreshEnvironment c b f lo z →
      Vacuous c b f lo z p := by
  intro c b f lo z hc hf
  rcases IsUFormula.case_iff.mp hc.2.1.isUFormula with
    ⟨k,r,ts,hr,ht,rfl⟩ | ⟨k,r,ts,hr,ht,rfl⟩ | rfl | rfl |
    ⟨p,q,hp,hq,rfl⟩ | ⟨p,q,hp,hq,rfl⟩ | ⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩
  · unfold Vacuous
    rw [translate_rel _ _ _ _ hr ht]
    exact atom_vacuity c b f lo z k r ts (fresh_rel_payload hc hf)
  · obtain ⟨code,hcode⟩ := atom_vacuity c b f lo z k r ts (fresh_nrel_payload hc hf)
    unfold Vacuous
    rw [translate_nrel _ _ _ _ hr ht,neg_value]
    let out := negationVacuity c _ ⟨code,hcode⟩
    exact ⟨out.code,out.accepted⟩
  · unfold Vacuous
    rw [translate_verum]
    let out := (truthCertificate (V:=V)).all c |>.mp (Dominated.k (wal c 0) 0)
    exact ⟨out.code,out.accepted⟩
  · unfold Vacuous
    rw [translate_falsum]
    exact ⟨(explosion (wal c (1:V))).code,(explosion (wal c (1:V))).accepted⟩
  · obtain ⟨left,hl⟩ := ih p (lt_K!_left p q) c b f lo z (coverage_and hc).1 hf
    obtain ⟨right,hr⟩ := ih q (lt_K!_right p q) c b f lo z (coverage_and hc).2 hf
    unfold Vacuous
    rw [translate_and _ _ _ hp hq,translationAnd_eq]
    let out := conjunctionVacuity c _ _ ⟨left,hl⟩ ⟨right,hr⟩
    exact ⟨out.code,out.accepted⟩
  · obtain ⟨left,hl⟩ := ih p (lt_or_left p q) c b f lo z (coverage_or hc).1 hf
    obtain ⟨right,hr⟩ := ih q (lt_or_right p q) c b f lo z (coverage_or hc).2 hf
    unfold Vacuous
    rw [translate_or _ _ _ hp hq,translationOr_eq]
    let out := implicationVacuity c _ _ (negationVacuity c _ ⟨left,hl⟩) ⟨right,hr⟩
    exact ⟨out.code,out.accepted⟩
  · obtain ⟨code,hcode⟩ := ih p (lt_forall p) c (lo∷b) f (lo+1) z (coverage_all hc) hf.advance
    unfold Vacuous
    rw [translate_all _ _ hp,parameters_allocator,advance_parameters]
    let out := universalVacuity c lo _ ⟨code,hcode⟩
    exact ⟨out.code,out.accepted⟩
  · obtain ⟨code,hcode⟩ := ih p (lt_exists p) c (lo∷b) f (lo+1) z (coverage_exs hc) hf.advance
    unfold Vacuous
    rw [translate_exs _ _ hp,parameters_allocator,advance_parameters,exs_value]
    let out := negationVacuity c _ (universalVacuity c lo _ (negationVacuity c _ ⟨code,hcode⟩))
    exact ⟨out.code,out.accepted⟩

/-- Both source and scan-induction bounds range over the PA model. Formula
coverage and freshness are explicit, not inferred from standard quotations. -/
theorem formula_vacuity_certificate (p c b f lo z : V) (hc : FormulaCovered b f lo z p)
    (hf : FreshEnvironment c b f lo z) :
    ∃ code, verifyValue code=wim (translate (parameters b f lo z) p)
      (wal c (translate (parameters b f lo z) p))+1 := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ n : V, ∀ p<n, ∀ c b f lo z : V, FormulaCovered b f lo z p →
      FreshEnvironment c b f lo z → Vacuous c b f lo z p := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun n : V =>
      ∀ p<n, ∀ c b f lo z : V, FormulaCovered b f lo z p →
        FreshEnvironment c b f lo z → Vacuous c b f lo z p) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb vacuityInvariant,by trivial,?_⟩
      intro n
      simpa [Vacuous] using (vacuity_invariant (V:=V) n).symm
    · intro p hp
      exact False.elim (by simpa using hp)
    · intro n ih p hp
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp hp) with he | hlt
      · subst p
        exact vacuity_source_step n ih
      · exact ih p hlt
  exact hall (p+1) p (lt_add_one p) c b f lo z hc hf

attribute [local irreducible] vacuityGraph coverageGraph freshEnvironmentGraph parametersGraph
noncomputable def vacuitySentence : ArithmeticSentence :=
  “∀ p c b f lo z, !coverageGraph b f lo z p → !freshEnvironmentGraph c b f lo z →
    ∃ param code, !parametersGraph param b f lo z ∧ !vacuityGraph code c param p”

theorem pa_proves_formula_vacuity : theory ⊢ vacuitySentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [vacuitySentence,models_iff,coverage_graph,freshEnvironment_graph,
    parameters_graph,vacuity_graph,Matrix.comp_vecCons'']
  intro p c b f lo z hc hf
  exact formula_vacuity_certificate p c b f lo z hc hf

#print axioms atom_vacuity
#print axioms vacuity_source_step
#print axioms formula_vacuity_certificate
#print axioms pa_proves_formula_vacuity
end PA196.Arithmetic.Transport.RelationalSource.Numeric

