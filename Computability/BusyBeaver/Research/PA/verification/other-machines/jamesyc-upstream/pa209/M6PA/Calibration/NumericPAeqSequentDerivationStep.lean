module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSequentRequestedLeaves
public import M6PA.Calibration.NumericPAeqSequentAllRule
public import M6PA.Calibration.NumericPAeqSequentExsRule
public import M6PA.Calibration.NumericPAeqSequentShiftRule
public import M6PA.Calibration.NumericPAeqSequentProofBudgetTail
@[expose] public section
namespace M6.PA.NumericPAeqFormula.Sequent
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem ordinary_derivation_requested_step (d : V)
    (ih : ∀ child<d, Derivation Presentation.ordinaryPAeq child → ∀ f : V,
      SourceProofBudget child f → RequestedCertificate f (fstIdx child))
    (hd : Derivation Presentation.ordinaryPAeq d) (f : V) (hb : SourceProofBudget d f) :
    RequestedCertificate f (fstIdx d) := by
  have hsup := hb.sequent hd
  rcases Derivation.case_iff.mp hd with ⟨hs,hcases⟩
  rcases hcases with ⟨s,p,rfl,hp,hn⟩ | ⟨s,rfl,hm⟩ |
    ⟨s,p,q,dp,dq,rfl,hm,hdp,hdq⟩ | ⟨s,p,q,dp,rfl,hm,hdp⟩ |
    ⟨s,p,dp,rfl,hm,hdp⟩ | ⟨s,p,t,dp,rfl,hm,ht,hdp⟩ |
    ⟨s,dp,rfl,hsub,hdp⟩ | ⟨s,dp,rfl,heq,hdp⟩ |
    ⟨s,p,dp,dq,rfl,hdp,hdq⟩ | ⟨s,p,rfl,hp,hax⟩ <;>
    simp only [fstIdx_axL,fstIdx_verumIntro,fstIdx_andIntro,fstIdx_orIntro,
      fstIdx_allIntro,fstIdx_exsIntro,fstIdx_wkRule,fstIdx_shiftRule,fstIdx_cutRule,fstIdx_axm] at hs hsup ⊢
  · exact identity_rule_requested hb.1 hsup hp hn
  · exact verum_rule_requested hb.1 hsup hm
  · apply and_rule_requested hb.1 hsup hm
    · simpa only [hdp.1] using ih dp (by simp) hdp.2 f (hb.descend (by exact (by simp : _ < _).le))
    · simpa only [hdq.1] using ih dq (by simp) hdq.2 f (hb.descend (by exact (by simp : _ < _).le))
  · apply or_rule_requested hb.1 hsup hm
    simpa only [hdp.1] using ih dp (by simp) hdp.2 f (hb.descend (by exact (by simp : _ < _).le))
  · apply all_rule_requested hb.1 hsup hm
    simpa only [hdp.1] using ih dp (by simp) hdp.2 _ (hb.eigen_child (by exact (by simp : _ < _).le))
  · apply exs_rule_requested hb.1 hsup hm ht (hb.term ht (t_lt_exsIntro s p t dp).le)
    simpa only [hdp.1] using ih dp (by simp) hdp.2 f (hb.descend (by exact (by simp : _ < _).le))
  · have hchild := hb.descend (show dp≤wkRule s dp from (by simp : dp<wkRule s dp).le)
    exact weakening_rule_requested hb.1 (hchild.sequent hdp) hsup hsub (ih dp (by simp) hdp f hchild)
  · have htail := hb.tail_child (show dp<shiftRule s dp by simp)
    have child := ih dp (by simp) hdp _ htail
    rcases nil_or_adjoin f with rfl | ⟨x,f,rfl⟩
    · have hpos := ordinary_derivation_positive hd
      have : shiftRule s dp≤0 := by simpa using hb.2
      exact False.elim (not_le_of_gt hpos this)
    · have hx : IsSemiterm language 0 x := (by simpa using hb.1 : IsSemiterm language 0 x ∧ IsSemitermVec language (len f) 0 f).1
      have hf : IsSemitermVec language (len f) 0 f := by simpa using htail.1
      rw [heq]
      exact shift_rule_requested hf hx (by simpa using htail.sequent hdp) (by simpa using child)
  · have bp := hb.descend (show dp≤cutRule s p dp dq from (by simp : dp<cutRule s p dp dq).le)
    have bq := hb.descend (show dq≤cutRule s p dp dq from (by simp : dq<cutRule s p dp dq).le)
    have hp := bp.sequent hdp.2 p (by simp [hdp.1])
    have hn := bq.sequent hdq.2 (neg Presentation.language p) (by simp [hdq.1])
    apply cut_rule_requested hb.1 hsup hp hn
    · simpa only [hdp.1] using ih dp (by simp) hdp.2 f bp
    · simpa only [hdq.1] using ih dq (by simp) hdq.2 f bq
  · exact axiom_rule_requested hb.1 hsup hp hax

#print axioms ordinary_derivation_requested_step
end M6.PA.NumericPAeqFormula.Sequent

