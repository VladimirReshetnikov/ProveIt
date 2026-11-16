module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationStepCertificate
@[expose] public section

/-! Discharge the concrete certificate into the explicitly universally closed
ordinary PAeq theory, using actual Theory.Proof data, not completeness. -/
namespace M6.PA.Presentation
open FFL FFL.FirstOrder

theorem embed_close_eq (p : Proposition language) (hp : p.freeVariables = ∅) :
    (Rewriting.emb p.univCl : Proposition language) = p := by
  simpa only [Semiformula.coe_univCl_eq_univCl'] using Semiformula.univCl'_eq_self_of p hp

theorem embed_closed_list (Γ : List (Proposition language))
    (hc : ∀ p ∈ Γ,p.freeVariables = ∅) :
    (Γ.map Semiformula.univCl).map (fun p : Sentence language => (Rewriting.emb p : Proposition language)) = Γ := by
  induction Γ with
  | nil => rfl
  | cons a Γ ih =>
    simp only [List.map_cons]
    rw [embed_close_eq a (hc a (by simp)),ih (by intro p hp; exact hc p (by simp [hp]))]

def ND.closedTheoryProof {T : Theory language} {Γ : List (Proposition language)}
    {p : Proposition language} (d : ND.Proof Γ p)
    (hc : ∀ q ∈ Γ,q.freeVariables = ∅) (hp : p.freeVariables = ∅)
    (ht : ∀ q ∈ Γ,q.univCl ∈ T) : T.Proof p.univCl where
  axioms := (Γ.map Semiformula.univCl : Multiset (Sentence language))
  axioms_mem := by
    intro σ hσ
    simp only [Multiset.mem_coe,List.mem_map] at hσ
    rcases hσ with ⟨q,hq,rfl⟩
    exact ht q hq
  derivation := d.cast (by
    have hm : ((Γ.map Semiformula.univCl : Multiset (Sentence language)).map Rewriting.emb) =
        (Γ : Multiset (Proposition language)) := by
      simpa only [Multiset.map_coe] using congrArg (fun xs : List (Proposition language) =>
        (xs : Multiset (Proposition language))) (embed_closed_list Γ hc)
    simp only [Multiset.map_add,Multiset.map_atom,Multiset.map_tilde_comm]
    rw [hm,embed_close_eq p hp]
    simp only [ND.negatives,Multiset.tilde_def,Multiset.map_coe,Semiformula.neg_eq]
    exact add_comm _ _)

theorem stepContext_closed (p : Proposition language) (hp : p ∈ stepCertificateContext) :
    p.freeVariables = ∅ := by
  simp only [stepCertificateContext,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    simp [addZero,addSucc,succCongruence,transitivity,inductionFormula,stepProperty,
      eq,add,succ,zero,implies,Semiformula.freeVariables,Semiformula.neg,
      Semiformula.rewAux,Semiterm.freeVariables,Rew.func,Fin.univ_succ]

def addOneSuccessorProof : ordinaryPAeq.Proof (Semiformula.all stepProperty).univCl :=
  ND.closedTheoryProof addOneSuccessorCertificate stepContext_closed
    (by simp [stepProperty,eq,add,succ,zero,Semiformula.freeVariables,
      Semiterm.freeVariables,Fin.univ_succ])
    (fun q hq => ⟨q,stepContext_is_PAeq q hq,rfl⟩)

theorem paeq_proves_addOneSuccessor : ordinaryPAeq ⊢ (Semiformula.all stepProperty).univCl :=
  ⟨addOneSuccessorProof⟩

#print axioms addOneSuccessorProof
#print axioms paeq_proves_addOneSuccessor
end M6.PA.Presentation
