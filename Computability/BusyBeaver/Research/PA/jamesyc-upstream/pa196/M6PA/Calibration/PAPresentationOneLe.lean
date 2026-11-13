module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationLtTrans
@[expose] public section

namespace M6.PA.Presentation
open FFL FFL.FirstOrder

def oneLe {ξ : Type} {n : Nat} (t : Semiterm language ξ n) : Semiformula language ξ n :=
  .or (eq (succ zero) t) (less (succ zero) t)
theorem oneLe_rew {ξ ζ : Type} {n m : Nat} (ω : Rew language ξ n ζ m) (t : Semiterm language ξ n) :
    Semiformula.rewAux ω (oneLe t) = oneLe (ω t) := by
  change Semiformula.or (Semiformula.rewAux ω (eq (succ zero) t))
    (Semiformula.rewAux ω (less (succ zero) t)) = _
  rw [eq_rew,less_rew,rew_succ,rew_zero]
  rfl

def oneLeSuccProperty : Semiproposition language 1 := oneLe (succ (.bvar 0))
def oneLeContext : List ND.Form := equalityContext ++ [addZero,addSucc,inductionFormula oneLeSuccProperty]

def oneLeSuccCertificate : ND.Proof oneLeContext (.all oneLeSuccProperty) := by
  let Γ := oneLeContext
  let E := equalityContextPremises.weaken (Δ := Γ) (by intro p hp; simp [Γ,oneLeContext,hp])
  have az : ND.Proof Γ addZero := ND.assumption (by simp [Γ,oneLeContext])
  have ar : ND.Proof Γ addSucc := ND.assumption (by simp [Γ,oneLeContext])
  have ind : ND.Proof Γ (inductionFormula oneLeSuccProperty) := ND.assumption (by simp [Γ,oneLeContext])
  have base : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![zero]) oneLeSuccProperty) := by
    rw [oneLeSuccProperty,oneLe_rew,rew_succ,Rew.subst_bvar]
    exact ND.orLeft (E.reflexive (succ zero))
  have step : ND.Proof Γ (.all (inductionStep oneLeSuccProperty (succ (.bvar 0)))) := by
    apply ND.allIntro
    let x : GroundTerm := .fvar 0
    let ES := E.shifted
    have az' := ND.shiftClosed az (by
      simp [addZero,eq,add,zero,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
    have ar' := ND.shiftClosed ar (by
      simp [addSucc,eq,add,succ,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
    have h0 : ND.Proof (ND.shifted Γ) (eq (add zero (succ x)) (succ x)) := by
      have d := ND.allElim _ (succ x) az'
      convert d using 1 <;> dsimp [addZero] <;> equalityInstanceSyntax
    have h1 : ND.Proof (ND.shifted Γ) (eq (add (succ zero) (succ x)) (succ (add zero (succ x)))) := by
      have d := ND.allElim2 _ zero (succ x) ar'
      convert d using 1 <;> dsimp [addSucc] <;> equalityInstanceSyntax
    have he := ES.transitivityOf h1 (ND.mp h0 (ES.successor (add zero (succ x)) (succ x)))
    have hp : ND.Proof (ND.shifted Γ) (oneLe (succ (succ x))) :=
      ND.orRight (ND.lessIntro (succ zero) (succ (succ x)) x he)
    rw [free_inductionStep]
    have hs : ND.Proof (ND.shifted Γ) (implies oneLeSuccProperty.free (oneLe (succ (succ x)))) := by
      apply ND.impIntro
      exact ND.weaken hp (fun p hp => List.mem_cons_of_mem _ hp)
    convert hs using 1
    change implies _ (Semiformula.rewAux (Rew.subst ![Rew.free (succ (.bvar 0))])
      (Semiformula.rewAux Rew.shift (oneLe (succ (.bvar 0))))) = _
    rw [oneLe_rew,rew_succ,oneLe_rew,rew_succ]
    simp [Rew.shift_bvar,Rew.subst_bvar,x]
  exact ND.mp step (ND.mp base ind)

theorem oneLeContext_mem_theory (q : ND.Form) (hq : q ∈ oneLeContext) : q.univCl ∈ ordinaryPAeq := by
  simp only [oneLeContext,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with hq | rfl | rfl | rfl
  · exact ⟨q,equalityContext_is_PAeq q hq,rfl⟩
  · exact ⟨addZero,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨addSucc,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨inductionFormula oneLeSuccProperty,.induction oneLeSuccProperty,rfl⟩

def oneLeSuccInstance (a : GroundTerm) : ND.Proof (closedContext oneLeContext) (oneLe (succ a)) := by
  have h := ND.allElim _ a (ND.replaceByClosures oneLeSuccCertificate)
  change ND.Proof _ (Semiformula.rewAux (Rew.subst ![a]) oneLeSuccProperty) at h
  simpa only [oneLeSuccProperty,oneLe_rew,rew_succ,Rew.subst_bvar,Matrix.cons_val_zero] using h

def oneLePositiveInstance (a : GroundTerm) : ND.Proof (closedContext oneLeContext)
    (implies (less zero a) (oneLe a)) := by
  let Γ := closedContext oneLeContext
  apply ND.impIntro
  let Δ := less zero a :: Γ
  have hp : ND.Proof Δ (less zero a) := ND.assumption (by simp [Δ])
  apply ND.lessElim zero a hp
  let x := Rew.shift a
  let w : GroundTerm := .fvar 0
  let h := eq (add zero (succ w)) x
  let Θ := h :: ND.shifted Δ
  have incl : ∀ p,p ∈ Γ → p ∈ Θ := by
    intro p hp
    apply List.mem_cons_of_mem
    exact closed_members_shifted (closedContext_closed oneLeContext)
      (fun p hp => List.mem_cons_of_mem _ hp) p hp
  have ec : EqualityPremises Γ := equalityContextPremises.weaken (Δ := Γ) (by
    intro p hp
    have hcl : p.freeVariables = ∅ := addLawsContext_closed p (by simp [addLawsContext,hp])
    have hmem : p ∈ oneLeContext := by simp [oneLeContext,hp]
    have hm := List.mem_map_of_mem (f := Semiformula.univCl') hmem
    simpa only [Γ,closedContext,Semiformula.univCl'_eq_self_of p hcl] using hm)
  let E := ec.weaken incl
  have az : ND.Proof Θ addZero := by
    apply ND.weaken (ND.replaceByClosures (Γ := oneLeContext)
      (ND.assumption (p := addZero) (by simp [oneLeContext]))) incl
  have h0 : ND.Proof Θ (eq (add zero (succ w)) (succ w)) := by
    have d := ND.allElim _ (succ w) az
    convert d using 1 <;> dsimp [addZero] <;> equalityInstanceSyntax
  have hw : ND.Proof Θ h := ND.assumption (by simp [Θ])
  have he := E.transitivityOf (E.symmetryOf h0) hw
  have hs := ND.weaken (oneLeSuccInstance w) incl
  have ht : ND.Proof Θ (Semiformula.rewAux (Rew.subst ![succ w]) (oneLe (.bvar 0))) := by
    simpa only [oneLe_rew,Rew.subst_bvar,Matrix.cons_val_zero] using hs
  have hout := E.substituteOne (oneLe (.bvar 0)) (succ w) x he ht
  simp only [rew_zero]
  change ND.Proof Θ (Semiformula.rewAux Rew.shift (oneLe a))
  simpa only [oneLe_rew,Rew.subst_bvar,Matrix.cons_val_zero] using hout

def foundationOneLeOfZeroLtProof : ordinaryPAeq.Proof (formula Arithmetic.PeanoMinus.Axiom.oneLeOfZeroLt) := by
  let Γ := closedContext oneLeContext
  have hc := closedContext_closed oneLeContext
  have hp : ND.Proof Γ (Rewriting.emb (formula Arithmetic.PeanoMinus.Axiom.oneLeOfZeroLt)) := by
    apply ND.allIntro
    have h := oneLePositiveInstance (.fvar 0)
    convert h using 1
    · exact shifted_closed Γ hc
    · change Semiformula.rewAux Rew.free (Semiformula.rewAux Rew.emb.q
        (implies (less zero (.bvar 0)) (oneLe (.bvar 0)))) = _
      simp only [rew_implies_any,less_rew,oneLe_rew,rew_zero]
      simp [Rew.q]
  have h := ND.parameterTheoryProof hp (closedContext_mem_theory oneLeContext_mem_theory)
  simpa only [Semiformula.univCl_coe_sentence] using h

#print axioms oneLeSuccCertificate
#print axioms foundationOneLeOfZeroLtProof
end M6.PA.Presentation
