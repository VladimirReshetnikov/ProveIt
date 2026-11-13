module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationAddLaws
@[expose] public section

namespace M6.PA.Presentation
open FFL FFL.FirstOrder

theorem addLawsContext_closed (q : ND.Form) (hq : q ∈ addLawsContext) : q.freeVariables = ∅ := by
  simp only [addLawsContext,List.mem_append] at hq
  rcases hq with hq | hq | hq
  · simp only [equalityContext,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [reflexivity,symmetry,transitivity,succCongruence,addCongruence,mulCongruence,
        implies,eq,add,mul,succ,Semiformula.neg,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ]
  · exact closedContext_closed assocContext q hq
  · exact closedContext_closed commContext q hq

theorem closed_members_shifted {Γ Δ : List ND.Form}
    (hc : ∀ q ∈ Γ,q.freeVariables = ∅) (hi : ∀ q,q ∈ Γ → q ∈ Δ) :
    ∀ q,q ∈ Γ → q ∈ ND.shifted Δ := by
  intro q hq
  have h := List.mem_map_of_mem (f := Semiformula.shift) (hi q hq)
  rw [shift_closed q (hc q hq)] at h
  exact h

def distrProperty : Semiproposition language 1 :=
  eq (mul (.bvar 0) (add (.fvar 0) (.fvar 1)))
    (add (mul (.bvar 0) (.fvar 0)) (mul (.bvar 0) (.fvar 1)))
def distrContext : List ND.Form :=
  addLawsContext ++ [mulZero,mulSucc,addZero,inductionFormula distrProperty]

def distrCertificate : ND.Proof distrContext (.all distrProperty) := by
  let Γ := distrContext
  have incl : ∀ q,q ∈ addLawsContext → q ∈ Γ := by intro q h; simp [Γ,distrContext,h]
  let E := equalityContextPremises.weaken (Δ := Γ)
    (by intro q h; apply incl; simp [addLawsContext,h])
  have mz : ND.Proof Γ mulZero := ND.assumption (by simp [Γ,distrContext])
  have mr : ND.Proof Γ mulSucc := ND.assumption (by simp [Γ,distrContext])
  have az : ND.Proof Γ addZero := ND.assumption (by simp [Γ,distrContext])
  have ind : ND.Proof Γ (inductionFormula distrProperty) := ND.assumption (by simp [Γ,distrContext])
  have base : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![zero]) distrProperty) := by
    let y : GroundTerm := .fvar 0
    let z : GroundTerm := .fvar 1
    have h0 : ND.Proof Γ (eq (mul zero (add y z)) zero) := by
      have h := ND.allElim _ (add y z) mz
      convert h using 1 <;> dsimp [mulZero] <;> equalityInstanceSyntax
    have hy : ND.Proof Γ (eq (mul zero y) zero) := by
      have h := ND.allElim _ y mz
      convert h using 1 <;> dsimp [mulZero] <;> equalityInstanceSyntax
    have hz : ND.Proof Γ (eq (mul zero z) zero) := by
      have h := ND.allElim _ z mz
      convert h using 1 <;> dsimp [mulZero] <;> equalityInstanceSyntax
    have h00 : ND.Proof Γ (eq (add zero zero) zero) := by
      have h := ND.allElim _ zero az
      convert h using 1 <;> dsimp [addZero] <;> equalityInstanceSyntax
    have h := E.transitivityOf h0 (E.symmetryOf (E.transitivityOf (E.additionOf hy hz) h00))
    convert h using 1 <;> dsimp [distrProperty,y,z] <;> equalityInstanceSyntax
  have step : ND.Proof Γ (.all (implies distrProperty
      (Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) distrProperty))) := by
    apply ND.allIntro
    let x : GroundTerm := .fvar 0
    let y : GroundTerm := .fvar 1
    let z : GroundTerm := .fvar 2
    let ES := E.shifted
    let A := derivedAddLaws.weaken (closed_members_shifted addLawsContext_closed incl)
    have mr' := ND.shiftClosed mr (by
      simp [mulSucc,eq,add,mul,succ,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
    have recu (a b : GroundTerm) : ND.Proof (ND.shifted Γ)
        (eq (mul (succ a) b) (add b (mul a b))) := by
      have h := ND.allElim2 _ b a mr'
      convert h using 1 <;> dsimp [mulSucc] <;> equalityInstanceSyntax
    have hs : ND.Proof (ND.shifted Γ)
        (implies (eq (mul x (add y z)) (add (mul x y) (mul x z)))
          (eq (mul (succ x) (add y z)) (add (mul (succ x) y) (mul (succ x) z)))) := by
      apply ND.impIntro
      let p := eq (mul x (add y z)) (add (mul x y) (mul x z))
      have up : ∀ q,q ∈ ND.shifted Γ → q ∈ p :: ND.shifted Γ := fun q h => List.mem_cons_of_mem _ h
      let EP := ES.weaken up
      have ih : ND.Proof (p :: ND.shifted Γ) p := ND.assumption (by simp)
      have h1 := ND.weaken (recu x (add y z)) up
      have h2 := EP.additionOf (EP.reflexive (add y z)) ih
      have h3 := ND.weaken (A.medial ES y z (mul x y) (mul x z)) up
      have h4 := ND.weaken (ES.additionOf (recu x y) (recu x z)) up
      exact EP.transitivityOf (EP.transitivityOf (EP.transitivityOf h1 h2) h3) (EP.symmetryOf h4)
    convert hs using 1 <;> dsimp [distrProperty,x,y,z] <;> equalityInstanceSyntax
  exact ND.mp step (ND.mp base ind)

theorem distrContext_mem_theory (q : ND.Form) (hq : q ∈ distrContext) : q.univCl ∈ ordinaryPAeq := by
  simp only [distrContext,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with hq | rfl | rfl | rfl | rfl
  · exact addLawsContext_mem_theory q hq
  · exact ⟨mulZero,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨mulSucc,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨addZero,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨inductionFormula distrProperty,.induction distrProperty,rfl⟩

def foundationDistrProof : ordinaryPAeq.Proof (formula Arithmetic.PeanoMinus.Axiom.distr) := by
  let Γ := closedContext distrContext
  have hc := closedContext_closed distrContext
  have d := ND.closeIter hc (ND.replaceByClosures distrCertificate) 2
  have hp : ND.Proof Γ (Rewriting.emb (formula Arithmetic.PeanoMinus.Axiom.distr)) := by
    apply ND.allIntro
    apply ND.allIntro
    apply ND.allIntro
    have h := ND.allElim3 _ (.fvar 2) (.fvar 1) (.fvar 0) d
    convert h using 1 <;> (try simp only [shifted_closed Γ hc]) <;>
      dsimp [closureIter,distrProperty,Arithmetic.PeanoMinus.Axiom.distr,formula,atom,term] <;>
      equalityInstanceSyntax
  have h := ND.parameterTheoryProof hp (closedContext_mem_theory distrContext_mem_theory)
  simpa only [Semiformula.univCl_coe_sentence] using h

#print axioms distrCertificate
#print axioms foundationDistrProof
end M6.PA.Presentation
