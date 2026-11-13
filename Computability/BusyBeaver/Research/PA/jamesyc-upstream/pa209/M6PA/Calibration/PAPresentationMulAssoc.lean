module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationMulComm
@[expose] public section

namespace M6.PA.Presentation
open FFL FFL.FirstOrder

def mulAssocProperty : Semiproposition language 1 :=
  eq (mul (mul (.bvar 0) (.fvar 0)) (.fvar 1))
    (mul (.bvar 0) (mul (.fvar 0) (.fvar 1)))
def mulAssocContext : List ND.Form := mulLawsContext ++
  (closedContext mulCommContext ++ [mulZero,mulSucc,inductionFormula mulAssocProperty])

def mulAssocCertificate : ND.Proof mulAssocContext (.all mulAssocProperty) := by
  let Γ := mulAssocContext
  have incl : ∀ q,q ∈ mulLawsContext → q ∈ Γ := by intro q h; simp [Γ,mulAssocContext,h]
  have ic : ∀ q,q ∈ closedContext mulCommContext → q ∈ Γ := by intro q h; simp [Γ,mulAssocContext,h]
  let E := equalityContextPremises.weaken (Δ := Γ)
    (by intro q h; apply incl; simp [mulLawsContext,addLawsContext,h])
  have mz : ND.Proof Γ mulZero := ND.assumption (by simp [Γ,mulAssocContext])
  have mr : ND.Proof Γ mulSucc := ND.assumption (by simp [Γ,mulAssocContext])
  have ind : ND.Proof Γ (inductionFormula mulAssocProperty) := ND.assumption (by simp [Γ,mulAssocContext])
  have base : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![zero]) mulAssocProperty) := by
    let y : GroundTerm := .fvar 0
    let z : GroundTerm := .fvar 1
    have h0 (a : GroundTerm) : ND.Proof Γ (eq (mul zero a) zero) := by
      have h := ND.allElim _ a mz
      convert h using 1 <;> dsimp [mulZero] <;> equalityInstanceSyntax
    have h1 := E.multiplicationOf (h0 y) (E.reflexive z)
    have h := E.transitivityOf (E.transitivityOf h1 (h0 z)) (E.symmetryOf (h0 (mul y z)))
    convert h using 1 <;> dsimp [mulAssocProperty,y,z] <;> equalityInstanceSyntax
  have step : ND.Proof Γ (.all (implies mulAssocProperty
      (Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) mulAssocProperty))) := by
    apply ND.allIntro
    let x : GroundTerm := .fvar 0
    let y : GroundTerm := .fvar 1
    let z : GroundTerm := .fvar 2
    let ES := E.shifted
    let MS := derivedMulLaws.weaken (closed_members_shifted mulLawsContext_closed incl)
    have comm (a b : GroundTerm) : ND.Proof (ND.shifted Γ) (eq (mul a b) (mul b a)) :=
      ND.weaken (mulCommInstance a b) (closed_members_shifted (closedContext_closed mulCommContext) ic)
    have leftDistr (a b c : GroundTerm) : ND.Proof (ND.shifted Γ)
        (eq (mul (add a b) c) (add (mul a c) (mul b c))) := by
      exact ES.transitivityOf (ES.transitivityOf (comm (add a b) c) (MS.distr c a b))
        (ES.additionOf (comm c a) (comm c b))
    have mr' := ND.shiftClosed mr (by
      simp [mulSucc,eq,add,mul,succ,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
    have recu (a b : GroundTerm) : ND.Proof (ND.shifted Γ)
        (eq (mul (succ a) b) (add b (mul a b))) := by
      have h := ND.allElim2 _ b a mr'
      convert h using 1 <;> dsimp [mulSucc] <;> equalityInstanceSyntax
    have hs : ND.Proof (ND.shifted Γ)
        (implies (eq (mul (mul x y) z) (mul x (mul y z)))
          (eq (mul (mul (succ x) y) z) (mul (succ x) (mul y z)))) := by
      apply ND.impIntro
      let p := eq (mul (mul x y) z) (mul x (mul y z))
      have up : ∀ q,q ∈ ND.shifted Γ → q ∈ p :: ND.shifted Γ := fun q h => List.mem_cons_of_mem _ h
      let EP := ES.weaken up
      have ih : ND.Proof (p :: ND.shifted Γ) p := ND.assumption (by simp)
      have h1 := ND.weaken (ES.multiplicationOf (recu x y) (ES.reflexive z)) up
      have h2 := ND.weaken (leftDistr y (mul x y) z) up
      have h3 := EP.additionOf (EP.reflexive (mul y z)) ih
      have h4 := ND.weaken (recu x (mul y z)) up
      exact EP.transitivityOf (EP.transitivityOf (EP.transitivityOf h1 h2) h3) (EP.symmetryOf h4)
    convert hs using 1 <;> dsimp [mulAssocProperty,x,y,z] <;> equalityInstanceSyntax
  exact ND.mp step (ND.mp base ind)

theorem mulAssocContext_mem_theory (q : ND.Form) (hq : q ∈ mulAssocContext) : q.univCl ∈ ordinaryPAeq := by
  simp only [mulAssocContext,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with hq | hq | rfl | rfl | rfl
  · exact mulLawsContext_mem_theory q hq
  · exact closedContext_mem_theory mulCommContext_mem_theory q hq
  · exact ⟨mulZero,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨mulSucc,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨inductionFormula mulAssocProperty,.induction mulAssocProperty,rfl⟩

def foundationMulAssocProof : ordinaryPAeq.Proof (formula Arithmetic.PeanoMinus.Axiom.mulAssoc) := by
  let Γ := closedContext mulAssocContext
  have hc := closedContext_closed mulAssocContext
  have d := ND.closeIter hc (ND.replaceByClosures mulAssocCertificate) 2
  have hp : ND.Proof Γ (Rewriting.emb (formula Arithmetic.PeanoMinus.Axiom.mulAssoc)) := by
    apply ND.allIntro
    apply ND.allIntro
    apply ND.allIntro
    have h := ND.allElim3 _ (.fvar 2) (.fvar 1) (.fvar 0) d
    convert h using 1 <;> (try simp only [shifted_closed Γ hc]) <;>
      dsimp [closureIter,mulAssocProperty,Arithmetic.PeanoMinus.Axiom.mulAssoc,formula,atom,term] <;>
      equalityInstanceSyntax
  have h := ND.parameterTheoryProof hp (closedContext_mem_theory mulAssocContext_mem_theory)
  simpa only [Semiformula.univCl_coe_sentence] using h

#print axioms mulAssocCertificate
#print axioms foundationMulAssocProof
end M6.PA.Presentation
