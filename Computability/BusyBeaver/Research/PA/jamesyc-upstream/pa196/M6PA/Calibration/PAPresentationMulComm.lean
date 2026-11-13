module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationMulLaws
@[expose] public section

namespace M6.PA.Presentation
open FFL FFL.FirstOrder

def mulCommProperty : Semiproposition language 1 :=
  eq (mul (.bvar 0) (.fvar 0)) (mul (.fvar 0) (.bvar 0))
def mulCommContext : List ND.Form :=
  mulLawsContext ++ [mulZero,mulSucc,inductionFormula mulCommProperty]

def mulCommCertificate : ND.Proof mulCommContext (.all mulCommProperty) := by
  let Γ := mulCommContext
  have incl : ∀ q,q ∈ mulLawsContext → q ∈ Γ := by intro q h; simp [Γ,mulCommContext,h]
  let E := equalityContextPremises.weaken (Δ := Γ)
    (by intro q h; apply incl; simp [mulLawsContext,addLawsContext,h])
  let M := derivedMulLaws.weaken incl
  have mz : ND.Proof Γ mulZero := ND.assumption (by simp [Γ,mulCommContext])
  have mr : ND.Proof Γ mulSucc := ND.assumption (by simp [Γ,mulCommContext])
  have ind : ND.Proof Γ (inductionFormula mulCommProperty) := ND.assumption (by simp [Γ,mulCommContext])
  have base : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![zero]) mulCommProperty) := by
    let y : GroundTerm := .fvar 0
    have h0 : ND.Proof Γ (eq (mul zero y) zero) := by
      have h := ND.allElim _ y mz
      convert h using 1 <;> dsimp [mulZero] <;> equalityInstanceSyntax
    have h := E.transitivityOf h0 (E.symmetryOf (M.zero y))
    convert h using 1 <;> dsimp [mulCommProperty,y] <;> equalityInstanceSyntax
  have step : ND.Proof Γ (.all (implies mulCommProperty
      (Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) mulCommProperty))) := by
    apply ND.allIntro
    let x : GroundTerm := .fvar 0
    let y : GroundTerm := .fvar 1
    let ES := E.shifted
    let MS := derivedMulLaws.weaken (closed_members_shifted mulLawsContext_closed incl)
    have mr' := ND.shiftClosed mr (by
      simp [mulSucc,eq,add,mul,succ,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
    have h1 : ND.Proof (ND.shifted Γ) (eq (mul (succ x) y) (add y (mul x y))) := by
      have h := ND.allElim2 _ y x mr'
      convert h using 1 <;> dsimp [mulSucc] <;> equalityInstanceSyntax
    have hs : ND.Proof (ND.shifted Γ)
        (implies (eq (mul x y) (mul y x)) (eq (mul (succ x) y) (mul y (succ x)))) := by
      apply ND.impIntro
      let p := eq (mul x y) (mul y x)
      have up : ∀ q,q ∈ ND.shifted Γ → q ∈ p :: ND.shifted Γ := fun q h => List.mem_cons_of_mem _ h
      let EP := ES.weaken up
      have ih : ND.Proof (p :: ND.shifted Γ) p := ND.assumption (by simp)
      have h2 := EP.additionOf (EP.reflexive y) ih
      exact EP.transitivityOf (EP.transitivityOf (ND.weaken h1 up) h2)
        (EP.symmetryOf (ND.weaken (MS.rightSucc y x) up))
    convert hs using 1 <;> dsimp [mulCommProperty,x,y] <;> equalityInstanceSyntax
  exact ND.mp step (ND.mp base ind)

theorem mulCommContext_mem_theory (q : ND.Form) (hq : q ∈ mulCommContext) : q.univCl ∈ ordinaryPAeq := by
  simp only [mulCommContext,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with hq | rfl | rfl | rfl
  · exact mulLawsContext_mem_theory q hq
  · exact ⟨mulZero,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨mulSucc,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨inductionFormula mulCommProperty,.induction mulCommProperty,rfl⟩

def mulCommInstance (a b : GroundTerm) : ND.Proof (closedContext mulCommContext)
    (eq (mul a b) (mul b a)) := by
  have d := ND.closeIter (closedContext_closed mulCommContext)
    (ND.replaceByClosures mulCommCertificate) 1
  have h := ND.allElim2 _ a b d
  convert h using 1 <;> dsimp [closureIter,mulCommProperty] <;> equalityInstanceSyntax

def foundationMulCommProof : ordinaryPAeq.Proof (formula Arithmetic.PeanoMinus.Axiom.mulComm) := by
  let Γ := closedContext mulCommContext
  have hc := closedContext_closed mulCommContext
  have hp : ND.Proof Γ (Rewriting.emb (formula Arithmetic.PeanoMinus.Axiom.mulComm)) := by
    apply ND.allIntro
    apply ND.allIntro
    have h := mulCommInstance (.fvar 1) (.fvar 0)
    convert h using 1 <;> first
      | (change ND.shifted (ND.shifted Γ) = Γ; rw [shifted_closed Γ hc,shifted_closed Γ hc])
      | (dsimp [Arithmetic.PeanoMinus.Axiom.mulComm,formula,atom,term]; equalityInstanceSyntax)
  have h := ND.parameterTheoryProof hp (closedContext_mem_theory mulCommContext_mem_theory)
  simpa only [Semiformula.univCl_coe_sentence] using h

#print axioms mulCommCertificate
#print axioms foundationMulCommProof
end M6.PA.Presentation
