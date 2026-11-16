module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationRightSucc
@[expose] public section

/-! Third fixed PA-minus image. Right-zero and right-recursion are reused
as actual derived proofs, never silently inserted as target axioms. -/
namespace M6.PA.Presentation
open FFL FFL.FirstOrder

def commProperty : Semiproposition language 1 :=
  eq (add (.bvar 0) (.fvar 0)) (add (.fvar 0) (.bvar 0))
def commContext : List ND.Form :=
  equalityContext ++ (rightZeroContext ++ (closedContext rightSuccContext ++
    [addZero,addSucc,inductionFormula commProperty]))

def commCertificate : ND.Proof commContext (.all commProperty) := by
  let Γ := commContext
  let E := equalityContextPremises.weaken (Δ := Γ) (by intro q hq; simp [Γ,commContext,hq])
  have az : ND.Proof Γ addZero := ND.assumption (by simp [Γ,commContext])
  have ar : ND.Proof Γ addSucc := ND.assumption (by simp [Γ,commContext])
  have ind : ND.Proof Γ (inductionFormula commProperty) := ND.assumption (by simp [Γ,commContext])
  have rz : ND.Proof Γ (.all rightZeroProperty) :=
    ND.weaken rightZeroCertificate (by intro q hq; simp [Γ,commContext,hq])
  have rs : ND.Proof Γ rightSuccFormula :=
    ND.weaken rightSuccClosedCertificate (by intro q hq; simp [Γ,commContext,hq])
  have base : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![zero]) commProperty) := by
    let y : GroundTerm := .fvar 0
    have h1 : ND.Proof Γ (eq (add zero y) y) := by
      have h := ND.allElim _ y az
      convert h using 1 <;> dsimp [addZero,y] <;> equalityInstanceSyntax
    have h2 : ND.Proof Γ (eq (add y zero) y) := by
      have h := ND.allElim _ y rz
      convert h using 1 <;> dsimp [rightZeroProperty,y] <;> equalityInstanceSyntax
    have h := E.transitivityOf h1 (E.symmetryOf h2)
    convert h using 1 <;> dsimp [commProperty,y] <;> equalityInstanceSyntax
  have step : ND.Proof Γ (.all (implies commProperty
      (Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) commProperty))) := by
    apply ND.allIntro
    let x : GroundTerm := .fvar 0
    let y : GroundTerm := .fvar 1
    let ES := E.shifted
    have ar' := ND.shiftClosed ar (by
      simp [addSucc,eq,add,succ,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
    have rs' := ND.shiftClosed rs (by
      simp [rightSuccFormula,eq,add,succ,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
    have h1 : ND.Proof (ND.shifted Γ) (eq (add (succ x) y) (succ (add x y))) := by
      have h := ND.allElim2 _ x y ar'
      convert h using 1 <;> dsimp [addSucc,x,y] <;> equalityInstanceSyntax
    have h3 : ND.Proof (ND.shifted Γ) (eq (add y (succ x)) (succ (add y x))) := by
      have h := ND.allElim2 _ x y rs'
      convert h using 1 <;> dsimp [rightSuccFormula,x,y] <;> equalityInstanceSyntax
    have hs : ND.Proof (ND.shifted Γ)
        (implies (eq (add x y) (add y x)) (eq (add (succ x) y) (add y (succ x)))) := by
      apply ND.impIntro
      let a := eq (add x y) (add y x)
      have up : ∀ q, q ∈ ND.shifted Γ → q ∈ a :: ND.shifted Γ := fun q hq => List.mem_cons_of_mem _ hq
      let E' := ES.weaken up
      have hi : ND.Proof (a :: ND.shifted Γ) a := ND.assumption (by simp)
      have h2 := ND.mp hi (E'.successor (add x y) (add y x))
      exact E'.transitivityOf (E'.transitivityOf (ND.weaken h1 up) h2)
        (E'.symmetryOf (ND.weaken h3 up))
    convert hs using 1 <;> dsimp [commProperty,x,y] <;> equalityInstanceSyntax
  exact ND.mp step (ND.mp base ind)

theorem commContext_mem_theory (q : ND.Form) (hq : q ∈ commContext) : q.univCl ∈ ordinaryPAeq := by
  simp only [commContext,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with hq | hq | hq | rfl | rfl | rfl
  · exact ⟨q,equalityContext_is_PAeq q hq,rfl⟩
  · exact ⟨q,rightZeroContext_is_PAeq q hq,rfl⟩
  · exact closedContext_mem_theory (T := ordinaryPAeq) (fun r hr => ⟨r,rightSuccContext_is_PAeq r hr,rfl⟩) q hq
  · exact ⟨addZero,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨addSucc,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨inductionFormula commProperty,.induction commProperty,rfl⟩

def foundationAddCommProof : ordinaryPAeq.Proof (formula Arithmetic.PeanoMinus.Axiom.addComm) := by
  let Γ := closedContext commContext
  have hc : ∀ q ∈ Γ,q.freeVariables = ∅ := closedContext_closed commContext
  have d := ND.closeIter hc (ND.replaceByClosures commCertificate) 1
  have hp : ND.Proof Γ (Rewriting.emb (formula Arithmetic.PeanoMinus.Axiom.addComm)) := by
    apply ND.allIntro
    apply ND.allIntro
    have h := ND.allElim2 _ (.fvar 1) (.fvar 0) d
    convert h using 1 <;> first
      | (change ND.shifted (ND.shifted Γ) = Γ; rw [shifted_closed Γ hc,shifted_closed Γ hc])
      | (dsimp [closureIter,commProperty,Arithmetic.PeanoMinus.Axiom.addComm,formula,atom,term]; equalityInstanceSyntax)
  have h := ND.parameterTheoryProof hp (closedContext_mem_theory commContext_mem_theory)
  simpa only [Semiformula.univCl_coe_sentence] using h

#print axioms commCertificate
#print axioms foundationAddCommProof
end M6.PA.Presentation
