module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationAddAssoc
@[expose] public section

/-! Derived recursion in the second argument, needed for commutativity.
Both the defining first-argument recursion and the induction context stay explicit. -/
namespace M6.PA.Presentation
open FFL FFL.FirstOrder

theorem closedContext_mem_theory {T : Theory language} {Γ : List ND.Form}
    (ht : ∀ q ∈ Γ,q.univCl ∈ T) : ∀ q ∈ closedContext Γ,q.univCl ∈ T := by
  intro q hq
  rcases List.mem_map.mp hq with ⟨r,hr,rfl⟩
  rw [univCl_idempotent]
  exact ht r hr

def rightSuccProperty : Semiproposition language 1 :=
  eq (add (.bvar 0) (succ (.fvar 0))) (succ (add (.bvar 0) (.fvar 0)))
def rightSuccContext : List ND.Form :=
  equalityContext ++ [addZero,addSucc,inductionFormula rightSuccProperty]
def rightSuccFormula : ND.Form := .all (.all
  (eq (add (.bvar 1) (succ (.bvar 0))) (succ (add (.bvar 1) (.bvar 0)))))

def rightSuccCertificate : ND.Proof rightSuccContext (.all rightSuccProperty) := by
  let Γ := rightSuccContext
  let E := equalityContextPremises.weaken (Δ := Γ) (by intro q hq; simp [Γ,rightSuccContext,hq])
  have az : ND.Proof Γ addZero := ND.assumption (by simp [Γ,rightSuccContext])
  have ar : ND.Proof Γ addSucc := ND.assumption (by simp [Γ,rightSuccContext])
  have ind : ND.Proof Γ (inductionFormula rightSuccProperty) := ND.assumption (by simp [Γ,rightSuccContext])
  have base : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![zero]) rightSuccProperty) := by
    let y : GroundTerm := .fvar 0
    have h1 : ND.Proof Γ (eq (add zero (succ y)) (succ y)) := by
      have h := ND.allElim _ (succ y) az
      convert h using 1 <;> dsimp [addZero,y] <;> equalityInstanceSyntax
    have h2 : ND.Proof Γ (eq (add zero y) y) := by
      have h := ND.allElim _ y az
      convert h using 1 <;> dsimp [addZero,y] <;> equalityInstanceSyntax
    have h := E.transitivityOf h1 (E.symmetryOf (ND.mp h2 (E.successor (add zero y) y)))
    convert h using 1 <;> dsimp [rightSuccProperty,y] <;> equalityInstanceSyntax
  have step : ND.Proof Γ (.all (implies rightSuccProperty
      (Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) rightSuccProperty))) := by
    apply ND.allIntro
    let x : GroundTerm := .fvar 0
    let y : GroundTerm := .fvar 1
    let ES := E.shifted
    have ar' := ND.shiftClosed ar (by
      simp [addSucc,eq,add,succ,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
    have h1 : ND.Proof (ND.shifted Γ) (eq (add (succ x) (succ y)) (succ (add x (succ y)))) := by
      have h := ND.allElim2 _ x (succ y) ar'
      convert h using 1 <;> dsimp [addSucc,x,y] <;> equalityInstanceSyntax
    have h3 : ND.Proof (ND.shifted Γ) (eq (add (succ x) y) (succ (add x y))) := by
      have h := ND.allElim2 _ x y ar'
      convert h using 1 <;> dsimp [addSucc,x,y] <;> equalityInstanceSyntax
    have hs : ND.Proof (ND.shifted Γ)
        (implies (eq (add x (succ y)) (succ (add x y)))
          (eq (add (succ x) (succ y)) (succ (add (succ x) y)))) := by
      apply ND.impIntro
      let a := eq (add x (succ y)) (succ (add x y))
      have up : ∀ q, q ∈ ND.shifted Γ → q ∈ a :: ND.shifted Γ := fun q hq => List.mem_cons_of_mem _ hq
      let E' := ES.weaken up
      have hi : ND.Proof (a :: ND.shifted Γ) a := ND.assumption (by simp)
      have h2 := ND.mp hi (E'.successor (add x (succ y)) (succ (add x y)))
      have h4 := ND.mp (ND.weaken h3 up) (E'.successor (add (succ x) y) (succ (add x y)))
      exact E'.transitivityOf (E'.transitivityOf (ND.weaken h1 up) h2) (E'.symmetryOf h4)
    convert hs using 1 <;> dsimp [rightSuccProperty,x,y] <;> equalityInstanceSyntax
  exact ND.mp step (ND.mp base ind)

theorem rightSuccContext_is_PAeq (q : ND.Form) (hq : q ∈ rightSuccContext) : PAeqAxiom q := by
  simp only [rightSuccContext,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with hq | rfl | rfl | rfl
  · exact equalityContext_is_PAeq q hq
  · exact .fixed _ (by simp [fixedAxioms])
  · exact .fixed _ (by simp [fixedAxioms])
  · exact .induction rightSuccProperty

def rightSuccClosedCertificate : ND.Proof (closedContext rightSuccContext) rightSuccFormula := by
  let Γ := closedContext rightSuccContext
  have hc : ∀ q ∈ Γ,q.freeVariables = ∅ := closedContext_closed rightSuccContext
  have d := ND.closeIter hc (ND.replaceByClosures rightSuccCertificate) 1
  apply ND.allIntro
  apply ND.allIntro
  have h := ND.allElim2 _ (.fvar 1) (.fvar 0) d
  convert h using 1
  · change ND.shifted (ND.shifted Γ) = Γ
    rw [shifted_closed Γ hc,shifted_closed Γ hc]
  · dsimp [closureIter,rightSuccProperty,rightSuccFormula]
    equalityInstanceSyntax

#print axioms rightSuccClosedCertificate
end M6.PA.Presentation
