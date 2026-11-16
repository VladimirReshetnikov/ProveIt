module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationAddZero
@[expose] public section

/-! A second fixed image: associativity of addition. The induction variable
is the first argument; two arbitrary parameters are closed and the final
three quantifiers are explicitly instantiated in Foundation's exact order. -/
namespace M6.PA.Presentation
open FFL FFL.FirstOrder

def assocProperty : Semiproposition language 1 :=
  eq (add (add (.bvar 0) (.fvar 0)) (.fvar 1))
    (add (.bvar 0) (add (.fvar 0) (.fvar 1)))
def assocContext : List ND.Form :=
  equalityContext ++ [addZero,addSucc,inductionFormula assocProperty]

def assocCertificate : ND.Proof assocContext (.all assocProperty) := by
  let Γ := assocContext
  let E := equalityContextPremises.weaken (Δ := Γ) (by intro q hq; simp [Γ,assocContext,hq])
  have az : ND.Proof Γ addZero := ND.assumption (by simp [Γ,assocContext])
  have ar : ND.Proof Γ addSucc := ND.assumption (by simp [Γ,assocContext])
  have ind : ND.Proof Γ (inductionFormula assocProperty) := ND.assumption (by simp [Γ,assocContext])
  have base : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![zero]) assocProperty) := by
    let y : GroundTerm := .fvar 0
    let z : GroundTerm := .fvar 1
    have hz : ND.Proof Γ (eq (add zero y) y) := by
      have h := ND.allElim _ y az
      convert h using 1 <;> dsimp [addZero,y] <;> equalityInstanceSyntax
    have ha : ND.Proof Γ (eq (add (add zero y) z) (add y z)) :=
      ND.mp (E.reflexive z) (ND.mp hz (E.addition (add zero y) y z z))
    have hb : ND.Proof Γ (eq (add zero (add y z)) (add y z)) := by
      have h := ND.allElim _ (add y z) az
      convert h using 1 <;> dsimp [addZero,y,z] <;> equalityInstanceSyntax
    have h := E.transitivityOf ha (E.symmetryOf hb)
    convert h using 1 <;> dsimp [assocProperty,y,z] <;> equalityInstanceSyntax
  have step : ND.Proof Γ (.all (implies assocProperty
      (Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) assocProperty))) := by
    apply ND.allIntro
    let x : GroundTerm := .fvar 0
    let y : GroundTerm := .fvar 1
    let z : GroundTerm := .fvar 2
    let ES := E.shifted
    have ar' := ND.shiftClosed ar (by
      simp [addSucc,eq,add,succ,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
    have hxy : ND.Proof (ND.shifted Γ) (eq (add (succ x) y) (succ (add x y))) := by
      have h := ND.allElim2 _ x y ar'
      convert h using 1 <;> dsimp [addSucc,x,y] <;> equalityInstanceSyntax
    have h1 : ND.Proof (ND.shifted Γ)
        (eq (add (add (succ x) y) z) (add (succ (add x y)) z)) :=
      ND.mp (ES.reflexive z) (ND.mp hxy (ES.addition (add (succ x) y) (succ (add x y)) z z))
    have h2 : ND.Proof (ND.shifted Γ)
        (eq (add (succ (add x y)) z) (succ (add (add x y) z))) := by
      have h := ND.allElim2 _ (add x y) z ar'
      convert h using 1 <;> dsimp [addSucc,x,y,z] <;> equalityInstanceSyntax
    have h4 : ND.Proof (ND.shifted Γ)
        (eq (add (succ x) (add y z)) (succ (add x (add y z)))) := by
      have h := ND.allElim2 _ x (add y z) ar'
      convert h using 1 <;> dsimp [addSucc,x,y,z] <;> equalityInstanceSyntax
    have hs : ND.Proof (ND.shifted Γ)
        (implies (eq (add (add x y) z) (add x (add y z)))
          (eq (add (add (succ x) y) z) (add (succ x) (add y z)))) := by
      apply ND.impIntro
      let a := eq (add (add x y) z) (add x (add y z))
      have up : ∀ q, q ∈ ND.shifted Γ → q ∈ a :: ND.shifted Γ := fun q hq => List.mem_cons_of_mem _ hq
      let E' := ES.weaken up
      have hi : ND.Proof (a :: ND.shifted Γ) a := ND.assumption (by simp)
      have h3 := ND.mp hi (E'.successor (add (add x y) z) (add x (add y z)))
      exact E'.transitivityOf (E'.transitivityOf (E'.transitivityOf (ND.weaken h1 up)
        (ND.weaken h2 up)) h3) (E'.symmetryOf (ND.weaken h4 up))
    convert hs using 1 <;> dsimp [assocProperty,x,y,z] <;> equalityInstanceSyntax
  exact ND.mp step (ND.mp base ind)

theorem assocContext_is_PAeq (q : ND.Form) (hq : q ∈ assocContext) : PAeqAxiom q := by
  simp only [assocContext,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with hq | rfl | rfl | rfl
  · exact equalityContext_is_PAeq q hq
  · exact .fixed _ (by simp [fixedAxioms])
  · exact .fixed _ (by simp [fixedAxioms])
  · exact .induction assocProperty

def foundationAddAssocProof : ordinaryPAeq.Proof (formula Arithmetic.PeanoMinus.Axiom.addAssoc) := by
  let Γ := closedContext assocContext
  have hc : ∀ q ∈ Γ,q.freeVariables = ∅ := closedContext_closed assocContext
  have d := ND.closeIter hc (ND.replaceByClosures assocCertificate) 2
  have hp : ND.Proof Γ (Rewriting.emb (formula Arithmetic.PeanoMinus.Axiom.addAssoc)) := by
    apply ND.allIntro
    apply ND.allIntro
    apply ND.allIntro
    have h := ND.allElim3 _ (.fvar 2) (.fvar 1) (.fvar 0) d
    convert h using 1 <;>
      (try simp only [shifted_closed Γ hc]) <;>
      dsimp [closureIter,assocProperty,Arithmetic.PeanoMinus.Axiom.addAssoc,formula,atom,term] <;>
      equalityInstanceSyntax
  have ht : ∀ q ∈ Γ,q.univCl ∈ ordinaryPAeq := by
    intro q hq
    rcases List.mem_map.mp hq with ⟨r,hr,rfl⟩
    rw [univCl_idempotent]
    exact ⟨r,assocContext_is_PAeq r hr,rfl⟩
  have h := ND.parameterTheoryProof hp ht
  simpa only [Semiformula.univCl_coe_sentence] using h

#print axioms assocCertificate
#print axioms foundationAddAssocProof
end M6.PA.Presentation
