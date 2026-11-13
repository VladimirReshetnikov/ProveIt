module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationAddDifference
@[expose] public section

namespace M6.PA.Presentation
open FFL FFL.FirstOrder

def ND.negIntro {Γ : List ND.Form} {p : ND.Form} (d : ND.Proof (p :: Γ) .falsum) :
    ND.Proof Γ p.neg := by
  apply ND.byContradiction
  change ND.Proof (p.neg.neg :: Γ) .falsum
  rw [Semiformula.neg_neg]
  exact d

theorem rew_neg_direct {ξ ζ : Type} {n m : Nat} (ω : Rew language ξ n ζ m)
    (p : Semiformula language ξ n) :
    Semiformula.rewAux ω p.neg = (Semiformula.rewAux ω p).neg := Semiformula.rewAux_neg ω p

def noLoop {ξ : Type} {n : Nat} (a : Semiterm language ξ n) : Semiformula language ξ n :=
  .all ((eq (add (Rew.bShift a) (succ (.bvar 0))) (Rew.bShift a)).neg)
theorem noLoop_rew {ξ ζ : Type} {n m : Nat} (ω : Rew language ξ n ζ m) (a : Semiterm language ξ n) :
    Semiformula.rewAux ω (noLoop a) = noLoop (ω a) := by
  simp only [noLoop,Semiformula.rewAux,rew_neg_direct,eq_rew,rew_add,rew_succ,
    Rew.q_comp_bShift_app,Rew.q_bvar_zero]
  rfl

def noLoopProperty : Semiproposition language 1 := noLoop (.bvar 0)
def noLoopContext : List ND.Form := equalityContext ++
  [addZero,addSucc,zeroNotSucc,succInjective,inductionFormula noLoopProperty]

def noLoopCertificate : ND.Proof noLoopContext (.all noLoopProperty) := by
  let Γ := noLoopContext
  let E := equalityContextPremises.weaken (Δ := Γ) (by intro p hp; simp [Γ,noLoopContext,hp])
  have az : ND.Proof Γ addZero := ND.assumption (by simp [Γ,noLoopContext])
  have ar : ND.Proof Γ addSucc := ND.assumption (by simp [Γ,noLoopContext])
  have nz : ND.Proof Γ zeroNotSucc := ND.assumption (by simp [Γ,noLoopContext])
  have si : ND.Proof Γ succInjective := ND.assumption (by simp [Γ,noLoopContext])
  have ind : ND.Proof Γ (inductionFormula noLoopProperty) := ND.assumption (by simp [Γ,noLoopContext])
  have base : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![zero]) noLoopProperty) := by
    rw [noLoopProperty,noLoop_rew,Rew.subst_bvar]
    change ND.Proof Γ (noLoop zero)
    apply ND.allIntro
    let y : GroundTerm := .fvar 0
    let ES := E.shifted
    have az' := ND.shiftClosed az (by
      simp [addZero,eq,add,zero,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
    have nz' := ND.shiftClosed nz (by
      simp [zeroNotSucc,eq,zero,succ,Semiformula.neg,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
    have hz : ND.Proof (ND.shifted Γ) (eq (add zero (succ y)) (succ y)) := by
      have d := ND.allElim _ (succ y) az'
      convert d using 1 <;> dsimp [addZero] <;> equalityInstanceSyntax
    have hn : ND.Proof (ND.shifted Γ) (eq zero (succ y)).neg := by
      have d := ND.allElim _ y nz'
      convert d using 1 <;> dsimp [zeroNotSucc] <;> equalityInstanceSyntax
    have hp : ND.Proof (ND.shifted Γ) (eq (add zero (succ y)) zero).neg := by
      apply ND.negIntro
      let p := eq (add zero (succ y)) zero
      have up : ∀ q,q ∈ ND.shifted Γ → q ∈ p :: ND.shifted Γ := fun q h => List.mem_cons_of_mem _ h
      let EP := ES.weaken up
      have he : ND.Proof (p :: ND.shifted Γ) p := ND.assumption (by simp)
      exact ND.contradiction (EP.transitivityOf (EP.symmetryOf he) (ND.weaken hz up)) (ND.weaken hn up)
    convert hp using 1 <;> dsimp [noLoop,y] <;> equalityInstanceSyntax
  have step : ND.Proof Γ (.all (inductionStep noLoopProperty (succ (.bvar 0)))) := by
    apply ND.allIntro
    let x : GroundTerm := .fvar 0
    have hs : ND.Proof (ND.shifted Γ) (implies (noLoop x) (noLoop (succ x))) := by
      apply ND.impIntro
      let Δ := noLoop x :: ND.shifted Γ
      have ih : ND.Proof Δ (noLoop x) := ND.assumption (by simp [Δ])
      apply ND.allIntro
      let y : GroundTerm := .fvar 0
      let x' := Rew.shift x
      let Θ := ND.shifted Δ
      have up : ∀ q,q ∈ ND.shifted Γ → q ∈ Δ := fun q h => List.mem_cons_of_mem _ h
      let ET := (E.shifted.weaken up).shifted
      have ar' := ND.shiftClosed ar (by
        simp [addSucc,eq,add,succ,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
      have ar'' := ND.shiftClosed (ND.weaken ar' up) (by
        simp [addSucc,eq,add,succ,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
      have si' := ND.shiftClosed si (by
        simp [succInjective,implies,eq,succ,Semiformula.neg,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
      have si'' := ND.shiftClosed (ND.weaken si' up) (by
        simp [succInjective,implies,eq,succ,Semiformula.neg,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
      have nih : ND.Proof Θ (noLoop x') := by
        have d := ND.shiftProof ih
        change ND.Proof _ (Semiformula.rewAux Rew.shift (noLoop x)) at d
        simpa only [noLoop_rew] using d
      have hn : ND.Proof Θ (eq (add x' (succ y)) x').neg := by
        have d := ND.allElim _ y nih
        change ND.Proof _ (Semiformula.rewAux (Rew.subst ![y]) _) at d
        simpa only [noLoop,rew_neg_direct,eq_rew,rew_add,rew_succ,
          Rew.subst_bShift_app,Rew.subst_bvar,Matrix.cons_val_zero] using d
      have ha : ND.Proof Θ (eq (add (succ x') (succ y)) (succ (add x' (succ y)))) := by
        have d := ND.allElim2 _ x' (succ y) ar''
        convert d using 1 <;> dsimp [addSucc] <;> equalityInstanceSyntax
      have inj : ND.Proof Θ (implies (eq (succ (add x' (succ y))) (succ x')) (eq (add x' (succ y)) x')) := by
        have d := ND.allElim2 _ x' (add x' (succ y)) si''
        convert d using 1 <;> dsimp [succInjective] <;> equalityInstanceSyntax
      have hp : ND.Proof Θ (eq (add (succ x') (succ y)) (succ x')).neg := by
        apply ND.negIntro
        let p := eq (add (succ x') (succ y)) (succ x')
        have up2 : ∀ q,q ∈ Θ → q ∈ p :: Θ := fun q h => List.mem_cons_of_mem _ h
        let EP := ET.weaken up2
        have he : ND.Proof (p :: Θ) p := ND.assumption (by simp)
        have hsucc := EP.transitivityOf (EP.symmetryOf (ND.weaken ha up2)) he
        exact ND.contradiction (ND.mp hsucc (ND.weaken inj up2)) (ND.weaken hn up2)
      change ND.Proof Θ (Semiformula.rewAux Rew.free
        ((eq (add (Rew.bShift (succ x)) (succ (.bvar 0))) (Rew.bShift (succ x))).neg))
      simpa only [rew_neg_direct,eq_rew,rew_add,rew_succ,Rew.free_bShift_app,
        Rew.free_bvar_last_zero] using hp
    rw [free_inductionStep]
    convert hs using 1
    change implies (Semiformula.rewAux Rew.free (noLoop (.bvar 0)))
      (Semiformula.rewAux (Rew.subst ![Rew.free (succ (.bvar 0))])
        (Semiformula.rewAux Rew.shift (noLoop (.bvar 0)))) = _
    simp [noLoop_rew,rew_succ,Rew.shift_bvar,Rew.subst_bvar,x]
  exact ND.mp step (ND.mp base ind)

theorem noLoopContext_mem_theory (q : ND.Form) (hq : q ∈ noLoopContext) : q.univCl ∈ ordinaryPAeq := by
  simp only [noLoopContext,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with hq | rfl | rfl | rfl | rfl | rfl
  · exact ⟨q,equalityContext_is_PAeq q hq,rfl⟩
  · exact ⟨addZero,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨addSucc,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨zeroNotSucc,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨succInjective,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨inductionFormula noLoopProperty,.induction noLoopProperty,rfl⟩

def ltIrreflInstance (a : GroundTerm) : ND.Proof (closedContext noLoopContext) (less a a).neg := by
  have d := ND.allElim _ a (ND.replaceByClosures noLoopCertificate)
  change ND.Proof _ (Semiformula.rewAux (Rew.subst ![a]) noLoopProperty) at d
  change ND.Proof (closedContext noLoopContext) (noLoop a)
  simpa only [noLoopProperty,noLoop_rew,Rew.subst_bvar,Matrix.cons_val_zero] using d

def foundationLtIrreflProof : ordinaryPAeq.Proof (formula Arithmetic.PeanoMinus.Axiom.ltIrrefl) := by
  let Γ := closedContext noLoopContext
  have hc := closedContext_closed noLoopContext
  have hp : ND.Proof Γ (Rewriting.emb (formula Arithmetic.PeanoMinus.Axiom.ltIrrefl)) := by
    apply ND.allIntro
    have h := ltIrreflInstance (.fvar 0)
    convert h using 1
    · exact shifted_closed Γ hc
    · change Semiformula.rewAux Rew.free (Semiformula.rewAux Rew.emb.q ((less (.bvar 0) (.bvar 0)).neg)) = _
      simp only [rew_neg_direct,less_rew]
      simp [Rew.q]
  have d := ND.parameterTheoryProof hp (closedContext_mem_theory noLoopContext_mem_theory)
  simpa only [Semiformula.univCl_coe_sentence] using d

#print axioms noLoopCertificate
#print axioms foundationLtIrreflProof
end M6.PA.Presentation
