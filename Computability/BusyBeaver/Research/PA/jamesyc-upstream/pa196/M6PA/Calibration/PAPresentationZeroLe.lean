module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationOrderBasic
@[expose] public section

namespace M6.PA.Presentation
open FFL FFL.FirstOrder

def zeroLeProperty : Semiproposition language 1 := .or (eq zero (.bvar 0)) (less zero (.bvar 0))
theorem zeroLeProperty_rew {m : Nat} (ω : Rew language Nat 1 Nat m) :
    Semiformula.rewAux ω zeroLeProperty = .or (eq zero (ω (.bvar 0))) (less zero (ω (.bvar 0))) := by
  change Semiformula.or (Semiformula.rewAux ω (eq zero (.bvar 0)))
    (Semiformula.rewAux ω (less zero (.bvar 0))) = _
  rw [eq_rew,less_rew,rew_zero]

def zeroLeContext : List ND.Form := equalityContext ++ [addZero,inductionFormula zeroLeProperty]

def zeroLeCertificate : ND.Proof zeroLeContext (.all zeroLeProperty) := by
  let Γ := zeroLeContext
  let E := equalityContextPremises.weaken (Δ := Γ) (by intro q h; simp [Γ,zeroLeContext,h])
  have az : ND.Proof Γ addZero := ND.assumption (by simp [Γ,zeroLeContext])
  have ind : ND.Proof Γ (inductionFormula zeroLeProperty) := ND.assumption (by simp [Γ,zeroLeContext])
  have base : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![zero]) zeroLeProperty) := by
    change ND.Proof Γ (.or _ _)
    apply ND.orLeft
    convert E.reflexive zero using 1 <;> dsimp [zeroLeProperty] <;> equalityInstanceSyntax
  have step : ND.Proof Γ (.all (implies zeroLeProperty
      (Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) zeroLeProperty))) := by
    apply ND.allIntro
    let x : GroundTerm := .fvar 0
    have az' := ND.shiftClosed az (by
      simp [addZero,eq,add,zero,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
    have h : ND.Proof (ND.shifted Γ) (eq (add zero (succ x)) (succ x)) := by
      have d := ND.allElim _ (succ x) az'
      convert d using 1 <;> dsimp [addZero] <;> equalityInstanceSyntax
    have hp : ND.Proof (ND.shifted Γ) (.or (eq zero (succ x)) (less zero (succ x))) :=
      ND.orRight (ND.lessIntro zero (succ x) x h)
    have hs : ND.Proof (ND.shifted Γ) (implies zeroLeProperty.free
        (.or (eq zero (succ x)) (less zero (succ x)))) := by
      apply ND.impIntro
      exact ND.weaken hp (fun q hq => List.mem_cons_of_mem _ hq)
    change ND.Proof (ND.shifted Γ) (inductionStep zeroLeProperty (succ (.bvar 0))).free
    rw [free_inductionStep]
    have he : Semiformula.rewAux (Rew.subst ![Rew.free (succ (.bvar 0))]) zeroLeProperty.shift =
        .or (eq zero (succ x)) (less zero (succ x)) := by
      change Semiformula.rewAux (Rew.subst ![Rew.free (succ (.bvar 0))])
        (Semiformula.rewAux Rew.shift zeroLeProperty) = _
      rw [rewrite_compose,zeroLeProperty_rew]
      simp [Rew.comp_app,rew_succ,Rew.shift_bvar,Rew.subst_bvar,x]
    rw [he]
    exact hs
  exact ND.mp step (ND.mp base ind)

theorem zeroLeContext_is_PAeq (q : ND.Form) (hq : q ∈ zeroLeContext) : PAeqAxiom q := by
  simp only [zeroLeContext,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with hq | rfl | rfl
  · exact equalityContext_is_PAeq q hq
  · exact .fixed _ (by simp [fixedAxioms])
  · exact .induction zeroLeProperty

def foundationZeroLeProof : ordinaryPAeq.Proof (formula Arithmetic.PeanoMinus.Axiom.zeroLe) := by
  have d := ND.parameterTheoryProof zeroLeCertificate (T := ordinaryPAeq)
    (fun q hq => ⟨q,zeroLeContext_is_PAeq q hq,rfl⟩)
  have he : formula Arithmetic.PeanoMinus.Axiom.zeroLe = (Semiformula.all zeroLeProperty).univCl := by
    apply (Semiformula.coe_inj _ _).mp
    rw [Semiformula.coe_univCl_eq_univCl']
    rw [Semiformula.univCl'_eq_self_of _ (by
      simp [zeroLeProperty,less,eq,add,zero,succ,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])]
    change Semiformula.rewAux Rew.emb (formula Arithmetic.PeanoMinus.Axiom.zeroLe) = _
    rw [←formula_emb]
    rfl
  rw [he]
  exact d

#print axioms zeroLeCertificate
#print axioms foundationZeroLeProof
end M6.PA.Presentation
