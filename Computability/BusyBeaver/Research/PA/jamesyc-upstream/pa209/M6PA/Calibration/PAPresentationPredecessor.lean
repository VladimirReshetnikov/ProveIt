module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationMulLtMul
@[expose] public section

namespace M6.PA.Presentation
open FFL FFL.FirstOrder

def predecessor {ξ : Type} {n : Nat} (a : Semiterm language ξ n) : Semiformula language ξ n :=
  .or (eq a zero) (.exs (eq (Rew.bShift a) (succ (.bvar 0))))
theorem predecessor_rew {ξ ζ : Type} {n m : Nat} (ω : Rew language ξ n ζ m) (a : Semiterm language ξ n) :
    Semiformula.rewAux ω (predecessor a) = predecessor (ω a) := by
  simp only [predecessor,Semiformula.rewAux,eq_rew,rew_succ,rew_zero,
    Rew.q_comp_bShift_app,Rew.q_bvar_zero]
  rfl

def predecessorProperty : Semiproposition language 1 := predecessor (.bvar 0)
def predecessorContext : List ND.Form := equalityContext ++ [inductionFormula predecessorProperty]

def predecessorCertificate : ND.Proof predecessorContext (.all predecessorProperty) := by
  let Γ := predecessorContext
  let E := equalityContextPremises.weaken (Δ := Γ) (by intro p hp; simp [Γ,predecessorContext,hp])
  have ind : ND.Proof Γ (inductionFormula predecessorProperty) := ND.assumption (by simp [Γ,predecessorContext])
  have base : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![zero]) predecessorProperty) := by
    rw [predecessorProperty,predecessor_rew,Rew.subst_bvar]
    exact ND.orLeft (E.reflexive zero)
  have step : ND.Proof Γ (.all (inductionStep predecessorProperty (succ (.bvar 0)))) := by
    apply ND.allIntro
    let x : GroundTerm := .fvar 0
    have hp : ND.Proof (ND.shifted Γ) (predecessor (succ x)) := by
      apply ND.orRight
      apply ND.exsIntro _ x
      change ND.Proof _ (Semiformula.rewAux (Rew.subst ![x]) _)
      simpa only [eq_rew,rew_succ,Rew.subst_bShift_app,Rew.subst_bvar,Matrix.cons_val_zero]
        using E.shifted.reflexive (succ x)
    have hs : ND.Proof (ND.shifted Γ) (implies predecessorProperty.free (predecessor (succ x))) := by
      apply ND.impIntro
      exact ND.weaken hp (fun p hp => List.mem_cons_of_mem _ hp)
    rw [free_inductionStep]
    convert hs using 1
    change implies _ (Semiformula.rewAux (Rew.subst ![Rew.free (succ (.bvar 0))])
      (Semiformula.rewAux Rew.shift (predecessor (.bvar 0)))) = _
    simp [predecessor_rew,rew_succ,Rew.shift_bvar,Rew.subst_bvar,x]
  exact ND.mp step (ND.mp base ind)

theorem predecessorContext_mem_theory (p : ND.Form) (hp : p ∈ predecessorContext) : p.univCl ∈ ordinaryPAeq := by
  simp only [predecessorContext,List.mem_append,List.mem_singleton] at hp
  rcases hp with hp | rfl
  · exact ⟨p,equalityContext_is_PAeq p hp,rfl⟩
  · exact ⟨inductionFormula predecessorProperty,.induction predecessorProperty,rfl⟩

def predecessorInstance (a : GroundTerm) : ND.Proof (closedContext predecessorContext) (predecessor a) := by
  have d := ND.allElim _ a (ND.replaceByClosures predecessorCertificate)
  change ND.Proof _ (Semiformula.rewAux (Rew.subst ![a]) predecessorProperty) at d
  simpa only [predecessorProperty,predecessor_rew,Rew.subst_bvar,Matrix.cons_val_zero] using d

#print axioms predecessorCertificate
#print axioms predecessorInstance
end M6.PA.Presentation

