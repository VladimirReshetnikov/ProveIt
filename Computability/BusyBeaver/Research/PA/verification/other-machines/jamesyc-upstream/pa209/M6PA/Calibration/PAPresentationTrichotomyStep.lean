module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationTrichotomyTools
@[expose] public section

namespace M6.PA.Presentation
open FFL FFL.FirstOrder

def triAll {ξ : Type} {n : Nat} (a : Semiterm language ξ n) : Semiformula language ξ n :=
  .all (tri (Rew.bShift a) (.bvar 0))
theorem triAll_rew {ξ ζ : Type} {n m : Nat} (ω : Rew language ξ n ζ m) (a : Semiterm language ξ n) :
    Semiformula.rewAux ω (triAll a) = triAll (ω a) := by
  simp only [triAll,Semiformula.rewAux,tri_rew,Rew.q_comp_bShift_app,Rew.q_bvar_zero]
  rfl

def triBaseContext : List ND.Form := orderLawContext ++
  (closedContext predecessorContext ++ (closedContext zeroLeContext ++ [addZero]))
theorem triBaseContext_closed (p : ND.Form) (hp : p ∈ triBaseContext) : p.freeVariables = ∅ := by
  simp only [triBaseContext,List.mem_append,List.mem_singleton] at hp
  rcases hp with hp | hp | hp | rfl
  · exact orderLawContext_closed p hp
  · exact closedContext_closed predecessorContext p hp
  · exact closedContext_closed zeroLeContext p hp
  · simp [addZero,eq,add,zero,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ]
theorem triBaseContext_mem_theory (p : ND.Form) (hp : p ∈ triBaseContext) : p.univCl ∈ ordinaryPAeq := by
  simp only [triBaseContext,List.mem_append,List.mem_singleton] at hp
  rcases hp with hp | hp | hp | rfl
  · exact orderLawContext_mem_theory p hp
  · exact closedContext_mem_theory predecessorContext_mem_theory p hp
  · exact closedContext_mem_theory (T := ordinaryPAeq)
      (fun q hq => ⟨q,zeroLeContext_is_PAeq q hq,rfl⟩) p hp
  · exact ⟨addZero,.fixed _ (by simp [fixedAxioms]),rfl⟩

def triSuccessorStep {Γ : List ND.Form} (incl : ∀ p,p ∈ triBaseContext → p ∈ Γ)
    (a : GroundTerm) (ih : ND.Proof Γ (triAll a)) : ND.Proof Γ (triAll (succ a)) := by
  apply ND.allIntro
  let x := Rew.shift a
  let y : GroundTerm := .fvar 0
  let Γ1 := ND.shifted Γ
  have in1 : ∀ p,p ∈ triBaseContext → p ∈ Γ1 := closed_members_shifted triBaseContext_closed incl
  have hi : ND.Proof Γ1 (triAll x) := by
    have d := ND.shiftProof ih
    change ND.Proof _ (Semiformula.rewAux Rew.shift (triAll a)) at d
    simpa only [triAll_rew] using d
  have pred : ND.Proof Γ1 (predecessor y) := ND.weaken (predecessorInstance y)
    (by intro p hp; apply in1; simp [triBaseContext,hp])
  have goal : ND.Proof Γ1 (tri (succ x) y) := by
    apply ND.orElim pred
    · let Δ := eq y zero :: Γ1
      have in2 : ∀ p,p ∈ triBaseContext → p ∈ Δ := fun p hp => List.mem_cons_of_mem _ (in1 p hp)
      let E := equalityContextPremises.weaken (Δ := Δ)
        (by intro p hp; apply in2; simp [triBaseContext,orderLawContext,addLawsContext,hp])
      have az : ND.Proof Δ addZero := ND.assumption (in2 _ (by simp [triBaseContext]))
      have h0 : ND.Proof Δ (eq (add zero (succ x)) (succ x)) := by
        have d := ND.allElim _ (succ x) az
        convert d using 1 <;> dsimp [addZero] <;> equalityInstanceSyntax
      have hl := ND.lessIntro zero (succ x) x h0
      have ht : ND.Proof Δ (tri (succ x) zero) := ND.orRight (ND.orRight hl)
      have he : ND.Proof Δ (eq y zero) := ND.assumption (by simp [Δ])
      exact E.triRight (succ x) zero y (E.symmetryOf he) ht
    · let ep := Semiformula.exs (eq (Rew.bShift y) (succ (.bvar 0)))
      let Δ := ep :: Γ1
      have hd : ND.Proof Δ ep := ND.assumption (by simp [Δ])
      apply ND.exsElim hd
      let x' := Rew.shift x
      let y' := Rew.shift y
      let v : GroundTerm := .fvar 0
      let h := eq y' (succ v)
      let Θ := h :: ND.shifted Δ
      have in2 : ∀ p,p ∈ triBaseContext → p ∈ Δ := fun p hp => List.mem_cons_of_mem _ (in1 p hp)
      have in3 : ∀ p,p ∈ triBaseContext → p ∈ Θ := fun p hp => List.mem_cons_of_mem _
        (closed_members_shifted triBaseContext_closed in2 p hp)
      let E := equalityContextPremises.weaken (Δ := Θ)
        (by intro p hp; apply in3; simp [triBaseContext,orderLawContext,addLawsContext,hp])
      have hi' : ND.Proof Θ (triAll x') := by
        have d := ND.shiftProof (ND.weaken hi (fun p hp => List.mem_cons_of_mem ep hp))
        have e := ND.weaken d (fun p hp => List.mem_cons_of_mem h hp)
        change ND.Proof _ (Semiformula.rewAux Rew.shift (triAll x)) at e
        simpa only [triAll_rew] using e
      have hv : ND.Proof Θ (tri x' v) := by
        have d := ND.allElim _ v hi'
        change ND.Proof _ (Semiformula.rewAux (Rew.subst ![v]) _) at d
        simpa only [triAll,tri_rew,Rew.subst_bShift_app,Rew.subst_bvar,Matrix.cons_val_zero] using d
      have hs := successorTri (Γ := Θ) (by intro p hp; apply in3; simp [triBaseContext,hp]) x' v hv
      have he : ND.Proof Θ h := ND.assumption (by simp [Θ])
      have hout := E.triRight (succ x') (succ v) y' (E.symmetryOf he) hs
      change ND.Proof ((eq (Rew.bShift y) (succ (.bvar 0))).free :: ND.shifted Δ)
        (Semiformula.rewAux Rew.shift (tri (succ x) y))
      have hbody : (eq (Rew.bShift y) (succ (.bvar 0))).free = h := by
        change Semiformula.rewAux Rew.free (eq (Rew.bShift y) (succ (.bvar 0))) = h
        rw [eq_rew,rew_succ,Rew.free_bShift_app]
        rfl
      rw [hbody,tri_rew,rew_succ]
      exact hout
  change ND.Proof Γ1 (Semiformula.rewAux Rew.free (tri (Rew.bShift (succ a)) (.bvar 0)))
  simpa only [tri_rew,Rew.free_bShift_app,rew_succ,Rew.free_bvar_last_zero] using goal

#print axioms triSuccessorStep
end M6.PA.Presentation

