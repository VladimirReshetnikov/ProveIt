module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationPredecessor
@[expose] public section

namespace M6.PA.Presentation
open FFL FFL.FirstOrder

def tri {ξ : Type} {n : Nat} (a b : Semiterm language ξ n) : Semiformula language ξ n :=
  .or (less a b) (.or (eq a b) (less b a))
theorem tri_rew {ξ ζ : Type} {n m : Nat} (ω : Rew language ξ n ζ m) (a b : Semiterm language ξ n) :
    Semiformula.rewAux ω (tri a b) = tri (ω a) (ω b) := by
  change Semiformula.or (Semiformula.rewAux ω (less a b))
    (.or (Semiformula.rewAux ω (eq a b)) (Semiformula.rewAux ω (less b a))) = _
  rw [less_rew,eq_rew,less_rew]
  rfl

def EqualityPremises.triRight {Γ : List ND.Form} (E : EqualityPremises Γ)
    (a b c : GroundTerm) (he : ND.Proof Γ (eq b c)) (hp : ND.Proof Γ (tri a b)) : ND.Proof Γ (tri a c) := by
  have ht : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![b]) (tri (Rew.bShift a) (.bvar 0))) := by
    simpa only [tri_rew,Rew.subst_bShift_app,Rew.subst_bvar,Matrix.cons_val_zero] using hp
  have d := E.substituteOne (tri (Rew.bShift a) (.bvar 0)) b c he ht
  simpa only [tri_rew,Rew.subst_bShift_app,Rew.subst_bvar,Matrix.cons_val_zero] using d

def succLessInstance (a b : GroundTerm) : ND.Proof orderLawContext
    (implies (less a b) (less (succ a) (succ b))) := by
  let Γ := orderLawContext
  apply ND.impIntro
  let Δ := less a b :: Γ
  have hp : ND.Proof Δ (less a b) := ND.assumption (by simp [Δ])
  apply ND.lessElim a b hp
  let x := Rew.shift a
  let y := Rew.shift b
  let u : GroundTerm := .fvar 0
  let h := eq (add x (succ u)) y
  let Θ := h :: ND.shifted Δ
  have incl : ∀ p,p ∈ Γ → p ∈ Θ := by
    intro p hp
    apply List.mem_cons_of_mem
    exact closed_members_shifted orderLawContext_closed (fun p hp => List.mem_cons_of_mem _ hp) p hp
  let E := equalityContextPremises.weaken (Δ := Θ)
    (by intro p hp; apply incl; simp [Γ,orderLawContext,addLawsContext,hp])
  have ar : ND.Proof Θ addSucc := ND.assumption (incl _ (by simp [Γ,orderLawContext]))
  have hr : ND.Proof Θ (eq (add (succ x) (succ u)) (succ (add x (succ u)))) := by
    have d := ND.allElim2 _ x (succ u) ar
    convert d using 1 <;> dsimp [addSucc] <;> equalityInstanceSyntax
  have hw : ND.Proof Θ h := ND.assumption (by simp [Θ])
  have he := E.transitivityOf hr (ND.mp hw (E.successor (add x (succ u)) y))
  have d := ND.lessIntro (succ x) (succ y) u he
  simpa only [less_shift,rew_succ] using d

def successorTri {Γ : List ND.Form} (incl : ∀ p,p ∈ orderLawContext → p ∈ Γ)
    (a b : GroundTerm) (hp : ND.Proof Γ (tri a b)) : ND.Proof Γ (tri (succ a) (succ b)) := by
  let E := equalityContextPremises.weaken (Δ := Γ)
    (by intro p hp; apply incl; simp [orderLawContext,addLawsContext,hp])
  have sl := ND.weaken (succLessInstance a b) incl
  have sr := ND.weaken (succLessInstance b a) incl
  apply ND.orElim hp
  · have up : ∀ p,p ∈ Γ → p ∈ less a b :: Γ := fun p hp => List.mem_cons_of_mem _ hp
    exact ND.orLeft (ND.mp (ND.assumption (by simp)) (ND.weaken sl up))
  · let Δ := Semiformula.or (eq a b) (less b a) :: Γ
    have up : ∀ p,p ∈ Γ → p ∈ Δ := fun p hp => List.mem_cons_of_mem _ hp
    have hd : ND.Proof Δ (.or (eq a b) (less b a)) := ND.assumption (by simp [Δ])
    apply ND.orElim hd
    · have up2 : ∀ p,p ∈ Γ → p ∈ eq a b :: Δ := fun p hp => List.mem_cons_of_mem _ (up p hp)
      exact ND.orRight (ND.orLeft (ND.mp (ND.assumption (by simp)) (ND.weaken (E.successor a b) up2)))
    · have up2 : ∀ p,p ∈ Γ → p ∈ less b a :: Δ := fun p hp => List.mem_cons_of_mem _ (up p hp)
      exact ND.orRight (ND.orRight (ND.mp (ND.assumption (by simp)) (ND.weaken sr up2)))

def zeroTriInstance (a : GroundTerm) : ND.Proof (closedContext zeroLeContext) (tri zero a) := by
  have d := ND.allElim _ a (ND.replaceByClosures zeroLeCertificate)
  have h : ND.Proof (closedContext zeroLeContext) (.or (eq zero a) (less zero a)) := by
    change ND.Proof _ (Semiformula.rewAux (Rew.subst ![a]) zeroLeProperty) at d
    simpa only [zeroLeProperty_rew,Rew.subst_bvar,Matrix.cons_val_zero] using d
  apply ND.orElim h
  · exact ND.orRight (ND.orLeft (ND.assumption (by simp)))
  · exact ND.orLeft (ND.assumption (by simp))

#print axioms successorTri
#print axioms zeroTriInstance
end M6.PA.Presentation

