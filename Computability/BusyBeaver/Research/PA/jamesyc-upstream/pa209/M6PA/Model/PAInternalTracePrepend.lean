module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import M6PA.Model.PAInternalTraceCompose
@[expose] public section

namespace M6.Arithmetic.PA.InternalTrace
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
attribute [local irreducible] StepFormula.formula Step
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma segment_zero (q l r : V) : Segment 0 ?[q] ?[l] ?[r] q l r q l r := by
  simp [Segment]

lemma segment_prepend {n qs ls rs q0 l0 r0 q l r qe le re : V}
    (hfirst : Step q0 l0 r0 q l r) (h : Segment n qs ls rs q l r qe le re) :
    Segment (n+1) (q0 ∷ qs) (l0 ∷ ls) (r0 ∷ rs) q0 l0 r0 qe le re := by
  rcases h with ⟨hq,hl,hr,hq0,hl0,hr0,hqn,hln,hrn,hsteps⟩
  refine ⟨by simp [hq],by simp [hl],by simp [hr],by simp,by simp,by simp,
    by simpa using hqn,by simpa using hln,by simpa using hrn,?_⟩
  intro i hi
  rcases zero_or_succ i with rfl | ⟨i,rfl⟩
  · simpa [hq0,hl0,hr0] using hfirst
  · have hi' : i < n := by simpa using hi
    simpa using hsteps i hi'

lemma segment_prepend_nat {n : Nat} {qs ls rs q0 l0 r0 q l r qe le re : V}
    (hfirst : Step q0 l0 r0 q l r) (h : Segment (n : V) qs ls rs q l r qe le re) :
    Segment ((n+1 : Nat) : V) (q0 ∷ qs) (l0 ∷ ls) (r0 ∷ rs) q0 l0 r0 qe le re := by
  simpa only [Nat.cast_add,Nat.cast_one] using segment_prepend hfirst h

#print axioms segment_prepend
end M6.Arithmetic.PA.InternalTrace

