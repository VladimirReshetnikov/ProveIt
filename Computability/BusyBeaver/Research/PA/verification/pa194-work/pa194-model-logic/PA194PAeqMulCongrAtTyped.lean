import PA194PAeqAddOneProof
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.MulCongrTyped
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194PAeq.AddOne
variable {Γ : List Fm}
theorem substShiftThrice (s t u v : Tm) :
    (Rew.subst ![v]) ((Rew.subst ![u]).q ((Rew.subst ![t]).q.q
      (Rew.bShift (Rew.bShift (Rew.bShift s))))) = s := by simp
noncomputable def mulCongrAt (a b c d : Tm) (h : mulCongruence ∈ Γ)
    (p : ND.Proof Γ (eq a b)) (q : ND.Proof Γ (eq c d)) :
    ND.Proof Γ (eq (mul a c) (mul b d)) := by
  have h0 : ND.Proof Γ mulCongruence := ND.assumption h
  have h1 := ND.allElim _ d h0
  have h2 := ND.allElim _ c h1
  have h3 := ND.allElim _ b h2
  have h4 := ND.allElim _ a h3
  have ht := substShiftThrice d c b a
  simp only [Rew.subst, Rew.q] at ht
  have hh : ND.Proof Γ (eq a b 🡒 (eq c d 🡒 eq (mul a c) (mul b d))) := by
    simpa [mulCongruence,implies,Semiformula.imp_eq,eq,mul,Semiformula.neg_eq,Semiformula.neg,
      Semiformula.rewAux,Rew.subst,Rew.func,Rew.q,emptyFn,substShift,substShiftTwice,ht] using h4
  exact ND.mp q (ND.mp p hh)
#print axioms mulCongrAt
end PA194PAeq.MulCongrTyped
