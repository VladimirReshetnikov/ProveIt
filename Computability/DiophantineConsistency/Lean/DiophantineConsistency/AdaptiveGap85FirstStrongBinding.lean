import DiophantineConsistency.AdaptiveGap85FamilyGeneral

/-! The weak first/strong arithmetic hypotheses bind to actual 85 factors. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85FirstStrongBinding
open AdaptiveGap85Factors AdaptiveGap85FamilyBinding

def witnessStrong (b k a t f i : ℤ) : Fin 13 → ℤ :=
  let q := b+1
  let B := q*(1+k*q)-(1+a)*q
  let m := q*(k+t)
  let r := 2*B+m-2
  ![1,1+a,q,f,i,1,1,q^3,r,1,1,1,1]

/-- Under the quotient/remainder relation and strong norm, the actual first
and strong factor projections evaluate to one. This says nothing about the
main or auxiliary factors. -/
theorem first_and_strong_actual (b k a t f i mu nu : ℤ) (h : k=b*t+a)
    (hstrong : let Y := (b+1)^3
      let c := 1+2*Y
      let Delta := (2*Y+1)*(2*Y+3)
      (c*c*i)*(c*c*i)+Delta=Delta*(f*f)) :
    ((factors (ports b k mu nu)).1).eval (witnessStrong b k a t f i)=1 ∧
    ((factors (ports b k mu nu)).2.2.2).eval (witnessStrong b k a t f i)=1 := by
  constructor
  · have hf := first_factor_actual b k a t mu nu h
    simpa [factors,Expr.eval,ports,witnessStrong,witness] using hf
  · dsimp at hstrong
    simp [factors,Expr.eval,ports,witnessStrong]
    nlinarith [hstrong]
end DiophantineConsistency.AdaptiveGap85FirstStrongBinding
