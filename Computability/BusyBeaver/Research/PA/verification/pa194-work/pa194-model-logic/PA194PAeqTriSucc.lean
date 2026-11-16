import PA194PAeqSuccLtSucc
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.TriSucc
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194PAeq.AddOne PA194PAeq.SuccLtSucc
variable {Γ : List Fm}
def tri {ξ : Type} {n : Nat} (a b : Semiterm language ξ n) : Semiformula language ξ n :=
  less a b ⋎ eq a b ⋎ less b a
noncomputable def atTerms (a b : Tm) (h : ND.Proof Γ (tri a b))
    (hax : ∀ p ∈ AddLtAdd.axioms, p ∈ Γ) : ND.Proof Γ (tri (succ a) (succ b)) := by
  apply ND.orElim h
  · let Δ := less a b :: Γ
    have hl : ND.Proof Δ (less a b) := ND.assumption (by simp [Δ])
    exact ND.orLeft (SuccLtSucc.atTerms a b hl (by intro p hp; simp [Δ,hax p hp]))
  · let Δ := (eq a b ⋎ less b a) :: Γ
    have hh : ND.Proof Δ (eq a b ⋎ less b a) := ND.assumption (by simp [Δ])
    apply ND.orElim hh
    · let Ψ := eq a b :: Δ
      have he : ND.Proof Ψ (eq a b) := ND.assumption (by simp [Ψ])
      exact ND.orRight (ND.orLeft (succCongrAt _ _ (by simp [Ψ,Δ,hax succCongruence (by simp [AddLtAdd.axioms])]) he))
    · let Ψ := less b a :: Δ
      have hl : ND.Proof Ψ (less b a) := ND.assumption (by simp [Ψ])
      exact ND.orRight (ND.orRight (SuccLtSucc.atTerms b a hl (by intro p hp; simp [Ψ,Δ,hax p hp])))
#print axioms atTerms
end PA194PAeq.TriSucc
