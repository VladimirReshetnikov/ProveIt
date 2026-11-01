import DiophantineConsistency.AdaptiveDirectOrdinate86Context
import DiophantineConsistency.ArithmeticSignedPairExpressions
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 6000000
noncomputable section
namespace DiophantineConsistency.AdaptiveZ46RootAlgebra
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticSignedPairs ArithmeticSignedPairExpressions AdaptiveFirstRootFactor87
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def residual (z : Pair V) (s r : V) (a b c d : Pair V) : Pair V :=
  minus z (minus (plus (multiply (natural s) (minus (plus a (natural r)) b)) c) d)

theorem root_invariant (zOld zNew : Pair V) (s rOld rNew : V) (a b c d : Pair V)
    (h : Equivalent (plus zOld (natural (s*rNew))) (plus zNew (natural (s*rOld)))) :
    Equivalent (residual zOld s rOld a b c d) (residual zNew s rNew a b c d) := by
  dsimp only [Equivalent, residual, plus, minus, multiply, natural] at *
  simp only [mul_zero,zero_mul,add_zero,zero_add] at *
  let rest := s*(a.2+b.1)+c.2+d.1+s*(a.1+b.2)+c.1+d.2
  calc
    _ = (zOld.1+s*rNew+zNew.2)+rest := by dsimp [rest]; ring
    _ = (zOld.2+(zNew.1+s*rOld))+rest := by rw [h]
    _ = _ := by dsimp [rest]; ring
#print axioms root_invariant
end DiophantineConsistency.AdaptiveZ46RootAlgebra
