import P64ConverseAlgebra
import DiophantineConsistency.ArithmeticPellCongruences

/-! First-Pell residue supplies P64's Y² carrier quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace P64ConverseResidue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticPellCongruences
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Canonical odd-index and first-Pell data supply the exact quotient used
by the P64 gamma witness, without an independent divisibility assumption. -/
theorem carrier_quotient (X Y r R k : V)
    (hP : 1≤(X*Y)*Y)
    (hR : R=2*r+1)
    (hk : k=2*ycoord (r+1) (2*((X*Y)*Y-1)+1)) :
    ∃ t : V, k=R+1+4*X*(Y*Y)*t := by
  let P := (X*Y)*Y
  let B := 2*(P-1)+1
  have hP1 : P-1+1=P := tsub_add_cancel_of_le hP
  have hB : B+1=2*P := by
    dsimp [B]
    calc
      2*(P-1)+1+1=2*(P-1+1) := by ring
      _=2*P := by rw [hP1]
  have hdiv : 2*P ∣ B+1 := by rw [hB]
  obtain ⟨_,t,_,ht⟩ := residue_quotients (r+1) B (2*P) hdiv
  refine ⟨t,?_⟩
  change k=2*ycoord (r+1) B at hk
  rw [hk,ht,hR]
  dsimp [P]
  ring

theorem positive_gamma (X Y r R k gammaOld : V)
    (hP : 1≤(X*Y)*Y) (hR : R=2*r+1)
    (hk : k=2*ycoord (r+1) (2*((X*Y)*Y-1)+1))
    (hgamma : 0<gammaOld) :
    ∃ t gamma : V, 0<gamma ∧ k=R+1+4*X*(Y*Y)*t ∧
      gamma=gammaOld+4*X*t := by
  obtain ⟨t,ht⟩ := carrier_quotient X Y r R k hP hR hk
  exact ⟨t,gammaOld+4*X*t,add_pos_of_pos_of_nonneg hgamma (by simp),ht,rfl⟩

#print axioms P64ConverseResidue.carrier_quotient
#print axioms P64ConverseResidue.positive_gamma
end P64ConverseResidue
