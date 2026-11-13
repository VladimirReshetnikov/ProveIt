import DiophantineConsistency.ModelThirteenCarrierPrelude
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ModelThirteenCarrier
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Combine the strong-index and auxiliary-seed lemmas without fixed ports. -/
theorem natural_seed (a R b c : V) (hb : 0 < b) (hc : 0 < c)
    (hphase : R % 4 = 3) (hcR : c = ycoord R a) :
    ∃ t j : V, 0 < j ∧
      let i := b * j
      let f := xcoord t a
      ∃ T u y : V, 0 < f ∧ 0 < T ∧ 0 < u ∧ 0 < y ∧
        f*f = 1 + delta a * (i*c*c) * (i*c*c) ∧
        let I := delta a*i*c*c
        y = ycoord R (I-2) ∧ xcoord R (I-2) = I*u ∧
        f*f*c*T = u+c+f*f*R ∧ u = absdiff (f*f*c*T) (f*f*R+c) ∧
        I*I*u*u+y*y = 1+I*I*y*y ∧ (y+1)%(4*I*I) = 0 := by
  obtain ⟨t,j,_,hj,hyt⟩ := ArithmeticThirteenSeed.strong_index a b c hb hc
  refine ⟨t,j,hj,?_⟩
  dsimp only
  have hyt' : ycoord t a = (b*j)*ycoord R a*ycoord R a := by
    rw [← hcR]
    exact hyt
  have h := ArithmeticThirteenSeed.auxiliary_seed_of a R t (b*j) hphase (mul_pos hb hj) hyt'
  dsimp only at h
  rw [← hcR] at h
  exact h

end DiophantineConsistency.ModelThirteenCarrier
#print axioms DiophantineConsistency.ModelThirteenCarrier.natural_seed
