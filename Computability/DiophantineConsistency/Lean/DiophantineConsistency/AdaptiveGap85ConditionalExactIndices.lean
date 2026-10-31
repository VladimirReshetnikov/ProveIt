import DiophantineConsistency.AdaptiveGap85ActualSignedHalf
import DiophantineConsistency.AdaptiveGap85OrientedRank

/-! Conditional exact indices for a possibly signed 85 rank. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ConditionalExactIndices
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticPellRecurrence ArithmeticPellHalfIndex
open AdaptiveGap85Literal AdaptiveGap85ActualSignedHalf AdaptiveGap85OrientedRank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Under the explicit rank-size, half-size and main-index-growth hypotheses,
an actual 85 zero has positive rank and exact relation m+1=2n. -/
theorem expressionAt_conditional_exact_indices85 (p : Fin 4 → ℕ) (v : Fin 13 → V) (n m : V)
    (hb : 0<(p 0:V)) (hv : ∀ j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v)
    (hn : 0<n)
    (hny : 2*ycoord n (2*((v 6*v 7)*v 7-1)+1)=v 9+v 10)
    (hm6 : 6≤m)
    (hmy : ycoord m (v 6*v 7+v 7)=v 9+v 7*(v 9+v 10))
    (hhalf : 2*rankMagnitude p v<v 9+v 7*(v 9+v 10))
    (hsmall : rankMagnitude p v+2*n<(1+v 0*(p 0:V))^4) :
    0<rankMagnitude p v ∧ m=rankMagnitude p v ∧ m+1=2*n := by
  have ho := expressionAt_oriented_rank85 p v n hb hv hz hn hny (by
    simpa only [rankMagnitude] using hsmall)
  have hR : 0<rankMagnitude p v := by
    dsimp only [rankMagnitude,absdiff]
    exact add_pos_of_pos_of_nonneg (tsub_pos_iff_lt.mpr ho.1) (by simp)
  have hm := expressionAt_signed_half85 p v m hv hm6 hmy hR hhalf hz
  have he : rankMagnitude p v+1=2*n := by
    simpa only [rankMagnitude] using ho.2
  exact ⟨hR,hm,by rw [hm]; exact he⟩
end DiophantineConsistency.AdaptiveGap85ConditionalExactIndices
