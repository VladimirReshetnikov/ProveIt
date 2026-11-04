import DiophantineConsistency.Compact44.DirectMainProjection

/-! Conditional direct-gap lemma, separate from growth estimates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectMainGapBalance
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- If the main root exceeds `(a+1)c` and the ordinate dominates
`X+H*w`, the direct balance forces `w<G`. -/
theorem gap_of_balance (U X a c H G R k main w : V)
    (hU : 0<U) (hR : R+1≤k)
    (hbalance : U*(X+a*c)+H*(U*G+R+1)=H*k+U*main)
    (hmain : (a+1)*c<main) (hgrowth : X+H*w<c) : w<G := by
  have he : U*(X+a*c+H*G)+H*(R+1)=U*main+H*k := by
    calc
      U*(X+a*c+H*G)+H*(R+1)=U*(X+a*c)+H*(U*G+R+1) := by ring
      _=H*k+U*main := hbalance
      _=U*main+H*k := by ring
  have hmul : U*main≤U*(X+a*c+H*G) := by
    have h := mul_le_mul_of_nonneg_left hR (by simp : (0:V)≤H)
    have h' : U*main+H*(R+1)≤U*(X+a*c+H*G)+H*(R+1) := by
      rw [he]
      simpa only [add_comm] using add_le_add_left h (U*main)
    exact (add_le_add_iff_right (H*(R+1))).mp h'
  have hmainle : main≤X+a*c+H*G := le_of_mul_le_mul_left hmul hU
  have hstrong : a*c+c<X+a*c+H*G := by
    calc
      a*c+c=(a+1)*c := by ring
      _<main := hmain
      _≤X+a*c+H*G := hmainle
  have hclear : c<X+H*G := by
    apply (add_lt_add_iff_left (a*c)).mp
    calc
      a*c+c<X+a*c+H*G := hstrong
      _=a*c+(X+H*G) := by ring
  have hscale : H*w<H*G := by
    apply (add_lt_add_iff_left X).mp
    exact lt_trans hgrowth hclear
  exact lt_of_mul_lt_mul_left hscale (by simp)

#print axioms DirectMainGapBalance.gap_of_balance
end DirectMainGapBalance
