import DiophantineConsistency.ArithmeticPellPowerRecovery

/-! Rank parity forces the beta-J radix parity without coprimality assumptions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80Parity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem odd_rank_even_radix (beta J q G T R : V)
    (hbeta : ∃ u : V, beta=2*u+1)
    (hq : q=beta*J+1)
    (hR : R=G*(q*q-1)+J*T)
    (hodd : R%2=1) : ∃ w : V, q=2*w := by
  obtain ⟨j,hj|hj⟩ := even_or_odd J
  · have hqform : q=2*(beta*j)+1 := by rw [hq,hj]; ring
    have hq2 : q*q-1=2*(2*(beta*j)*(beta*j)+2*(beta*j)) := by
      rw [hqform]
      have h : (2*(beta*j)+1)*(2*(beta*j)+1)=2*(2*(beta*j)*(beta*j)+2*(beta*j))+1 := by ring
      rw [h,add_tsub_cancel_right]
    have hRform : R=2*(G*(2*(beta*j)*(beta*j)+2*(beta*j))+j*T) := by
      rw [hR,hq2,hj]
      ring
    have hzero : R%2=0 := by
      rw [hRform,show 2*(G*(2*(beta*j)*(beta*j)+2*(beta*j))+j*T)=
        (G*(2*(beta*j)*(beta*j)+2*(beta*j))+j*T)*2 by ring]
      exact mod_mul_self_left _ _
    exact False.elim ((zero_ne_one : (0:V)≠1) (hzero.symm.trans hodd))
  · obtain ⟨u,hu⟩ := hbeta
    refine ⟨2*u*j+u+j+1,?_⟩
    rw [hq,hu,hj]
    ring

#print axioms Direct80Parity.odd_rank_even_radix
end Direct80Parity
