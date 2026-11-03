import DiophantineConsistency.CompactFixedBeta

/-! Fixed beta is odd, without expanding its large power. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80FixedBetaOdd
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency CompactFixedBeta
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem pred_pow_odd (n : ℕ) : 2^(n+1)-1=2*(2^n-1)+1 := by
  have h : 0<2^n := pow_pos (by norm_num) _
  rw [pow_succ]
  omega

theorem beta_odd_nat : ∃u : ℕ, betaNat=2*u+1 := by
  let n : ℕ := 67*8807-1
  have hexp : 67*8807=n+1 := by dsimp [n]
  refine ⟨2^n-1,?_⟩
  unfold betaNat
  rw [hexp]
  exact pred_pow_odd n

theorem beta_odd_model : ∃u : V, (betaNat:V)=2*u+1 := by
  obtain ⟨u,hu⟩ := beta_odd_nat
  refine ⟨(u:V),?_⟩
  exact_mod_cast hu

#print axioms Direct80FixedBetaOdd.beta_odd_nat
#print axioms Direct80FixedBetaOdd.beta_odd_model
end Direct80FixedBetaOdd
