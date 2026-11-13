import Direct80RankLower
import DiophantineConsistency.CompactFixedBeta

/-! The symbolic Mersenne beta is at least 31 without numeral expansion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositiveFixedBetaLower
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency CompactFixedBeta
attribute [local irreducible] CompactFixedBeta.betaNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem beta_ge_31 : (31:V)≤(betaNat:V) := by
  have hsmall : Exp.exp (5:V)=32 := by
    rw [show (5:V)=4+1 by ring,exp_succ,show (4:V)=3+1 by ring,exp_succ,
      show (3:V)=2+1 by ring,exp_succ,show (2:V)=1+1 by ring,exp_succ,
      show (1:V)=0+1 by ring,exp_succ]
    norm_num
  have hindex : (5:V)≤(67:V)*8807 := by norm_num
  have hexp : (32:V)≤Exp.exp ((67:V)*8807) := by
    rw [←hsmall]
    exact exp_monotone_le.mpr hindex
  rw [←CompactFixedBeta.beta_identity] at hexp
  apply (add_le_add_iff_right (1:V)).mp
  simpa only [show (31:V)+1=32 by ring] using hexp

#print axioms TenPositiveFixedBetaLower.beta_ge_31
end TenPositiveFixedBetaLower
