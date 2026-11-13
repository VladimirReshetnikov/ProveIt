import FirstMainLargeK

/-! Source-only natural first-Pell root gap. No graph, parent root,
Lean elaboration or endpoint is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.FirstRootGapDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A large first-Pell ordinate forces tau>m*k+s for every s≤m. -/
theorem root_gt_linear (m k tau s : V)
    (hm : 0<m) (hsm : s≤m) (hk : 8*m+4≤k)
    (hn : tau*tau=1+m*(m+1)*k*k) : m*k+s<tau := by
  have hbase : 4*m+2≤k := by nlinarith
  have hmk : m≤k := by nlinarith
  have hprod : k*(4*m+2)≤k*k := mul_le_mul_of_nonneg_left hbase (Arithmetic.zero_le k)
  have hmk0 : 0≤m*k := Arithmetic.zero_le _
  have hbound : 2*m*k+m≤k*k := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hbound (Arithmetic.zero_le m)
  have hsq : (m*k+m)*(m*k+m)<tau*tau := by nlinarith
  have hlt : m*k+m<tau := lt_of_mul_self_lt_mul_self₀ (Arithmetic.zero_le _) hsq
  exact lt_of_le_of_lt (add_le_add_left hsm (m*k)) hlt

end DiophantineConsistency.FirstRootGapDraft

#print axioms DiophantineConsistency.FirstRootGapDraft.root_gt_linear
