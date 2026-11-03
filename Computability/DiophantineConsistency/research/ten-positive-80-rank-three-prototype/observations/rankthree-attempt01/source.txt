import Direct80RankLower
import Direct80TransportModel

/-! A strengthened rank bound from the actual positive mask gap. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80RankThree
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_rank_gt_three_q (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : (31:V)≤(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    3*q p v<rankNat p v := by
  have hbpos : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb
  have hgap := (TenPositive80TransportModel.graph_transport_and_mask p v hbpos hv hz).2
  have hq32 := (TenPositive80RankLower.graph_rank_lower p v hb (hv 0) (hv 2) (hv 5)).1
  have hq1 : 1≤q p v := le_trans (by norm_num) hq32
  have hqpos : 0<q p v := lt_of_lt_of_le (by norm_num) hq1
  have hFlt : v 1<q p v := lt_of_le_of_lt (by simp) hgap
  have hqF : 1≤q p v-v 1 := pos_iff_one_le.mp (tsub_pos_iff_lt.mpr hFlt)
  have hbmul : b p v≤b p v*(q p v-v 1) := le_mul_of_one_le_right (by simp) hqF
  have hG : q p v≤b p v*(q p v-v 1)+v 2 := by
    have h := add_le_add hbmul (pos_iff_one_le.mp (hv 2))
    simpa only [q] using h
  have hqq1 : 1≤q p v*q p v := one_le_mul hq1 hq1
  have hqsub : (4:V)≤q p v*q p v-1 := (le_tsub_iff_right hqq1).mpr (calc
    4+1≤32 := by norm_num
    _≤q p v := hq32
    _≤q p v*q p v := le_mul_of_one_le_right (by simp) hq1)
  calc
    3*q p v<4*q p v := mul_lt_mul_of_pos_right (by norm_num) hqpos
    _=q p v*4 := by ring
    _≤(b p v*(q p v-v 1)+v 2)*(q p v*q p v-1) :=
      mul_le_mul hG hqsub (by simp) (by simp)
    _≤rankNat p v := by dsimp [rankNat]; simp

#print axioms Direct80RankThree.graph_rank_gt_three_q
end Direct80RankThree
