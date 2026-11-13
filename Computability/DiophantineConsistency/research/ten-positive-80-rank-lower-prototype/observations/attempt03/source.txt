import Direct80NaturalRank

/-! Radix and rank lower bounds from the literal natural rank expression. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositive80RankLower
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open TenPositive80Factors TenPositive80NaturalRank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem rank_ge_radix (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hJ : 0<v 0) (ha : 0<v 2) : q p v≤rankNat p v := by
  have hb0 : 0<b p v := mul_pos hb hJ
  have hq2 : 2≤q p v := by
    have h := _root_.add_le_add_right (pos_iff_one_le.mp hb0) (1:V)
    simpa only [q,show (2:V)=1+1 by ring,add_comm] using h
  have hq1 : 1≤q p v := le_trans (by norm_num) hq2
  have hqq1 : 1≤q p v*q p v := one_le_mul hq1 hq1
  have hqq : q p v+1≤q p v*q p v := calc
    q p v+1≤q p v+q p v := by simpa only [add_comm] using _root_.add_le_add_left hq1 (q p v)
    _=2*q p v := by ring
    _≤q p v*q p v := mul_le_mul_of_nonneg_right hq2 (by simp)
  have hqsub : q p v≤q p v*q p v-1 := (le_tsub_iff_right hqq1).mpr hqq
  have hG : 1≤b p v*(q p v-v 1)+v 2 := pos_iff_one_le.mp (by
    exact add_pos_of_nonneg_of_pos (by simp) ha)
  calc
    q p v≤q p v*q p v-1 := hqsub
    _≤(b p v*(q p v-v 1)+v 2)*(q p v*q p v-1) := le_mul_of_one_le_left (by simp) hG
    _≤rankNat p v := by dsimp [rankNat]; simp

theorem graph_rank_lower (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : (31:V)≤(p 0:V)) (hJ : 0<v 0) (ha : 0<v 2) (hw : 0<v 5) :
    32≤q p v ∧ 32≤X p v ∧ 32≤rankNat p v := by
  have hbpos : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb
  have hJ1 : 1≤v 0 := pos_iff_one_le.mp hJ
  have hbetaJ : (p 0:V)≤b p v := le_mul_of_one_le_right (by simp) hJ1
  have hq : 32≤q p v := by
    have h := _root_.add_le_add_right (le_trans hb hbetaJ) (1:V)
    simpa only [q,add_comm,show (1:V)+31=32 by ring] using h
  have hqX : q p v≤X p v := by
    change q p v≤v 5*q p v
    exact le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp hw)
  exact ⟨hq,le_trans hq hqX,le_trans hq (rank_ge_radix p v hbpos hJ ha)⟩

theorem h_lt_X (p : Fin 4 → ℕ) (v : Fin 10 → V) (hw : 0<v 5) : b p v<X p v := by
  have hqX : q p v≤X p v := by
    change q p v≤v 5*q p v
    exact le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp hw)
  exact lt_of_lt_of_le (show b p v<q p v from lt_add_one _) hqX

theorem half_rank_ge_fifteen (R r : V) (hR : 32≤R) (hr : R=2*r+1) : 15≤r := by
  have hmul : (2:V)*15≤2*r := by
    apply (add_le_add_iff_right (1:V)).mp
    calc
      2*15+1≤32 := by norm_num
      _≤R := hR
      _=2*r+1 := hr
  exact le_of_mul_le_mul_left hmul (by norm_num : (0:V)<2)

#print axioms TenPositive80RankLower.rank_ge_radix
#print axioms TenPositive80RankLower.graph_rank_lower
#print axioms TenPositive80RankLower.h_lt_X
#print axioms TenPositive80RankLower.half_rank_ge_fifteen
end TenPositive80RankLower
