import DiophantineConsistency.Compact44.DirectMainComparison
import DiophantineConsistency.Compact44.DirectMainGapBalance
import DiophantineConsistency.Compact44.DirectMainGrowthAlgebra
import DiophantineConsistency.Compact44.DirectMainPellGrowth

/-! The direct witness gap from positive graph zeros and bounded ports. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectMainGap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJDirectMainGraph
open AdaptiveEquationSyntax2011 ArithmeticPellRecurrence ArithmeticPellPowerRecovery
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_gap (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (DirectMainFirst.integerPorts p)).output v) :
    v 5<v 11 := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let U : V := Y*(q*q)
  let k : V := v 8+v 9
  let c : V := v 8+Y*k
  let a : V := X*Y+Y
  let H : V := 3+4*a
  let Q : V := (X*Y)*Y
  let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
  have hb0 : 0<b := mul_pos (hv 0) hb
  have hb1 : 1≤b := pos_iff_one_le.mp hb0
  have hq2 : 2≤q := by
    dsimp [q]
    calc
      (2:V)=1+1 := by norm_num
      _≤1+b := by simpa only [add_comm] using add_le_add_left hb1 1
  have hq : 0<q := lt_of_lt_of_le (by simp : (0:V)<2) hq2
  have hq1 : 1≤q := le_trans (by norm_num : (1:V)≤2) hq2
  have hs : 1≤v 6 := pos_iff_one_le.mp (hv 6)
  have hq2sq : 4≤q*q := by
    have h := mul_le_mul hq2 hq2 (by simp : (0:V)≤2) (by simp : (0:V)≤q)
    norm_num at h ⊢
    exact h
  have hq3 : 8≤q*(q*q) := by
    have h := mul_le_mul hq2 hq2sq (by simp : (0:V)≤4) (by simp : (0:V)≤q)
    norm_num at h ⊢
    exact h
  have hY : 8≤Y := le_trans hq3 (le_mul_of_one_le_right (by simp) hs)
  have hX : 0<X := mul_pos hq (hv 5)
  have hX1 : 1≤X := pos_iff_one_le.mp hX
  have hwX : v 5≤X := by
    dsimp [X]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hq1 (show (0:V)≤v 5 by simp)
  have hU : 0<U := mul_pos (lt_of_lt_of_le (by simp : (0:V)<8) hY) (mul_pos hq hq)
  have hQ : 0<Q := mul_pos (mul_pos hX (lt_of_lt_of_le (by simp : (0:V)<8) hY)) (lt_of_lt_of_le (by simp : (0:V)<8) hY)
  obtain ⟨first,main,n,m,hfirst,hmain,hn13,hnm,hm14,hhalf,hnk,hmc,hnx,hny,hmx,hmy,hnmod,hnlow,hRk⟩ :=
    DirectMainComparison.comparison p v hb hl hh hv hz
  have hn3 : 3≤n := le_trans (by norm_num : (3:V)≤13) hn13
  have hk : Q*Q≤k := DirectMainPellGrowth.square_bound Q n k hQ hn3 hny
  have hgrowth : X+H*v 5<c :=
    DirectMainGrowthAlgebra.growth_of_square_bound X Y (v 5) k (v 8) hX1 hY hwX hk
  obtain ⟨first',main',n',m',hfirst',hmain',hbalance,hn',hm',hnk',hmc',hnx',hny',hmx',hmy'⟩ :=
    DirectMainIndices.graph_indices p v hb hv hz
  change ycoord m' a=c at hmy'
  change xcoord m' a=main' at hmx'
  have hmainbound : (a+1)*c<main' := by
    rw [←hmy',←hmx']
    exact x_gt a m'
  exact DirectMainGapBalance.gap_of_balance U X a c H (v 11) R k main' (v 5)
    hU hRk hbalance hmainbound hgrowth

#print axioms DirectMainGap.graph_gap
end DirectMainGap
