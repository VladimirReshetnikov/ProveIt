import Direct80GrowthWitness
import Direct80Size
import Direct80IndexAlignment

/-! The exact 80 graph rank is below the internal Y power bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80PowerBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank TenPositive80RankExact TenPositive80IndexAlignment
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_power_bound (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hbeta15 : (15:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v)
    (hbetaodd : ∃u : V, (p 0:V)=2*u+1) : Exp.exp (rankNat p v)<Y p v := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<15) hbeta15
  have hX := Direct80Size.x_lower p v hbeta15 hv
  obtain ⟨n,hn,hnR,hrel,hny,hc⟩ := graph_first_main_alignment p v hb hl hh hv hz hbetaodd
  have hR : 24≤rankNat p v := (graph_rank_exact p v hb hl hh hv hz).1
  have hn3 : 3≤n := by
    by_contra hn3
    have hnlt : n<3 := lt_of_not_ge hn3
    have hnplus : n+1≤2+1 := by
      simpa only [show (2:V)+1=3 by ring] using lt_iff_succ_le.mp hnlt
    have hnle : n≤2 := (add_le_add_iff_right (1:V)).mp hnplus
    have h2n : 2*n≤4 := by
      simpa only [show (2:V)*2=4 by ring] using mul_le_mul_of_nonneg_left hnle (show (0:V)≤2 by simp)
    have h25 : (25:V)≤rankNat p v+1 := by
      simpa only [add_comm,show (1:V)+24=25 by ring,show (24:V)+1=25 by ring] using add_le_add_right hR (1:V)
    have hbad : (25:V)≤4 := le_trans h25 (by rw [←hrel]; exact h2n)
    norm_num at hbad
  exact Direct80GrowthWitness.growth_of_witnesses p v n (rankNat p v) hb hv hX hn3 hrel.symm hny hc

#print axioms Direct80PowerBound.graph_power_bound
end Direct80PowerBound
