import Trace75SandwichBoth
import Trace75Repunit
import ScaledPellRounding
import DiophantineConsistency.ArithmeticHalfBinomial

/-! Population consequence at the same trace75 repunit length. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75Population
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticBinaryPopulation
open Trace75Factors Trace75Rank Trace75RankExact
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_population (p : Fin 4 → ℕ) (v : Fin 10 → V) (d : V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V))
    (hh : (p 3:V)<2*(p 0:V)) (hv : ∀j,0<v j)
    (hz : value75 (ports p) (fun j => ι (v j)) = 0)
    (hd : 2≤d) (hbeta : (p 0:V)+1=Exp.exp d) :
    ∃ N : V, 0<N ∧ v 0=ArithmeticRepunit.rep d N ∧
      3*(d*N)+2≤population (rankNat p v) := by
  obtain ⟨r,hr,hR,hX,hlow,hup⟩ := Trace75SandwichBoth.graph_sandwich_both p v hb31 hl hh hv hz
  obtain ⟨z,hbin⟩ := ScaledPellRounding.extract (X p v) (Y p v) r (v 8) (v 9)
    (k v) (c p v) hr hX rfl rfl (hv 8) (hv 9) hlow hup
  obtain ⟨N,hN,hj,hq,_,_⟩ := Trace75Repunit.graph_repunit p v d hb31 hl hh hv hz hd hbeta
  have hdvd : Exp.exp (3*(d*N))∣Y p v := by
    refine ⟨v 6,?_⟩
    dsimp [Y]
    rw [hq]
    rw [show 3*(d*N)=(d*N)+(d*N)+(d*N) by ring, exp_add, exp_add]
  have hqbound : d*N+1≤q p v := by rw [hq]; exact lt_iff_succ_le.mp (lt_exp (d*N))
  have hrank : 3*(d*N)+1≤2*r+1 := by
    rw [←hR]
    calc
      3*(d*N)+1≤3*(d*N+1) := by
        have he : 3*(d*N)+1+2=3*(d*N+1) := by ring
        rw [←he]; exact le_add_of_nonneg_right (by simp)
      _≤3*q p v := mul_le_mul_of_nonneg_left hqbound (by simp)
      _≤rankNat p v := (graph_rank_exact p v hb31 hl hh hv hz).2.1.le
  have hpop := ArithmeticHalfBinomial.population_lower (X p v) (Y p v) r z (d*N) hX hbin hdvd hrank
  exact ⟨N,hN,hj,by simpa only [hR] using hpop⟩

#print axioms Trace75Population.graph_population
end Trace75Population
