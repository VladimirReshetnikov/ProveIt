import Direct80Repunit
import Direct80RankThree
import DiophantineConsistency.ArithmeticHalfBinomial

/-! Population consequence, conditional on the missing half-binomial witness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80PopulationConditional
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open ArithmeticBinomPascal ArithmeticBinaryPopulation
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_population_of_half_binomial (p : Fin 4 → ℕ) (v : Fin 10 → V) (d r z : V)
    (hbeta31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v)
    (hbetaodd : ∃u : V, (p 0:V)=2*u+1) (hd : 2≤d)
    (hbeta : (p 0:V)+1=Exp.exp d) (hr : rankNat p v=2*r+1)
    (hbin : 2*Y p v=binom (2*r) r+z*X p v) :
    ∃ N : V, 0<N ∧ v 0=ArithmeticRepunit.rep d N ∧
      3*(d*N)+2≤population (rankNat p v) := by
  obtain ⟨N,hN,hj,hq,_,_⟩ :=
    Direct80Repunit.graph_repunit p v d hbeta31 hl hh hv hz hbetaodd hd hbeta
  have hpow : X p v=Exp.exp (2*r+1) := by
    rw [←hr]
    exact Direct80GraphPower.graph_power p v hbeta31 hl hh hv hz hbetaodd
  have hdvd : Exp.exp (3*(d*N))∣Y p v := by
    refine ⟨v 6,?_⟩
    dsimp [Y]
    rw [hq]
    rw [show 3*(d*N)=(d*N)+(d*N)+(d*N) by ring, exp_add, exp_add]
  have hqbound : d*N+1≤q p v := by rw [hq]; exact lt_iff_succ_le.mp (lt_exp (d*N))
  have hrank : 3*(d*N)+1≤2*r+1 := by
    rw [←hr]
    calc
      3*(d*N)+1≤3*(d*N+1) := by
        have he : 3*(d*N)+1+2=3*(d*N+1) := by ring
        rw [←he]; exact le_add_of_nonneg_right (by simp)
      _≤3*q p v := mul_le_mul_of_nonneg_left hqbound (by simp)
      _≤rankNat p v := (Direct80RankThree.graph_rank_gt_three_q p v hbeta31 hv hz).le
  have hpop := ArithmeticHalfBinomial.population_lower (X p v) (Y p v) r z (d*N) hpow hbin hdvd hrank
  exact ⟨N,hN,hj,by simpa only [hr] using hpop⟩

#print axioms Direct80PopulationConditional.graph_population_of_half_binomial
end Direct80PopulationConditional
