import DiophantineConsistency.FreeJPowerFinish
import DiophantineConsistency.FreeJPopulationFactsNarrow
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJPopulationClient
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticPellRecurrence ArithmeticAdaptiveFirstDivisibility2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Conditional graph client: the compact port tuple and radix must still be
identified separately. The beta bound is needed by graph_power. -/
theorem graph_population (p : Fin 4 → ℕ) (v : Fin 12 → V) (h : V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v)
    (hbeta : (46:V)≤(p 0:V)) (hq : 1+v 0*(p 0:V)=Exp.exp h) :
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    3*h+2≤ArithmeticBinaryPopulation.population R := by
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  change 3*h+2≤ArithmeticBinaryPopulation.population R
  have hq16 : 16≤q := by
    have hm : (p 0:V)≤v 0*(p 0:V) :=
      le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp (hv 0))
    exact le_trans (le_trans (by norm_num : (16:V)≤46) hbeta)
      (le_trans hm (by dsimp [q]; simp))
  have hx : v 5=Exp.exp R := FreeJPowerFinish.graph_power p v hb hl hh hv hz hbeta
  obtain ⟨s,hs⟩ := FreeJRootBinding.first_factor_forces_Y_divisible p v hz (hv 0) hb
  have hy : ∃s:V, v 6=q^3*s := by
    refine ⟨s,?_⟩
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using hs
  obtain ⟨first,main,j,pi,_,_,hj13,_,hpiR,hjR,_,hjy,_,hpy⟩ :=
    FreeJExactOrdinary.exact_ordinary_indices p v hb hl hh hv hz
  change pi=R at hpiR
  change ycoord pi (v 5*v 6+v 6)=v 8+v 6*(v 8+v 9) at hpy
  have hRy : ycoord R (v 5*v 6+v 6)=v 8+v 6*(v 8+v 9) := by
    rw [←hpiR]; exact hpy
  exact FreeJPopulationFacts.population_of_ordinary_facts q (v 1) (v 2) (v 0) (p 2:V) (p 3:V)
    (v 5) (v 6) (v 8) (v 9) h R j hq16 (hv 2) hq rfl hy hx (hv 6) (hv 8) (hv 9)
    hj13 hjR hjy hRy
end FreeJPopulationClient
#print axioms FreeJPopulationClient.graph_population
