import DiophantineConsistency.Sign33CurrentFiveWitnesses
import DiophantineConsistency.Sign33CurrentWindows
import DiophantineConsistency.ModelThirteenCoreInvariants

/-! Bind the five checked source representatives to Carrier65 core values. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33CurrentCoreCuts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticCarrierRadix2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem five_core_representatives_of_current_zero (v : Fin 14 → V)
    (hz : ObjectCurrentEquation2011.InternalZero ObjectCurrentEquation2011.naturalExpression v) :
    let w : Fin 14 → V := fun j => v j+1
    let d := Carrier65.core (ModelThirteenCarrier.ringPorts (V := V)) (fun j => ι (w j))
    ∃ gap tau inner val negative : V,
      ι gap = (d.q-1)*(d.q-ι (w 1))+ι (w 2) ∧
      ι tau = d.tau ∧
      ι inner = d.c*ι (w 6)-d.rank ∧
      ι val = d.V ∧
      ι negative = d.y*d.y-d.V*d.V := by
  dsimp only
  let w : Fin 14 → V := fun j => v j+1
  let d := Carrier65.core (ModelThirteenCarrier.ringPorts (V := V)) (fun j => ι (w j))
  have hwin := Sign33CurrentWindows.windows_of_current_zero v hz
  have hgap : 0<q w-w 1-w 2 := hwin.1
  have ha : w 2 < q w-w 1 := tsub_pos_iff_lt.mp hgap
  have hFq : w 1 < q w := tsub_pos_iff_lt.mp (lt_of_le_of_lt _root_.zero_le ha)
  obtain ⟨eq_q, _, eq_E, _, eq_c, _, eq_rank⟩ := ModelThirteenCarrier.core_invariants w hFq
  have hfive := Sign33CurrentFiveWitnesses.five_witnesses_of_current_zero v hz
  change ∃ gap tau inner val negative : V,
    ι gap = (ι (q w)-1)*(ι (q w)-ι (w 1))+ι (w 2) ∧
    ι tau = ι (X w*Y w)*ι (w 9)+ι (w 10+w 11)-ι (rank w) ∧
    ι inner = ι ((w 10+w 11)*Y w+w 10)*ι (w 6)-ι (rank w) ∧
    ι val = ι (w 4)*ι (w 4)*(ι ((w 10+w 11)*Y w+w 10)*ι (w 6)-ι (rank w))-ι ((w 10+w 11)*Y w+w 10) ∧
    ι negative = ι (w 12)*ι (w 12)-
      (ι (w 4*w 4*((w 10+w 11)*Y w+w 10)*w 6)-ι (w 4*w 4*rank w+((w 10+w 11)*Y w+w 10)))*
      (ι (w 4*w 4*((w 10+w 11)*Y w+w 10)*w 6)-ι (w 4*w 4*rank w+((w 10+w 11)*Y w+w 10))) at hfive
  obtain ⟨gap,tau,inner,val,negative,hgap',htau,hinner,hval,hnegative⟩ := hfive
  have etau : d.tau = ι (X w*Y w)*ι (w 9)+ι (w 10+w 11)-ι (rank w) := by
    change d.E*ι (w 9)+(ι (w 10)+ι (w 11))-d.rank = _
    rw [eq_E, eq_rank, map_add]
  have eV : d.V = ι (w 4)*ι (w 4)*(ι ((w 10+w 11)*Y w+w 10)*ι (w 6)-ι (rank w))-ι ((w 10+w 11)*Y w+w 10) := by
    change (ι (w 4))^2*(d.c*ι (w 6)-d.rank)-d.c = _
    rw [eq_c, eq_rank, pow_two]
  have ediff : ι (w 4*w 4*((w 10+w 11)*Y w+w 10)*w 6)-ι (w 4*w 4*rank w+((w 10+w 11)*Y w+w 10)) = d.V := by
    rw [eV]
    simp only [map_add, map_mul]
    ring
  refine ⟨gap,tau,inner,val,negative,?_,?_,?_,?_,?_⟩
  · simpa only [eq_q] using hgap'
  · exact htau.trans etau.symm
  · simpa only [eq_c, eq_rank] using hinner
  · exact hval.trans eV.symm
  · change ι negative = ι (w 12)*ι (w 12)-d.V*d.V
    simpa only [ediff] using hnegative
end DiophantineConsistency.Sign33CurrentCoreCuts
#print axioms DiophantineConsistency.Sign33CurrentCoreCuts.five_core_representatives_of_current_zero
