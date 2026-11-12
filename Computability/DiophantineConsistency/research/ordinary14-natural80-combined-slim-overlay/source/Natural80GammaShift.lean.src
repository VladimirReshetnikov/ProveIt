import Natural80GammaClient
import P81NaturalForcedJ

/-! Source-only 80-to-81 gamma shift. The positivity client, ring identity,
model transport and all their dependencies are unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.Natural80GammaShiftDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open Natural80GammaClientDraft

def down81 {R : Type*} [Sub R] [One R] (v : Fin 14 → R) : Fin 14 → R :=
  fun j => if j = 12 then v j - 1 else v j

/-- Ring identity at a shifted gamma coordinate, not at the same valuation. -/
theorem output_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P80NaturalForcedGamma.graph p).output.evalRing v =
      (P81NaturalForcedJ.graph p).output.evalRing (down81 v) := by
  simp [P80NaturalForcedGamma.graph, P81NaturalForcedJ.graph, Expr.evalRing_add,
    Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant,
    Expr.evalRing_ofNat, down81]

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def Related (v80 v81 : Fin 14 → V) : Prop :=
  v80 12=v81 12+1 ∧ ∀ j, j≠12 → v80 j=v81 j
def lift (v : Fin 14 → V) : Fin 14 → V :=
  fun j => if j=12 then v j+1 else v j

theorem related_lift (v : Fin 14 → V) : Related (lift v) v := by
  constructor
  · simp [lift]
  · intro j hj; simp [lift,hj]

theorem related_embedding {v80 v81 : Fin 14 → V} (h : Related v80 v81) :
    down81 (fun j => ι (v80 j)) = (fun j => ι (v81 j)) := by
  funext j
  fin_cases j <;> simp_all [Related,down81,map_add,map_one]

theorem internalZero_iff_related (p : Fin 4 → ℤ) {v80 v81 : Fin 14 → V}
    (h : Related v80 v81) :
    InternalZero (P80NaturalForcedGamma.graph p).output v80 ↔
      InternalZero (P81NaturalForcedJ.graph p).output v81 := by
  rw [ModelDifferenceRing.internalZero_iff, ModelDifferenceRing.internalZero_iff,
    output_eval, related_embedding h]

/-- Proposed existential transfer with all represented ports and rank bounds
explicit; positive gamma is derived from the separate client. -/
theorem exists_zero_iff (p : Fin 4 → ℤ) (beta K MC MF : V)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hMC : (p 2 : DiffRing V)=ι MC) (hMF : (p 3 : DiffRing V)=ι MF)
    (hb : 0<beta) (hKpos : 0<K) (hMCbound : MC<beta) (hMFbound : MF<2*beta) :
    (∃ v, InternalZero (P80NaturalForcedGamma.graph p).output v) ↔
      ∃ w, InternalZero (P81NaturalForcedJ.graph p).output w := by
  constructor
  · rintro ⟨v,hv⟩
    have hg := gamma_pos_of_80_zero p beta K MC MF v hbeta hK hMC hMF hb hKpos hMCbound hMFbound hv
    obtain ⟨g,hg⟩ := exists_add_of_le (pos_iff_one_le.mp hg)
    let w : Fin 14 → V := fun t => if t=12 then g else v t
    have hw : Related v w := by
      constructor
      · simpa [w,add_comm] using hg
      · intro t ht; simp [w,ht]
    exact ⟨w,(internalZero_iff_related p hw).mp hv⟩
  · rintro ⟨w,hw⟩
    exact ⟨lift w,(internalZero_iff_related p (related_lift w)).mpr hw⟩

end DiophantineConsistency.Natural80GammaShiftDraft

#print axioms DiophantineConsistency.Natural80GammaShiftDraft.output_eval
#print axioms DiophantineConsistency.Natural80GammaShiftDraft.internalZero_iff_related
#print axioms DiophantineConsistency.Natural80GammaShiftDraft.exists_zero_iff
