import GowersSzemeredi.Proofs16SupportedHigherArrangementCount

/-! The concrete higher family projects into the supported additive
anchor quadruples and supported additive eight-column tuples. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def supportedColumnTuples {N : Nat} (W : Finset (ZMod N)) : Finset (Fin 8 → ZMod N) :=
  (Fintype.piFinset fun _ : Fin 8 => W).filter fun v =>
    (v 0-v 1)+(v 2-v 3) = (v 4-v 5)+(v 6-v 7)

theorem supported_higher_anchor_quadruple_mem {N : Nat} [NeZero N]
    (W : Finset (ZMod N)) {p : HigherArrangementParameter N}
    (hp : p ∈ supportedHigherArrangements W) (j : Fin 4) :
    higherArrangementAnchorQuadruple p j ∈ supportedAnchorQuadruples W := by
  have hm := (Finset.mem_filter.mp hp).2
  refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_,higherArrangementAnchorQuadruple_additive p j⟩
  intro i
  fin_cases i <;> dsimp [higherArrangementAnchorQuadruple,higherArrangementEndpointPair] <;> exact hm _

theorem supported_higher_column_tuples_mem {N : Nat} [NeZero N]
    (W : Finset (ZMod N)) {p : HigherArrangementParameter N}
    (hp : p ∈ supportedHigherArrangements W) :
    higherArrangementLeftColumns p ∈ supportedColumnTuples W ∧
      higherArrangementRightColumns p ∈ supportedColumnTuples W := by
  have hm := (Finset.mem_filter.mp hp).2
  constructor
  · refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => hm (Fin.castAdd 8 i)),?_⟩
    dsimp [higherArrangementLeftColumns,higherArrangementEndpoints]
    ring
  · refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => hm (Fin.natAdd 8 i)),?_⟩
    dsimp [higherArrangementRightColumns,higherArrangementEndpoints]
    ring

end LeanProofs.GowersSzemeredi
