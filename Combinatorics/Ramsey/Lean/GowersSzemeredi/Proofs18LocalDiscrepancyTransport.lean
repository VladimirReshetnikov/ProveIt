import GowersSzemeredi.Proofs18FullIntervalDiscrepancy
import GowersSzemeredi.Proofs18PrimeCubeModel

/-! Complete local discrepancy partitions transport from a new prime model
back to the original progression, preserving the count and every cell sum. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

/-- Apply a function inverse bound in a sufficiently large prime model of
an index interval and transport its full ordinary partition back to the
original progression. The discrepancy lower bound has no boundary loss. -/
theorem FunctionDiscrepancyBound.progression_partition
    {degree N M : Nat} [NeZero N] [NeZero M] [Fact M.Prime]
    {alpha beta sigma T : Real}
    (hbound : FunctionDiscrepancyBound degree alpha beta sigma T)
    (P : ModAP N) (hP : P.IsProper) (hM : 4 ≤ M) (hL : P.length ≤ M) (hT : T ≤ M)
    (f : ZMod N → Complex) (hf : DiscValued f)
    (hnot : ¬ UniformOfDegree (intervalExtension M (P.pullbackFunction f)) alpha degree) :
    ∃ J : Nat, ∃ R : Fin J → ModAP N,
      IsPartition (fun j => (R j).carrier) P.carrier ∧ (∀ j, (R j).IsProper) ∧
      (J : Real) ≤ 2 * boundaryRefinementConstant (1 / 16) * (M : Real) ^ (1 - sigma / 16) ∧
      beta * M ≤ ∑ j, ‖∑ x ∈ (R j).carrier, f x‖ := by
  obtain ⟨J, R, hR, hRproper, hcount, hdis⟩ := hbound.full_interval_partition
    hM hL hT (intervalExtension M (P.pullbackFunction f))
    (intervalExtension_discValued M fun i => hf (P.index i)) (fun x hx => dif_neg (by omega)) hnot
  have hsub (j : Fin J) : (R j).carrier ⊆ Finset.range P.length := IsPartition.cell_subset hR j
  refine ⟨J, fun j => section5Transport P (R j), section5Transport_partition P R hP hR,
    fun j => section5Transport_isProper P (R j) hP (hRproper j) (hsub j), hcount,
    hdis.trans_eq (Finset.sum_congr rfl fun j _ => ?_)⟩
  rw [section5Transport_sum P (R j) hP (hsub j)]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  have htL : t < P.length := Finset.mem_range.mp (hsub j ht)
  simp only [intervalExtension, ZMod.val_natCast_of_lt (htL.trans_le hL), dif_pos htL,
    ModAP.pullbackFunction, ModAP.index, section5IndexPoint]

end LeanProofs.GowersSzemeredi
