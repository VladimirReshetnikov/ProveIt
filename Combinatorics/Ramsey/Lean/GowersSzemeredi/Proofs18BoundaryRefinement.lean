import GowersSzemeredi.Proofs05VariablePhaseRefinement
import GowersSzemeredi.Proofs18ExceptionalCellSelection

/-! Refining a progression partition into cells of small modular diameter,
while preserving discrepancy and a quantitative bound on the cell count. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Count constant for a modular-diameter tolerance epsilon*N. -/
def boundaryRefinementConstant (epsilon : Real) : Real :=
  section5LocalRefinementConstant 1 (4 * Real.pi * epsilon)

/-- A proper progression has a small-diameter refinement with a sublinear
cell count, including the short-progression and empty cases. -/
theorem ModAP.small_diameter_refinement {N : Nat} [NeZero N]
    (P : ModAP N) (hP : P.IsProper) (epsilon : Real) (hε : 0 < epsilon) :
    ∃ L : Nat, ∃ R : Fin L → ModAP N,
      IsPartition (fun j ↦ (R j).carrier) P.carrier ∧
      (∀ j, (R j).IsProper) ∧
      (L : Real) ≤ boundaryRefinementConstant epsilon * (P.carrier.card : Real) ^ (15 / 16 : Real) ∧
      ∀ j, diameterAtMostReal (R j).carrier (epsilon * N) := by
  have hid : PolynomialOn 1 Finset.univ (id : ZMod N → ZMod N) := by
    refine ⟨![0, 1], fun x _ ↦ ?_⟩
    simp [Fin.sum_univ_two]
  obtain ⟨L, R, hpart, hproper, hcount, hdiam⟩ :=
    section5_efficient_diameter_refinement_of_corollary_5_6 corollary_5_6_holds
      P id (4 * Real.pi * epsilon) hP (by omega) hid (by positivity)
  have hK : (1 : Real) - (polynomialPartitionConstant 1 : Real)⁻¹ = 15 / 16 := by
    norm_num [polynomialPartitionConstant, Nat.factorial]
  have hscale : 4 * Real.pi * epsilon * N / (4 * Real.pi) = epsilon * N := by
    field_simp
  refine ⟨L, R, hpart, hproper, ?_, ?_⟩
  · simpa only [boundaryRefinementConstant, hK] using hcount
  · intro j
    simpa only [Finset.image_id, hscale] using hdiam j

/-- A global small-diameter refinement preserves the total discrepancy of
every function, and retains the usual Jensen cell-count exponent. -/
theorem small_diameter_partition_refinement {N M : Nat} [NeZero N]
    (Q : Fin M → ModAP N) (epsilon : Real) (hε : 0 < epsilon)
    (hQ : IsPartition (fun i ↦ (Q i).carrier) Finset.univ)
    (hproper : ∀ i, (Q i).IsProper) :
    ∃ L : Nat, ∃ R : Fin L → ModAP N,
      IsPartition (fun j ↦ (R j).carrier) Finset.univ ∧
      IsRefinement (fun j ↦ (R j).carrier) (fun i ↦ (Q i).carrier) ∧
      (∀ j, (R j).IsProper) ∧
      (L : Real) ≤ boundaryRefinementConstant epsilon * (M : Real) ^ (1 / 16 : Real) *
        (N : Real) ^ (15 / 16 : Real) ∧
      (∀ j, diameterAtMostReal (R j).carrier (epsilon * N)) ∧
      ∀ f : ZMod N → Complex,
        (∑ i, ‖∑ x ∈ (Q i).carrier, f x‖) ≤ ∑ j, ‖∑ x ∈ (R j).carrier, f x‖ := by
  classical
  have hM := section18_partition_index_nonempty (fun i ↦ (Q i).carrier) hQ
  choose L R hpart hRproper hcount hdiam using fun i ↦ (Q i).small_diameter_refinement (hproper i) epsilon hε
  refine ⟨∑ i, L i, section5Flatten L R, section5Flatten_partition Q L R hQ hpart,
    section5Flatten_refinement Q L R hQ hpart, section5Flatten_isProper L R hRproper, ?_, ?_, ?_⟩
  · have hcards : ∑ i, (Q i).carrier.card = N := by simpa using hQ.sum_card
    have hjensen := section5_sum_rpow_le hM (by omega : 0 < 16) (fun i ↦ (Q i).carrier.card) hcards
    norm_num only [Nat.cast_ofNat] at hjensen
    rw [Nat.cast_sum]
    calc
      _ ≤ ∑ i, boundaryRefinementConstant epsilon * ((Q i).carrier.card : Real) ^ (15 / 16 : Real) :=
        Finset.sum_le_sum fun i _ ↦ hcount i
      _ = boundaryRefinementConstant epsilon *
          ∑ i, ((Q i).carrier.card : Real) ^ (15 / 16 : Real) := (Finset.mul_sum _ _ _).symm
      _ ≤ boundaryRefinementConstant epsilon *
          ((M : Real) ^ (1 / 16 : Real) * (N : Real) ^ (15 / 16 : Real)) := by
        apply mul_le_mul_of_nonneg_left _ (section5LocalRefinementConstant_pos _ _).le
        simpa only [one_div] using hjensen
      _ = _ := by ring
  · intro j
    let z := (section5FlattenEquiv L).symm j
    exact hdiam z.1 z.2
  · intro f
    rw [section5Flatten_sum L R (fun P ↦ ‖∑ x ∈ P.carrier, f x‖)]
    apply Finset.sum_le_sum
    intro i _
    rw [← (hpart i).sum_weights f]
    exact norm_sum_le _ _

end LeanProofs.GowersSzemeredi
