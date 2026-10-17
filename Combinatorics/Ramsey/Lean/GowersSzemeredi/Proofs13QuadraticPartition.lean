import GowersSzemeredi.Proofs13EndpointDeletion
import GowersSzemeredi.Proofs05FullPartition
import GowersSzemeredi.Proofs05Downstream

/-! Weighted quadratic partitioning before endpoint deletion.

`lemma_13_5_with_scale` is in `Proofs13QuadraticPartitionSide`, outside the
final route. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- A finite partition preserves arbitrary additive weights. -/
theorem IsPartition.sum_weights {X A : Type*} [DecidableEq X] [AddCommMonoid A]
    {M : Nat} {P : Fin M → Finset X} {S : Finset X}
    (hP : IsPartition P S) (w : X → A) :
    ∑ i, ∑ x ∈ P i, w x = ∑ x ∈ S, w x := by
  have hu : Finset.univ.biUnion P = S := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact (hP.1 x).symm
  rw [← hu, Finset.sum_biUnion]
  intro i _ j _ hij
  exact hP.2 i j (bne_iff_ne.mpr hij)

/-- Good-height weight is an ordinary nonnegative point weight, so it is
preserved when a progression is partitioned. -/
theorem stage135_partition_good_weight {N M : Nat} [NeZero N]
    (S : Section13Context N) (H : Finset (ZMod N)) (P : ModAP N)
    (Q : Fin M → ModAP N)
    (hpart : IsPartition (fun j => (Q j).carrier) P.carrier) :
    ∑ j, goodHeightWeight S ((Q j).carrier ∩ H) = goodHeightWeight S (P.carrier ∩ H) := by
  classical
  let w := fun h => if h ∈ H ∧ IsGoodHeight S h then section13C S h else 0
  have hw (A : Finset (ZMod N)) : goodHeightWeight S (A ∩ H) = ∑ h ∈ A, w h := by
    have hf : ((A ∩ H).filter (IsGoodHeight S)) =
        A.filter (fun h => h ∈ H ∧ IsGoodHeight S h) := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_inter]
      tauto
    unfold goodHeightWeight
    rw [hf, Finset.sum_filter]
  simp_rw [hw]
  exact hpart.sum_weights w

/-- Select a cell with at least the initial average good-height weight. -/
theorem stage135_select_weighted_cell {N M : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (Q : Fin M → ModAP N)
    (hM : 0 < M) (hP : D.P.IsProper) (hH : D.H ⊆ D.P.carrier)
    (hpart : IsPartition (fun j => (Q j).carrier) D.P.carrier)
    (hproper : ∀ j, (Q j).IsProper)
    (hweight : S.alpha ^ 32 * (N : Real) ^ 31 * D.P.length / 8 ≤
      (goodHeightWeight S D.H : Real)) :
    ∃ j, S.alpha ^ 32 * (N : Real) ^ 31 * (Q j).length / 8 ≤
      (goodHeightWeight S ((Q j).carrier ∩ D.H) : Real) := by
  have hsum : ∑ j, S.alpha ^ 32 * (N : Real) ^ 31 * (Q j).length / 8 ≤
      ∑ j, (goodHeightWeight S ((Q j).carrier ∩ D.H) : Real) := by
    have hl : ∑ j, (Q j).length = D.P.length := by
      have hcards : ∀ j, (Q j).carrier.card = (Q j).length := hproper
      simpa only [hcards, show D.P.carrier.card = D.P.length from hP] using hpart.sum_card
    have hw := stage135_partition_good_weight S D.H D.P Q hpart
    rw [Finset.inter_eq_right.mpr hH] at hw
    have hlR : ∑ j, ((Q j).length : Real) = (D.P.length : Real) := by exact_mod_cast hl
    have hwR : ∑ j, (goodHeightWeight S ((Q j).carrier ∩ D.H) : Real) =
        (goodHeightWeight S D.H : Real) := by exact_mod_cast hw
    rw [hwR, ← Finset.sum_div, ← Finset.mul_sum, hlR]
    exact hweight
  obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le
    (show (Finset.univ : Finset (Fin M)).Nonempty from ⟨⟨0, hM⟩, Finset.mem_univ _⟩) hsum
  exact ⟨j, hj⟩

end LeanProofs.GowersSzemeredi
