import GowersSzemeredi.Proofs16WeightedGraphSums
import GowersSzemeredi.Proofs16RetiledRecurrence

/-! Genuine unit product property on a partial-domain slab. Small graph
pair-sum support can supply the property even for an arbitrary value word;
full-domain multilinear rigidity cannot be applied to this situation.

`section16_slab_unit_product` is in `Proofs16SlabProductPropertySide`, outside
the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Pointwise
namespace LeanProofs.GowersSzemeredi

/-- A graph with at most N possible pair sums has the unit weighted-energy
bound, for any number of identical parallel restrictions. -/
theorem section16_weighted_graph_sum_bound {N p : Nat} [NeZero N]
    (A S E : Finset (ZMod N)) (f : ZMod N → ZMod N) (w : ZMod N → Real)
    (hEA : E ⊆ A) (hf : ∀ x ∈ A, f x ∈ S)
    (hsize : (A + A).card * (S + S).card ≤ N) :
    (N : Real)⁻¹ * (∑ x ∈ E, w x) ^ 4 ≤
      weightedSimultaneousAdditiveEnergy E w (fun _ : Fin p => f) := by
  let T : Finset (ZMod N × (Fin p → ZMod N)) :=
    ((A + A) ×ˢ (S + S)).image (fun z => (z.1, fun _ => z.2))
  have hT : T.card ≤ N := Finset.card_image_le.trans (by simpa only [Finset.card_product] using hsize)
  have h := weightedSimultaneousAdditiveEnergy_support_bound E w (fun _ : Fin p => f) T
    (M := (N : Real)) (fun a ha b hb => ?_) (by exact_mod_cast hT)
  · exact (inv_mul_le_iff₀ (by exact_mod_cast NeZero.pos N : (0 : Real) < N)).mpr h
  · exact Finset.mem_image.mpr ⟨(a + b, f a + f b), Finset.mem_product.mpr
      ⟨Finset.add_mem_add (hEA ha) (hEA hb), Finset.add_mem_add (hf a (hEA ha)) (hf b (hEA hb))⟩, rfl⟩

/-- Ordinary additive energy is the zero-valued graph case, for arbitrary
real weights and arbitrary parallel-family size. -/
theorem section16_zero_parallel_energy {N p : Nat} [NeZero N]
    (E : Finset (ZMod N)) (w : ZMod N → Real) :
    (N : Real)⁻¹ * (∑ x ∈ E, w x) ^ 4 ≤
      weightedSimultaneousAdditiveEnergy E w (fun _ : Fin p => fun _ => 0) := by
  apply section16_weighted_graph_sum_bound Finset.univ {0} E (fun _ => 0) w
    (Finset.subset_univ _) (by simp)
  simp only [Finset.singleton_add_singleton, zero_add, Finset.card_singleton, Nat.mul_one]
  exact (Finset.card_le_univ _).trans (ZMod.card N).le

/-- Constant parallel maps impose no constraint beyond ordinary additive
energy. Their constants may differ from one restriction to another. -/
theorem weightedSimultaneousAdditiveEnergy_constants {N p : Nat} [NeZero N]
    (E : Finset (ZMod N)) (w : ZMod N → Real) (c : Fin p → ZMod N) :
    weightedSimultaneousAdditiveEnergy E w (fun i _ => c i) =
      weightedSimultaneousAdditiveEnergy E w (fun _ : Fin p => fun _ => 0) := by
  unfold weightedSimultaneousAdditiveEnergy
  simp [IsAdditiveQuadruple]

end LeanProofs.GowersSzemeredi
