import GowersSzemeredi.Proofs16WeightedGraphSums
import GowersSzemeredi.Proofs16RetiledRecurrence

/-! Genuine unit product property on a partial-domain slab. Small graph
pair-sum support can supply the property even for an arbitrary value word;
full-domain multilinear rigidity cannot be applied to this situation. -/
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
  classical
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
  classical
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
  classical
  unfold weightedSimultaneousAdditiveEnergy
  simp [IsAdditiveQuadruple]

/-- Arbitrary functions into S on a final-coordinate domain A have the
original weighted product property at gamma=1 when |A+A||S+S|<=N.
All parallel-family sizes, including zero, and all nonnegative weights
are included. This is a partial-domain theorem, with no primality premise. -/
theorem section16_slab_unit_product {N k : Nat} [NeZero N]
    (A S : Finset (ZMod N)) (f : ZMod N → ZMod N)
    (hf : ∀ x ∈ A, f x ∈ S) (hsize : (A + A).card * (S + S).card ≤ N) :
    HasProductProperty (lastProductSet (Finset.univ : Finset (Point N k)) A)
      (fun z => f (section16Last z)) 1 := by
  classical
  intro p j y E w _hw hE
  simp only [one_pow, one_mul]
  by_cases hj : j = Fin.last k
  · subst j
    by_cases hp : p = 0
    · subst p
      have heq : (fun i : Fin 0 => coordinateRestriction
          (fun z => f (section16Last z)) (y i) (Fin.last k)) = (fun _ : Fin 0 => fun _ => 0) := by
        funext i
        exact Fin.elim0 i
      rw [heq]
      exact section16_zero_parallel_energy E w
    · have hEA : E ⊆ A := by
        intro x hx
        have h := hE ⟨0, Nat.pos_of_ne_zero hp⟩ x hx
        simpa [lastProductSet, section16Last, replaceCoordinate] using h
      have heq : (fun i => coordinateRestriction (fun z => f (section16Last z)) (y i) (Fin.last k)) =
          (fun _ : Fin p => f) := by
        funext i x
        simp [coordinateRestriction, section16Last, replaceCoordinate]
      rw [heq]
      exact section16_weighted_graph_sum_bound A S E f w hEA hf hsize
  · have heq : (fun i => coordinateRestriction (fun z => f (section16Last z)) (y i) j) =
        (fun i : Fin p => fun _ => f (section16Last (y i))) := by
      funext i x
      simp [coordinateRestriction, section16Last, replaceCoordinate, Function.update_of_ne (Ne.symm hj)]
    rw [heq, weightedSimultaneousAdditiveEnergy_constants]
    exact section16_zero_parallel_energy E w

end LeanProofs.GowersSzemeredi
