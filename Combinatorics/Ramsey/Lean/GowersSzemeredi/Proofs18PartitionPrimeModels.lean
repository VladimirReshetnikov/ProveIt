import GowersSzemeredi.Proofs17NonuniformCellMass
import GowersSzemeredi.Proofs18PrimeCubeModel

/-! Prime models for a positive mass of nonuniform partition cells. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

/-- A positive mass of short cells has obstructions in comparable prime
models, all at a single parameter independent of the cell and old modulus. -/
theorem partition_nonuniformity_prime_models {N K k m : Nat} [NeZero N] [Fact N.Prime]
    (f : ZMod N → Complex) (Q : Fin K → ModAP N) (beta : Real)
    (hf : DiscValued f) (hβ : 0 ≤ beta) (hm : 0 < m)
    (hpart : IsPartition (fun i => (Q i).carrier) Finset.univ)
    (hproper : ∀ i, (Q i).IsProper)
    (hlength : ∀ i, 2 ≤ (Q i).length ∧ (Q i).length ≤ m ∧ (k + 2) * (Q i).length ≤ N)
    (hfail : ¬ UniformOnPartition f k beta Q m) :
    ∃ B : Finset (Fin K),
      beta / 2 * N < ∑ i ∈ B, ((Q i).carrier.card : Real) ∧
      ∀ i ∈ B, ∃ M : Nat, ∃ hM : M.Prime,
        letI : NeZero M := ⟨hM.ne_zero⟩
        (k + 2) * (Q i).length < M ∧ M ≤ 2 * ((k + 2) * (Q i).length) ∧
        DiscValued (intervalExtension M ((Q i).pullbackFunction f)) ∧
        ¬ UniformOfDegree (intervalExtension M ((Q i).pullbackFunction f))
          ((beta / 2) / (2 * (k + 2 : Nat) : Real) ^ (k + 2)) k := by
  have hsize i : (Q i).carrier.card ≤ m := by
    rw [hproper i]
    exact (hlength i).2.1
  obtain ⟨B, hmass, hB⟩ := not_uniformOnPartition_nonuniform_cell_mass f Q beta
    hf hβ hm hpart hsize hfail
  refine ⟨B, hmass, fun i hi => ?_⟩
  exact (Q i).exists_prime_model_of_nonuniform f (beta / 2) (m : Real)
    (hproper i) (hlength i).1 (hlength i).2.2 hf (by positivity)
    (by exact_mod_cast (hlength i).2.1) (hB i hi)

end LeanProofs.GowersSzemeredi
