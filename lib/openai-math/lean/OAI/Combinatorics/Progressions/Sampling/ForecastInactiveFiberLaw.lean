import OAI.Combinatorics.Progressions.Probability.PrincipalSupportedUnitBlockLaw

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable (degree : D → ℕ)
variable (L : PrincipalTupleIndex B (fun a => degree a + 1) → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (fun a => degree a + 1) → Option α → ZMod q) (a : D)
variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ L ⟨a, b, v⟩)
variable (hcell : 0 < (principalTupleWeights (α := α) B (fun a => degree a + 1) L hL).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

include hcell in

theorem forecastInactive_fiber_image
    (rows : Finset (Finset α)) (shift z : rows → ℤ) :
    (principalTupleWeights (α := α) B (fun a => degree a + 1) L hL).fiberMean (principalResidueLabel q) r
      (fun y => if (shift + ∑ b, fun t : rows => integerBooleanBlockJet
        (fun v k => (y ⟨a, b, v⟩ k : ℤ)) t) = z then 1 else 0) =
      (principalTupleWeights (α := α) B (fun a => degree a + 1) L hL).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r)) * finiteImageMass (weightedCubeIntegerSource (principalSupportedAxisSources B (fun a => degree a + 1) L hL q hq r a hsize))
        (weightedCubeIntegerJetSum (principalSupportedAxisSources B (fun a => degree a + 1) L hL q hq r a hsize) rows shift) z := by
  rw [FiniteProbabilityWeights.fiberMean_eq_mass_mul_condition _ _ _ _ hcell]
  congr 1
  change finiteImageMass ((principalTupleWeights (α := α) B (fun a => degree a + 1) L hL).condition (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell)
    (fun y => shift + ∑ b, fun t : rows => integerBooleanBlockJet
      (fun v k => (y ⟨a, b, v⟩ k : ℤ)) t) z = _
  rw [finiteImageMass_eq_toPMF, finiteImageMass_eq_toPMF]
  have heq := principalSupportedResidue_unit_block_law B (fun a => degree a + 1) L hL q hq r a hsize hcell rows shift
  exact congrArg (fun p : PMF (rows → ℤ) => (p z).toReal) heq.symm

theorem forecastInactive_fiber_image_all
    (rows : Finset (Finset α)) (shift z : rows → ℤ) :
    (principalTupleWeights (α := α) B (fun a => degree a + 1) L hL).fiberMean (principalResidueLabel q) r
      (fun y => if (shift + ∑ b, fun t : rows => integerBooleanBlockJet
        (fun v k => (y ⟨a, b, v⟩ k : ℤ)) t) = z then 1 else 0) =
      (principalTupleWeights (α := α) B (fun a => degree a + 1) L hL).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)) *
        finiteImageMass (weightedCubeIntegerSource
          (principalSupportedAxisSources B (fun a => degree a + 1) L hL q hq r a hsize))
          (weightedCubeIntegerJetSum
            (principalSupportedAxisSources B (fun a => degree a + 1) L hL q hq r a hsize) rows shift) z := by
  let p := principalTupleWeights (α := α) B (fun a => degree a + 1) L hL
  let cell : Finset (PrincipalIntegerTuples B (fun a => degree a + 1) α L) :=
    Finset.univ.filter (fun y => principalResidueLabel q y = r)
  by_cases hc : 0 < p.mass cell
  · exact forecastInactive_fiber_image B degree L hL q hq r a hsize hc rows shift z
  · have hz : p.mass cell = 0 := le_antisymm (le_of_not_gt hc) (p.mass_nonneg _)
    change p.fiberMean _ _ _ = p.mass cell * _
    rw [hz, zero_mul]
    simpa only [FiniteProbabilityWeights.fiberMean, cell, Finset.mem_filter,
      Finset.mem_univ, true_and] using p.mean_mask_zero cell hz
        (fun y => if (shift + ∑ b, fun t : rows => integerBooleanBlockJet
          (fun v k => (y ⟨a, b, v⟩ k : ℤ)) t) = z then 1 else 0)

omit [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] in

theorem forecastInactive_fiber_kernel
    {Ω Z R : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq R]
    (p : FiniteProbabilityWeights Ω) (residue : Ω → R) (r : R)
    (hr : 0 < p.mass (Finset.univ.filter (fun x => residue x = r)))
    (kernel : Ω → PMF Z) (z : Z) :
    p.fiberMean residue r (fun x => (kernel x z).toReal) =
      p.mass (Finset.univ.filter (fun x => residue x = r)) *
        (((p.condition (Finset.univ.filter (fun x => residue x = r)) hr).toPMF.bind kernel) z).toReal := by
  rw [FiniteProbabilityWeights.fiberMean_eq_mass_mul_condition _ _ _ _ hr,
    FiniteProbabilityWeights.toPMF_bind_toReal]

end Erdos3

end

end OAI
