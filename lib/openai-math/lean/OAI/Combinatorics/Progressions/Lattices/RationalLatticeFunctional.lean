import OAI.Combinatorics.Progressions.Estimates.NativeCentralSeed

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem realLattice_functional_integral (η : L →ₗ[ℚ] ℚ)
    (hη : ∀ g : D.filtration.Group, g ∈ D.lattice → ∃ n : ℤ, η g.coord = n)
    (z : D.RealGroup) (hz : z ∈ D.realLattice) :
    ∃ n : ℤ, realifyFunctional η z.coord = n := by
  obtain ⟨g, hg, rfl⟩ := hz
  obtain ⟨n, hn⟩ := hη g hg
  refine ⟨n, ?_⟩
  change realifyFunctional η ((1 : ℝ) ⊗ₜ[ℚ] g.coord) = _
  rw [realifyFunctional_tmul, one_mul, hn, Rat.cast_intCast]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
