import OAI.Combinatorics.Progressions.Estimates.EuclideanBallVolumeBound
import OAI.Combinatorics.Progressions.Lattices.EuclideanDerivativeLattice

namespace OAI

section

namespace Erdos3

open MeasureTheory Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem shortVectorLattice_covolume_le
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (R N : ℝ) (hR : 0 ≤ R) (hN : 0 < N)
    (P : Finset (shortVectorLattice Λ R))
    (hP : ∀ p ∈ P, ‖(p : shortVectorSpan Λ R)‖ ≤ R) (hcard : N ≤ (P.card : ℝ)) :
    ZLattice.covolume (shortVectorLattice Λ R) ≤
      (((finrank ℝ (shortVectorSpan Λ R) : ℝ) + 2) * R) ^
        finrank ℝ (shortVectorSpan Λ R) / N := by
  let d := finrank ℝ (shortVectorSpan Λ R)
  have hpack := shortVectorLattice_covolume_packing Λ R P hP
  have hvol := euclidean_closedBall_volume_le (E := shortVectorSpan Λ R)
    (R + (d : ℝ) * R / 2) (by positivity)
  have he : 2 * (R + (d : ℝ) * R / 2) = ((d : ℝ) + 2) * R := by ring
  rw [he] at hvol
  have hcov : 0 ≤ ZLattice.covolume (shortVectorLattice Λ R) :=
    (ZLattice.covolume_pos (shortVectorLattice Λ R) volume).le
  apply (le_div_iff₀ hN).mpr
  calc
    ZLattice.covolume (shortVectorLattice Λ R) * N =
        N * ZLattice.covolume (shortVectorLattice Λ R) := mul_comm _ _
    _ ≤ (P.card : ℝ) * ZLattice.covolume (shortVectorLattice Λ R) :=
      mul_le_mul_of_nonneg_right hcard hcov
    _ ≤ _ := hpack.trans hvol

theorem shortVectorLattice_covolume_le_of_points
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (R N : ℝ) (hR : 0 ≤ R) (hN : 0 < N)
    (P : Finset E) (hP : ∀ p ∈ P, p ∈ Λ ∧ ‖p‖ ≤ R) (hcard : N ≤ (P.card : ℝ)) :
    ZLattice.covolume (shortVectorLattice Λ R) ≤
      (((finrank ℝ (shortVectorSpan Λ R) : ℝ) + 2) * R) ^
        finrank ℝ (shortVectorSpan Λ R) / N := by
  classical
  let f : P → shortVectorLattice Λ R := fun p =>
    ⟨⟨p.val, mem_shortVectorSpan Λ R (hP p.val p.property).1 (hP p.val p.property).2⟩,
      (hP p.val p.property).1⟩
  have hf : Function.Injective f := by
    intro p q hpq
    exact Subtype.ext (congrArg (fun z : shortVectorLattice Λ R => z.val.val) hpq)
  let Q : Finset (shortVectorLattice Λ R) := Finset.univ.image f
  have hQcard : Q.card = P.card := by
    rw [Finset.card_image_of_injective _ hf]
    simp
  have hQ : ∀ q ∈ Q, ‖(q : shortVectorSpan Λ R)‖ ≤ R := by
    intro q hq
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hq
    exact (hP p.val p.property).2
  exact shortVectorLattice_covolume_le Λ R N hR hN Q hQ (hQcard ▸ hcard)

end Erdos3

end

section

namespace Erdos3

open Module

theorem euclideanDerivativeLattice_covolume_le
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ]
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (R N : ℝ) (hR : 0 ≤ R) (hN : 0 < N)
    (P : Finset ((σ → ℝ) × (κ → ℝ)))
    (hP : ∀ v ∈ P,
      v ∈ derivativeGridPoints T scale Y (LinearMap.toMatrix' A.toLinearMap) l ∧ ‖v‖ ≤ R)
    (hcard : N ≤ (P.card : ℝ)) :
    let ρ := ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T hT scale hscale Y A l hl
    ZLattice.covolume (shortVectorLattice Λ ρ) ≤
      (((finrank ℝ (shortVectorSpan Λ ρ) : ℝ) + 2) * ρ) ^
        finrank ℝ (shortVectorSpan Λ ρ) / N := by
  obtain ⟨Q, hQcard, hQ⟩ := exists_bounded_euclideanDerivativeLattice_family
    T hT scale hscale Y A l hl R P hP
  apply shortVectorLattice_covolume_le_of_points _ _ N
    (mul_nonneg (Nat.cast_nonneg _) hR) hN Q hQ
  simpa only [hQcard] using hcard

end Erdos3

end

end OAI
