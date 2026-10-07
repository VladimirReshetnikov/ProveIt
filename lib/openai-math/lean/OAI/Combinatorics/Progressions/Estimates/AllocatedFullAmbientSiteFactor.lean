import OAI.Combinatorics.Progressions.Geometry.AllocatedFullSiteSupport

namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {D : Type*} [Fintype D]

noncomputable def fullSitePlateauFactor (H : ℝ) (f : (D → ℝ) → ℂ) (x : D → ℝ) : ℂ :=
  (normalizedSupportPlateau H x : ℂ) * f x

theorem fullSitePlateauFactor_norm_le (H : ℝ) (f : (D → ℝ) → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (x : D → ℝ) : ‖fullSitePlateauFactor H f x‖ ≤ 1 := by
  have hc := normalizedSupportPlateau_range H x
  rw [fullSitePlateauFactor, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc.1]
  exact (mul_le_mul hc.2 (hf x) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem fullSitePlateauFactor_lipschitz (H : ℝ) (f : (D → ℝ) → ℂ) {L : ℝ≥0}
    (hL : LipschitzWith L f) (hf : ∀ x, ‖f x‖ ≤ 1) :
    LipschitzWith (L + 4) (fullSitePlateauFactor H f) := by
  have hc : LipschitzWith 4 (fun x : D → ℝ => (normalizedSupportPlateau H x : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Complex.isometry_ofReal.dist_eq]
    exact (normalizedSupportPlateau_lipschitz H).dist_le_mul x y
  have hcb (x : D → ℝ) : ‖(normalizedSupportPlateau H x : ℂ)‖ ≤ (1 : ℝ≥0) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (normalizedSupportPlateau_range H x).1]
    exact (normalizedSupportPlateau_range H x).2
  have h := lipschitz_mul_of_bounds _ _ hc hL (Bf := 1) (Bg := 1) hcb hf
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [fullSitePlateauFactor, one_mul] using h.dist_le_mul x y

theorem fullSitePlateauFactor_eq {H : ℝ} (hH : 0 ≤ H) (f : (D → ℝ) → ℂ)
    (x : D → ℝ) (hx : ∀ a, |x a| ≤ H) : fullSitePlateauFactor H f x = f x := by
  rw [fullSitePlateauFactor, normalizedSupportPlateau_one hH x hx, Complex.ofReal_one, one_mul]

theorem fullSitePlateauFactor_nonzero_box (H : ℝ) (f : (D → ℝ) → ℂ)
    (x : D → ℝ) (hx : fullSitePlateauFactor H f x ≠ 0) : ∀ a, |x a| < H + 1 / 4 := by
  apply normalizedSupportPlateau_support x
  intro h
  apply hx
  rw [fullSitePlateauFactor, h, Complex.ofReal_zero, zero_mul]

namespace VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

local notation "single" => (fun _ : Fin m => Unit)
local notation "ambient" => JetAmbientIndex single J

theorem exists_allocated_full_ambient_site_factor (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ≥0)
    (hC : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ C j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) (L : ℝ≥0)
    (hL : LipschitzWith L f) (hf : ∀ v, ‖f v‖ ≤ 1) :
    ∃ g : (ambient → UnitAddCircle) → ℂ,
      LipschitzWith (2 * (L * (K * ∑ j, C j * Fintype.card (J j)))) g ∧
      (∀ z, ‖g z‖ ≤ 2) ∧
      ∀ v : ambient → ℝ, (∀ i, |v i| ≤ 1 / 4) →
        g (fun i => (v i : UnitAddCircle)) = f (allocatedFullAmbientSiteCoordinates (R := R) U b o v) := by
  obtain ⟨g, hg, hgb, hgv⟩ := exists_quarter_torus_extension
    (fun v => f (allocatedFullAmbientSiteCoordinates (R := R) U b o v))
    (L * (K * ∑ j, C j * Fintype.card (J j))) 1
    (hL.comp (allocatedFullAmbientSiteCoordinates_lipschitz U b o hR C hC K hK)) (fun v => hf _)
  exact ⟨g, hg, by simpa only [NNReal.coe_one, mul_one] using hgb, hgv⟩

theorem exists_allocated_full_buffered_ambient_site_factor (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ≥0)
    (hC : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ C j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (H : ℝ) (f : (LayerSamplerAxis I n → ℝ) → ℂ) (L : ℝ≥0)
    (hL : LipschitzWith L f) (hf : ∀ v, ‖f v‖ ≤ 1) :
    ∃ g : (ambient → UnitAddCircle) → ℂ,
      LipschitzWith (2 * ((L + 4) * (K * ∑ j, C j * Fintype.card (J j)))) g ∧
      (∀ z, ‖g z‖ ≤ 2) ∧
      ∀ v : ambient → ℝ, (∀ i, |v i| ≤ 1 / 4) →
        g (fun i => (v i : UnitAddCircle)) =
          fullSitePlateauFactor H f (allocatedFullAmbientSiteCoordinates (R := R) U b o v) :=
  exists_allocated_full_ambient_site_factor U b o hR C hC K hK (fullSitePlateauFactor H f) (L + 4)
    (fullSitePlateauFactor_lipschitz H f hL hf) (fullSitePlateauFactor_norm_le H f hf)

theorem allocatedFullAmbientSiteFactor_chart
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) (g : (ambient → UnitAddCircle) → ℂ)
    (hvalue : ∀ v : ambient → ℝ, (∀ i, |v i| ≤ 1 / 4) →
      g (fun i => (v i : UnitAddCircle)) = f (allocatedFullAmbientSiteCoordinates (R := R) U b o v))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (z : MixedCoveredJetSource I single Q n d)
    (hz : z ∈ mixedCoveredJetRegion U o b d (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))) :
    g (coveredJetAmbientTorus U d (mixedCoveredJetChart U o b hb bW d z)) =
      f (allocatedFullMixedSiteValue (R := R) U b (fun j => mixedArrayRegroup _ _ _ (z.1 j) ())) := by
  rw [coveredJetAmbientTorus_chart U b hb o bW d z]
  have hsmall : ∀ a, |mixedJetAmbientPoint U b o z.1 a| ≤ 1 / 4 := by
    rintro ⟨j, t, i⟩
    exact (hz j (Set.mem_univ j) t (Set.mem_univ t)).1 i
  rw [hvalue _ hsmall, allocatedFullAmbientSiteCoordinates_point]

theorem allocatedFullSitePlateau_point_bound (hR : ∀ j, 0 < R j)
    {H : ℝ} (hH : 0 ≤ H) (f : (LayerSamplerAxis I n → ℝ) → ℂ)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ))
    (hw : fullSitePlateauFactor H f (allocatedFullMixedSiteValue (R := R) U b w) ≠ 0)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (j : Fin m) :
    ‖normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w j))‖ ≤
      C j * (((Fintype.card (I j) : ℝ) + 1) * ((H + 1 / 4) * R j)) :=
  allocatedFullMixedSiteValue_point_bound U b hR o w (by positivity)
    (fun a => (fullSitePlateauFactor_nonzero_box H f _ hw a).le) C hC hchart j

theorem allocatedFullSitePlateau_nonzero_mem_quarter (hR : ∀ j, 0 < R j)
    {H : ℝ} (hH : 0 ≤ H) (f : (LayerSamplerAxis I n → ℝ) → ℂ)
    {Q : Fin m → Type*} (d : ℕ) (z : MixedCoveredJetSource I single Q n d)
    (hz : fullSitePlateauFactor H f (allocatedFullMixedSiteValue (R := R) U b
      (fun j => mixedArrayRegroup _ _ _ (z.1 j) ())) ≠ 0)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * ((H + 1 / 4) * R j)) ≤ 1 / 4) :
    z ∈ mixedCoveredJetRegion U o b d (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j)) := by
  intro j _ t _
  refine ⟨?_, Set.mem_univ _⟩
  intro i
  cases t
  have h := (allocatedFullSitePlateau_point_bound U b o hR hH f
    (fun j => mixedArrayRegroup _ _ _ (z.1 j) ()) hz C hC hchart j).trans (hbudget j)
  exact (PiLp.norm_apply_le (normalizedLatticePoint (euclideanSubspace (U j)) (b j)
    (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (z.1 j) ()))) i).trans h

end VectorPolynomial
end Erdos3

end

end OAI
