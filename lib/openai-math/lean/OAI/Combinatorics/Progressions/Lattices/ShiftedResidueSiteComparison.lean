import OAI.Combinatorics.Progressions.Lattices.PhysicalResidueOffsetShift

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem refinedResidue_shifted_site_error {D I J N : Type*}
    [Fintype D] [Fintype I] [DecidableEq I] [Fintype J] [Fintype N]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (C R : D → Matrix (Unit ⊕ I) N ℤ)
    (m : ℕ) [NeZero m]
    (hp : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤ pivotFullImage A B)
    (q : D → ℕ) (hq : ∀ d, 0 < q d) (residue : D → N → ℤ)
    (hresidue : ∀ d j, |(residue d j : ℝ)| ≤ q d)
    (hCR : ∀ d, integerResidueMatrix (C d) (q d * m) = integerResidueMatrix (R d) (q d * m))
    (f : D → ((Unit ⊕ I) → ℝ) → ℝ) {K : ℝ≥0} (hf : ∀ d, LipschitzWith K (f d))
    (H : D → ℝ) (hH : ∀ d, 0 < H d)
    (mass : D → ((Unit ⊕ I) → ℤ) → ℝ)
    {G cap E δ b r : ℝ} (hG : 0 ≤ G) (hcap0 : 0 ≤ cap) (hE : 0 ≤ E) (hδ : 0 ≤ δ)
    (hb : 0 < b) (hr : 0 < r)
    (hi : ∀ d, ((pivotFullImage A (Matrix.fromCols B (R d))).toAddSubgroup.index : ℝ) ≤ G)
    (hcap : ∀ d v, |f d v| ≤ cap)
    (hmass : ∀ d v, |mass d v -
      maskedIntegerImageDensity A (Matrix.fromCols B (C d)) (fun _ => H d) (f d) v| ≤ E)
    (hmove : ∀ d i, (∑ j, |((C d i j - R d i j : ℤ) : ℝ)|) ≤ δ * H d)
    (v : D → (Unit ⊕ I) → ℤ)
    (hv : ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / H d| ≤ b) :
    let shift := fun d => residueMatrixShift (C d) (R d) (q d) (residue d)
    let E' := E + G * K * δ
    ‖((∏ d, mass d (v d - shift d) : ℝ) : ℂ) -
      ∏ d, spatialSiteApprox A (Matrix.fromCols B (R d)) m (f d) (H d) b r (v d)‖ ≤
      Fintype.card D * (E' + 4 * G * K * r) * (1 + G * cap + E') ^ Fintype.card D := by
  intro shift E'
  have hpfull (d) : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤
      pivotFullImage A (Matrix.fromCols B (R d)) := by
    rw [pivotFullImage_split]
    exact hp.trans le_sup_left
  have hshift (d) : shift d ∈ integerScalarLattice (Unit ⊕ I) (m : ℤ) :=
    (residueMatrixShift_spec (C d) (R d) (q d) m (hq d) (hCR d) (residue d)).2
  have hnorm (d) : ‖fun i => ((-shift d) i : ℝ) / H d‖ ≤ δ := by
    apply (pi_norm_le_iff_of_nonneg hδ).mpr
    intro i
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hH d)]
    rw [Pi.neg_apply, Int.cast_neg, abs_neg, div_le_iff₀ (hH d)]
    exact (residueMatrixShift_bound (C d) (R d) (q d) m (hq d) (hCR d)
      (residue d) (hresidue d) i).trans (hmove d i)
  have hmass' (d) (w : (Unit ⊕ I) → ℤ) :
      |mass d (w - shift d) -
        maskedIntegerImageDensity A (Matrix.fromCols B (R d)) (fun _ => H d) (f d) w| ≤ E' := by
    have hmod : integerResidueMatrix (C d) m = integerResidueMatrix (R d) m :=
      integerResidueMatrix_reduce (C d) (R d) (Nat.dvd_mul_left m (q d)) (hCR d)
    have h := shiftedMass_residueMask_error A B (C d) (R d) m hp hmod
      (fun _ => H d) (f d) (hf d) (-shift d)
      ((integerScalarLattice (Unit ⊕ I) (m : ℤ)).neg_mem (hshift d)) (hi d) (mass d) (hmass d) w
    calc
      _ ≤ E + G * K * ‖fun i => ((-shift d) i : ℝ) / H d‖ := by
        simpa only [sub_eq_add_neg] using h
      _ ≤ E' := add_le_add le_rfl (mul_le_mul_of_nonneg_left (hnorm d)
        (mul_nonneg hG K.coe_nonneg))
  have hE' : 0 ≤ E' := by dsimp only [E']; positivity
  exact vectorSpatialSiteApprox_error A (fun d => Matrix.fromCols B (R d)) m hpfull f hf H
    (fun d w => mass d (w - shift d)) hG hcap0 hE' hb hr hi hcap hmass' v hv

end Erdos3

end

end OAI
