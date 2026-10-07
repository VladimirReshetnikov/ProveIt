/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.GramCovolume
import OAI.Combinatorics.Progressions.Linear.BasisAxisNormalization
import OAI.Combinatorics.Progressions.Linear.BasisImageSection
import OAI.Combinatorics.Progressions.Linear.MatrixSupInverse

namespace OAI

section

namespace Erdos3

open Module MeasureTheory
open scoped BigOperators

variable {I E : Type*} [Fintype I] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem covolume_basis_eq_orthonormal_det [DecidableEq I]
    (o : OrthonormalBasis I ℝ E) (b : Basis I ℝ E) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) = |o.toBasis.det b| := by
  classical
  have hvolume : volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [measureReal_def]
    have hfd : volume (ZSpan.fundamentalDomain o.toBasis) = 1 := by
      rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume)]
      exact o.volume_parallelepiped
    rw [hfd]
    simp
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain b volume),
    ZSpan.measureReal_fundamentalDomain b volume o.toBasis, hvolume, mul_one]

theorem covolume_basis_scale (o : OrthonormalBasis I ℝ E) (b c : Basis I ℝ E)
    (t : I → ℝ) (ht : ∀ i, 0 ≤ t i) (hc : ∀ i, c i = t i • b i) :
    ZLattice.covolume (Submodule.span ℤ (Set.range c)) =
      (∏ i, t i) * ZLattice.covolume (Submodule.span ℤ (Set.range b)) := by
  classical
  rw [covolume_basis_eq_orthonormal_det o c, covolume_basis_eq_orthonormal_det o b]
  rw [show (c : I → E) = (fun i => t i • b i) from funext hc,
    AlternatingMap.map_smul_univ, smul_eq_mul, abs_mul,
    abs_of_nonneg (Finset.prod_nonneg (fun i _ => ht i))]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem orthonormal_basis_coordinate_abs_le (o : OrthonormalBasis I ℝ E) (x : E) (i : I) :
    |o.toBasis.equivFun x i| ≤ ‖x‖ := by
  have h := PiLp.norm_apply_le (o.repr x) i
  change |o.repr x i| ≤ ‖x‖
  simpa only [Real.norm_eq_abs, LinearIsometryEquiv.norm_map] using h

theorem covolume_basis_le_norm_bound (o : OrthonormalBasis I ℝ E) (b : Basis I ℝ E)
    {H : ℝ} (hb : ∀ i, ‖b i‖ ≤ H) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) ≤
      (Fintype.card I).factorial * H ^ Fintype.card I := by
  classical
  rw [covolume_basis_eq_orthonormal_det o b, Basis.det_apply]
  apply matrix_det_abs_le_uniform_bound
  intro i j
  exact (orthonormal_basis_coordinate_abs_le o (b j) i).trans (hb j)

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators Matrix

theorem basis_synthesis_norm_le {E : Type*} {n : ℕ}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : Basis (Fin n) ℝ E) {H : ℝ} (hb : ∀ i, ‖b i‖ ≤ H) (x : Fin n → ℝ) :
    ‖b.equivFun.symm x‖ ≤ (n : ℝ) * H * ‖x‖ := by
  rw [Basis.equivFun_symm_apply]
  calc
    _ ≤ ∑ i, ‖x i • b i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖x‖ * H := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm x i) (hb i) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem basis_coordinates_norm_le_of_covolume {E : Type*} {n : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (o : OrthonormalBasis (Fin n) ℝ E) (b : Basis (Fin n) ℝ E)
    {H κ : ℝ} (hH : 0 ≤ H) (hκ : 0 < κ) (hb : ∀ i, ‖b i‖ ≤ H)
    (hcovol : κ ≤ ZLattice.covolume (span ℤ (Set.range b))) (x : E) :
    ‖b.equivFun x‖ ≤ ((n : ℝ) * n.factorial * H ^ (n - 1) / κ) * ‖x‖ := by
  classical
  let A := o.toBasis.toMatrix b
  have hdet : κ ≤ |A.det| := by
    simpa only [covolume_basis_eq_orthonormal_det o b, Basis.det_apply] using hcovol
  have hentry : ∀ i j, |A i j| ≤ H := fun i j =>
    (orthonormal_basis_coordinate_abs_le o (b j) i).trans (hb j)
  have hinv : ∀ i j, |A⁻¹ i j| ≤ (n.factorial : ℝ) * H ^ (n - 1) / κ := by
    intro i j
    simpa only [Fintype.card_fin] using matrix_inverse_entry_abs_le A hentry hκ hdet i j
  have hM : A *ᵥ (b.equivFun x) = o.toBasis.equivFun x :=
    basis_coordinate_matrix_mulVec b o.toBasis.equivFun.toLinearMap x
  have hback : A⁻¹ *ᵥ (o.toBasis.equivFun x) = b.equivFun x := by
    rw [← hM, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr (abs_pos.mp (hκ.trans_le hdet))),
      Matrix.one_mulVec]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [← hback, Real.norm_eq_abs]
  change |∑ j, A⁻¹ i j * o.toBasis.equivFun x j| ≤ _
  calc
    _ ≤ ∑ j, |A⁻¹ i j * o.toBasis.equivFun x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, ((n.factorial : ℝ) * H ^ (n - 1) / κ) * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hinv i j) (orthonormal_basis_coordinate_abs_le o x j)
        (abs_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators

variable {E : Type*} {n : ℕ} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem normalizedAxisBasis_covolume (o : OrthonormalBasis (Fin n) ℝ E)
    (b : Basis (Fin n) ℝ E) :
    ZLattice.covolume (span ℤ (Set.range (normalizedAxisBasis b))) =
      (∏ i, (basisAxisScale b i : ℝ)) * ZLattice.covolume (span ℤ (Set.range b)) :=
  covolume_basis_scale o b (normalizedAxisBasis b) (fun i => (basisAxisScale b i : ℝ))
    (fun _ => Nat.cast_nonneg _) (normalizedAxisBasis_apply b)

theorem normalizedAxisBasis_covolume_lower (o : OrthonormalBasis (Fin n) ℝ E)
    (b : Basis (Fin n) ℝ E) {D : ℝ} (hD : 0 < D)
    (hb : (∏ i, ‖b i‖) ≤ D * ZLattice.covolume (span ℤ (Set.range b))) :
    1 / D ≤ ZLattice.covolume (span ℤ (Set.range (normalizedAxisBasis b))) := by
  have hprod : 1 ≤ ∏ i, ‖normalizedAxisBasis b i‖ := by
    apply Finset.one_le_prod₀
    intro i _
    rw [normalizedAxisBasis_norm]
    exact (basisAxisScale_mul_norm b i).1
  have hupper : (∏ i, ‖normalizedAxisBasis b i‖) ≤
      D * ZLattice.covolume (span ℤ (Set.range (normalizedAxisBasis b))) := by
    rw [normalizedAxisBasis_norm_product, normalizedAxisBasis_covolume o b]
    calc
      _ ≤ (∏ i, (basisAxisScale b i : ℝ)) *
          (D * ZLattice.covolume (span ℤ (Set.range b))) :=
        mul_le_mul_of_nonneg_left hb (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
      _ = _ := by ring
  apply (div_le_iff₀ hD).mpr
  simpa only [mul_comm] using hprod.trans hupper

theorem normalizedAxisBasis_covolume_upper (o : OrthonormalBasis (Fin n) ℝ E)
    (b : Basis (Fin n) ℝ E) {B : ℝ} (hb : ∀ i, ‖b i‖ ≤ B) :
    ZLattice.covolume (span ℤ (Set.range (normalizedAxisBasis b))) ≤
      (n.factorial : ℝ) * (B + 1) ^ n := by
  simpa only [Fintype.card_fin] using covolume_basis_le_norm_bound o (normalizedAxisBasis b)
    (fun i => (normalizedAxisBasis_norm_bounds b hb i).2)

theorem normalizedAxisBasis_coordinates_bound (o : OrthonormalBasis (Fin n) ℝ E)
    (b : Basis (Fin n) ℝ E) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 < D)
    (hb : ∀ i, ‖b i‖ ≤ B)
    (hprod : (∏ i, ‖b i‖) ≤ D * ZLattice.covolume (span ℤ (Set.range b))) (x : E) :
    ‖(normalizedAxisBasis b).equivFun x‖ ≤
      ((n : ℝ) * n.factorial * (B + 1) ^ (n - 1) * D) * ‖x‖ := by
  have h := basis_coordinates_norm_le_of_covolume o (normalizedAxisBasis b)
    (by positivity : 0 ≤ B + 1) (one_div_pos.mpr hD)
    (fun i => (normalizedAxisBasis_norm_bounds b hb i).2)
    (normalizedAxisBasis_covolume_lower o b hD hprod) x
  simpa only [one_div, div_inv_eq_mul] using h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem normalizedAxisBasis_synthesis_bound (b : Basis (Fin n) ℝ E) {B : ℝ}
    (hb : ∀ i, ‖b i‖ ≤ B) (x : Fin n → ℝ) :
    ‖(normalizedAxisBasis b).equivFun.symm x‖ ≤ (n : ℝ) * (B + 1) * ‖x‖ :=
  basis_synthesis_norm_le (normalizedAxisBasis b)
    (fun i => (normalizedAxisBasis_norm_bounds b hb i).2) x

theorem normalizedAxisBasis_reciprocal_covolume (o : OrthonormalBasis (Fin n) ℝ E)
    (b : Basis (Fin n) ℝ E) {q : ℝ}
    (hq : q * ZLattice.covolume (span ℤ (Set.range b)) = 1) :
    q / (∏ i, (basisAxisScale b i : ℝ)) =
      1 / ZLattice.covolume (span ℤ (Set.range (normalizedAxisBasis b))) := by
  have hc := (ZLattice.covolume_pos (span ℤ (Set.range b)) volume).ne'
  have hp : (∏ i, (basisAxisScale b i : ℝ)) ≠ 0 :=
    (Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (basisAxisScale_pos b i))).ne'
  have heq : q = 1 / ZLattice.covolume (span ℤ (Set.range b)) := (eq_div_iff hc).mpr hq
  rw [heq, normalizedAxisBasis_covolume o b]
  field_simp [hp, hc]

theorem normalizedAxisBasis_covolume_ratio_bounds (o : OrthonormalBasis (Fin n) ℝ E)
    (b : Basis (Fin n) ℝ E) {B D q : ℝ} (hD : 0 < D)
    (hb : ∀ i, ‖b i‖ ≤ B)
    (hprod : (∏ i, ‖b i‖) ≤ D * ZLattice.covolume (span ℤ (Set.range b)))
    (hq : q * ZLattice.covolume (span ℤ (Set.range b)) = 1) :
    1 / ((n.factorial : ℝ) * (B + 1) ^ n) ≤ q / (∏ i, (basisAxisScale b i : ℝ)) ∧
      q / (∏ i, (basisAxisScale b i : ℝ)) ≤ D := by
  rw [normalizedAxisBasis_reciprocal_covolume o b hq]
  have hpos := ZLattice.covolume_pos (span ℤ (Set.range (normalizedAxisBasis b))) volume
  refine ⟨div_le_div_of_nonneg_left zero_le_one hpos
    (normalizedAxisBasis_covolume_upper o b hb), ?_⟩
  apply (div_le_iff₀ hpos).mpr
  have h := (div_le_iff₀ hD).mp (normalizedAxisBasis_covolume_lower o b hD hprod)
  simpa only [mul_comm] using h

end Erdos3

end

end OAI
