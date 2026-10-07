import OAI.Combinatorics.Progressions.Lattices.ReducedLatticeBasis
import OAI.Combinatorics.Progressions.Linear.MatrixSupInverse

namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open Module Submodule
open scoped BigOperators

theorem basis_norm_le_of_integral_combination {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ)) {C : ℝ}
    (hprod : (∏ j, ‖b j‖) ≤ C * |(Matrix.of b).det|)
    (c : Fin n → ℤ) (i : Fin n) (hci : c i ≠ 0) :
    ‖b i‖ ≤ (n.factorial : ℝ) * C * ‖∑ j, c j • b j‖ := by
  classical
  let x := ∑ j, c j • b j
  let H := Function.update (fun j => ‖b j‖) i ‖x‖
  have hentry : ∀ j k, |((Matrix.of b).updateRow i x) j k| ≤ H j := by
    intro j k
    by_cases hji : j = i
    · subst j
      simpa only [Matrix.updateRow_self, H, Function.update_self] using abs_apply_le_norm x k
    · simpa only [Matrix.updateRow_ne hji, Matrix.of_apply, H, Function.update_of_ne hji]
        using abs_apply_le_norm (b j) k
  have hx : x = ∑ j, (c j : ℝ) • b j := by
    simp only [x, Int.cast_smul_eq_zsmul]
  have hdetx : ((Matrix.of b).updateRow i x).det = (c i : ℝ) * (Matrix.of b).det := by
    rw [hx]
    exact Matrix.det_updateRow_sum (Matrix.of b) i (fun j => (c j : ℝ))
  have hH : (∏ j, H j) = ‖x‖ * ∏ j ∈ Finset.univ.erase i, ‖b j‖ := by
    rw [← Finset.mul_prod_erase Finset.univ H (Finset.mem_univ i)]
    rw [show H i = ‖x‖ by simp [H]]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    exact Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
  have hbound := Erdos3.matrix_det_abs_le_row_bounds ((Matrix.of b).updateRow i x) H hentry
  rw [hdetx, abs_mul, hH, Fintype.card_fin] at hbound
  have hci1 : (1 : ℝ) ≤ |(c i : ℝ)| := by exact_mod_cast Int.one_le_abs hci
  have hdet : 0 < |(Matrix.of b).det| := by
    apply abs_pos.mpr
    have h := (AlternatingMap.map_basis_ne_zero_iff b (Pi.basisFun ℝ (Fin n)).det).mpr
      (Pi.basisFun ℝ (Fin n)).det_ne_zero
    simpa only [Pi.basisFun_det_apply] using h
  have hdetle : |(Matrix.of b).det| ≤
      (n.factorial : ℝ) * (‖x‖ * ∏ j ∈ Finset.univ.erase i, ‖b j‖) := by
    exact (le_mul_of_one_le_left hdet.le hci1).trans hbound
  have hmul : ‖b i‖ * |(Matrix.of b).det| ≤
      ((n.factorial : ℝ) * C * ‖∑ j, c j • b j‖) * |(Matrix.of b).det| := by
    calc
      ‖b i‖ * |(Matrix.of b).det| ≤ ‖b i‖ *
          ((n.factorial : ℝ) * (‖x‖ * ∏ j ∈ Finset.univ.erase i, ‖b j‖)) :=
        mul_le_mul_of_nonneg_left hdetle (norm_nonneg _)
      _ = (n.factorial : ℝ) * ‖x‖ * (∏ j, ‖b j‖) := by
        rw [← Finset.mul_prod_erase Finset.univ (fun j => ‖b j‖) (Finset.mem_univ i)]
        ring
      _ ≤ (n.factorial : ℝ) * ‖x‖ * (C * |(Matrix.of b).det|) :=
        mul_le_mul_of_nonneg_left hprod (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
      _ = ((n.factorial : ℝ) * C * ‖∑ j, c j • b j‖) * |(Matrix.of b).det| := by
        dsimp only [x]
        ring
  nlinarith

theorem basis_norm_le_of_short_spanning_family {n : ℕ} {A : Type*}
    (b : Basis (Fin n) ℝ (Fin n → ℝ)) {C R : ℝ} (hC : 0 ≤ C)
    (hprod : (∏ j, ‖b j‖) ≤ C * |(Matrix.of b).det|)
    (v : A → Fin n → ℝ) (hspan : span ℝ (Set.range v) = ⊤)
    (hmem : ∀ a, v a ∈ span ℤ (Set.range b)) (hnorm : ∀ a, ‖v a‖ ≤ R)
    (i : Fin n) : ‖b i‖ ≤ (n.factorial : ℝ) * C * R := by
  classical
  have hex : ∃ a, b.coord i (v a) ≠ 0 := by
    by_contra! h
    have hs : span ℝ (Set.range v) ≤ LinearMap.ker (b.coord i) := by
      apply span_le.mpr
      rintro _ ⟨a, rfl⟩
      exact LinearMap.mem_ker.mpr (h a)
    rw [hspan] at hs
    have hz := LinearMap.mem_ker.mp (hs (show b i ∈ (⊤ : Submodule ℝ (Fin n → ℝ)) from trivial))
    simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same, one_ne_zero] at hz
  obtain ⟨a, ha⟩ := hex
  have hm := hmem a
  rw [mem_span_range_iff_exists_fun] at hm
  obtain ⟨c, hc⟩ := hm
  have hci : c i ≠ 0 := by
    intro hz
    apply ha
    rw [← hc, map_sum]
    simp only [map_zsmul, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    simp [hz]
  have hb := basis_norm_le_of_integral_combination b hprod c i hci
  rw [hc] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (hnorm a) (mul_nonneg (Nat.cast_nonneg _) hC))

theorem abs_det_eq_of_same_integer_span {n : ℕ}
    (b c : Basis (Fin n) ℝ (Fin n → ℝ))
    (hspan : span ℤ (Set.range b) = span ℤ (Set.range c)) :
    |(Matrix.of b).det| = |(Matrix.of c).det| := by
  have hcov (d : Basis (Fin n) ℝ (Fin n → ℝ)) :
      ZLattice.covolume (span ℤ (Set.range d)) = |(Matrix.of d).det| := by
    simpa only [Function.comp_def, Basis.restrictScalars_apply] using
      ZLattice.covolume_eq_det (span ℤ (Set.range d)) (d.restrictScalars ℤ)
  rw [← hcov b, hspan, hcov c]

theorem exists_short_same_lattice_basis {n : ℕ} {A : Type*}
    (b : Basis (Fin n) ℝ (Fin n → ℝ)) (v : A → Fin n → ℝ) {R : ℝ}
    (hspan : span ℝ (Set.range v) = ⊤)
    (hmem : ∀ a, v a ∈ span ℤ (Set.range b)) (hnorm : ∀ a, ‖v a‖ ≤ R) :
    ∃ c : Basis (Fin n) ℝ (Fin n → ℝ),
      span ℤ (Set.range c) = span ℤ (Set.range b) ∧
      (∏ i, ‖c i‖) ≤ minkowskiSecondConstant n * |(Matrix.of c).det| ∧
      ∀ i, ‖c i‖ ≤ (n.factorial : ℝ) * minkowskiSecondConstant n * R := by
  obtain ⟨c, hc, hp⟩ := exists_same_lattice_basis_norm_product_le b
  rw [← abs_det_eq_of_same_integer_span c b hc] at hp
  refine ⟨c, hc, hp, ?_⟩
  apply basis_norm_le_of_short_spanning_family c (minkowskiSecondConstant_nonneg n) hp v hspan
  · intro a
    rw [hc]
    exact hmem a
  · exact hnorm

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI
