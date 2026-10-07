import OAI.Combinatorics.Progressions.Estimates.PrimitiveExtension
import OAI.Combinatorics.Progressions.Geometry.NormalizedSpatialReplacement
import OAI.Combinatorics.Progressions.Geometry.SpatialStarCoordinates
import OAI.Combinatorics.Progressions.Sampling.SmoothSplitSampling

namespace OAI


namespace Erdos3

open scoped BigOperators Matrix Classical

def affinePairMatrix {J : Type*} (t u : J → ℤ) : Matrix (Fin 2) (Option J) ℤ :=
  fun i c => match c with
    | none => 1
    | some j => ![t j, u j] i

theorem affinePairMatrix_mulVec {J : Type*} [Fintype J] (t u : J → ℤ)
    (w : Option J → ℤ) :
    affinePairMatrix t u *ᵥ w =
      ![w none + ∑ j, t j * w (some j), w none + ∑ j, u j * w (some j)] := by
  ext i
  fin_cases i <;> simp [affinePairMatrix, Matrix.mulVec, dotProduct, Fintype.sum_option]

def affinePairImage {J : Type*} [Fintype J] (t u : J → ℤ) : Submodule ℤ (Fin 2 → ℤ) :=
  (affinePairMatrix t u).mulVecLin.range

theorem mem_affinePairImage_iff {J : Type*} [Fintype J] (t u : J → ℤ) (v : Fin 2 → ℤ) :
    v ∈ affinePairImage t u ↔ ∃ x : ℤ, ∃ V : J → ℤ,
      x + ∑ j, t j * V j = v 0 ∧ x + ∑ j, u j * V j = v 1 := by
  constructor
  · rintro ⟨w, hw⟩
    change affinePairMatrix t u *ᵥ w = v at hw
    rw [affinePairMatrix_mulVec] at hw
    exact ⟨w none, (fun j => w (some j)), congrFun hw 0, congrFun hw 1⟩
  · rintro ⟨x, V, h0, h1⟩
    refine ⟨(fun c => Option.elim c x V), ?_⟩
    change affinePairMatrix t u *ᵥ (fun c => Option.elim c x V) = v
    rw [affinePairMatrix_mulVec]
    ext i
    fin_cases i
    · exact h0
    · exact h1

theorem affinePairImage_iff_content_dvd {J : Type*} [Fintype J]
    (t u : J → ℤ) (v : Fin 2 → ℤ) :
    v ∈ affinePairImage t u ↔ BohrLattice.Primitive.content (fun j => u j - t j) ∣ v 1 - v 0 := by
  rw [mem_affinePairImage_iff]
  constructor
  · rintro ⟨x, V, h0, h1⟩
    have he : v 1 - v 0 = ∑ j, (u j - t j) * V j := by
      rw [← h0, ← h1]
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    rw [he]
    exact Finset.dvd_sum (fun j _ => dvd_mul_of_dvd_left
      (BohrLattice.Primitive.content_dvd (fun j => u j - t j) j) (V j))
  · rintro ⟨c, hc⟩
    obtain ⟨b, hb⟩ := BohrLattice.Primitive.exists_bezout_finset Finset.univ (fun j => u j - t j)
    have hb' : ∑ j, b j * (u j - t j) = BohrLattice.Primitive.content (fun j => u j - t j) := hb
    have he : (∑ j, u j * (c * b j)) - (∑ j, t j * (c * b j)) =
        BohrLattice.Primitive.content (fun j => u j - t j) * c := by
      calc
        _ = ∑ j, (u j * (c * b j) - t j * (c * b j)) := by rw [Finset.sum_sub_distrib]
        _ = c * ∑ j, b j * (u j - t j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by rw [hb']; ring
    refine ⟨v 0 - ∑ j, t j * (c * b j), (fun j => c * b j), ?_, ?_⟩
    · ring
    · linarith

end Erdos3


namespace Erdos3

open scoped Matrix

def pairDifferenceMod (m : ℕ) : (Fin 2 → ℤ) →+ ZMod m where
  toFun v := ((v 1 - v 0 : ℤ) : ZMod m)
  map_zero' := by simp
  map_add' x y := by simp only [Pi.add_apply, Int.cast_sub, Int.cast_add]; ring

theorem pairDifferenceMod_surjective (m : ℕ) : Function.Surjective (pairDifferenceMod m) := by
  intro r
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective r
  refine ⟨![0, z], ?_⟩
  simpa [pairDifferenceMod] using hz

theorem pairDifferenceMod_ker (m : ℕ) (v : Fin 2 → ℤ) :
    v ∈ (pairDifferenceMod m).ker ↔ (m : ℤ) ∣ v 1 - v 0 := by
  change (((v 1 - v 0 : ℤ) : ZMod m) = 0) ↔ _
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

theorem affinePairImage_eq_congruence_kernel {J : Type*} [Fintype J] (t u : J → ℤ) :
    (affinePairImage t u).toAddSubgroup =
      (pairDifferenceMod (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs).ker := by
  ext v
  rw [Submodule.mem_toAddSubgroup, affinePairImage_iff_content_dvd, pairDifferenceMod_ker,
    Int.natAbs_dvd]

theorem pairDifferenceMod_index (m : ℕ) : (pairDifferenceMod m).ker.index = m := by
  rw [AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.mpr (pairDifferenceMod_surjective m)]
  simpa only [Nat.card_zmod] using
    (Nat.card_congr (AddSubgroup.topEquiv : (⊤ : AddSubgroup (ZMod m)) ≃+ ZMod m).toEquiv)

theorem affinePairImage_index {J : Type*} [Fintype J] (t u : J → ℤ) :
    (affinePairImage t u).toAddSubgroup.index =
      (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs := by
  rw [affinePairImage_eq_congruence_kernel, pairDifferenceMod_index]

end Erdos3


namespace Erdos3

open scoped Matrix

theorem integerResidueMatrix_fromCols {I J N : Type*}
    (B : Matrix I J ℤ) (C : Matrix I N ℤ) (m : ℕ) :
    integerResidueMatrix (Matrix.fromCols B C) m =
      Matrix.fromCols (integerResidueMatrix B m) (integerResidueMatrix C m) := by
  ext i k
  cases k <;> rfl

theorem integerMatrix_fromCols_range {I J N : Type*} [Fintype J] [Fintype N]
    (B : Matrix I J ℤ) (C : Matrix I N ℤ) :
    (Matrix.fromCols B C).mulVecLin.range = B.mulVecLin.range ⊔ C.mulVecLin.range := by
  ext v
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨B *ᵥ (fun j => x (.inl j)), ⟨_, rfl⟩,
      C *ᵥ (fun n => x (.inr n)), ⟨_, rfl⟩, ?_⟩
    exact (Matrix.fromCols_mulVec B C x).symm.trans hx
  · rintro ⟨b, ⟨x, rfl⟩, c, ⟨y, rfl⟩, h⟩
    refine ⟨Sum.elim x y, ?_⟩
    change Matrix.fromCols B C *ᵥ Sum.elim x y = v
    rw [Matrix.fromCols_mulVec_sumElim]
    exact h

theorem pivotFullImage_eq_range {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) :
    pivotFullImage A B = (Matrix.fromCols A B).mulVecLin.range :=
  (integerMatrix_fromCols_range A B).symm

theorem pivotFullImage_split {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (C : Matrix I N ℤ) :
    pivotFullImage A (Matrix.fromCols B C) = pivotFullImage A B ⊔ C.mulVecLin.range := by
  unfold pivotFullImage
  rw [integerMatrix_fromCols_range, sup_assoc]

theorem pivotFullImage_eq_of_kernel_residues {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (C D : Matrix I N ℤ) (m : ℕ)
    (hperiod : integerScalarLattice I (m : ℤ) ≤ pivotFullImage A B)
    (hCD : integerResidueMatrix C m = integerResidueMatrix D m) :
    pivotFullImage A (Matrix.fromCols B C) = pivotFullImage A (Matrix.fromCols B D) := by
  have hc : integerScalarLattice I (m : ℤ) ≤ (Matrix.fromCols A (Matrix.fromCols B C)).mulVecLin.range := by
    rw [← pivotFullImage_eq_range, pivotFullImage_split]
    exact hperiod.trans le_sup_left
  have hd : integerScalarLattice I (m : ℤ) ≤ (Matrix.fromCols A (Matrix.fromCols B D)).mulVecLin.range := by
    rw [← pivotFullImage_eq_range, pivotFullImage_split]
    exact hperiod.trans le_sup_left
  rw [pivotFullImage_eq_range, pivotFullImage_eq_range]
  apply integerMatrixImage_eq_of_residueMatrix _ _ m hc hd
  simp only [integerResidueMatrix_fromCols, hCD]

theorem maskedIntegerImageDensity_eq_of_kernel_residues {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (C D : Matrix I N ℤ) (m : ℕ)
    (hperiod : integerScalarLattice I (m : ℤ) ≤ pivotFullImage A B)
    (hCD : integerResidueMatrix C m = integerResidueMatrix D m)
    (P : I → ℝ) (f : (I → ℝ) → ℝ) :
    maskedIntegerImageDensity A (Matrix.fromCols B C) P f =
      maskedIntegerImageDensity A (Matrix.fromCols B D) P f := by
  classical
  funext v
  have h := pivotFullImage_eq_of_kernel_residues A B C D m hperiod hCD
  exact congrArg (fun L : Submodule ℤ (I → ℤ) =>
    if v ∈ L then (L.toAddSubgroup.index : ℝ) * f (fun i => (v i : ℝ) / P i) else 0) h

end Erdos3


namespace Erdos3

open scoped Matrix Classical

def affinePairPivot {J : Type*} (t u : J → ℤ) (k : J) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, t k; 1, u k]

def affinePairFree {J : Type*} (t u : J → ℤ) (k : J) :
    Matrix (Fin 2) {j : J // j ≠ k} ℤ := fun i j => ![t j.val, u j.val] i

def affinePairColumnEquiv {J : Type*} [DecidableEq J] (k : J) :
    (Fin 2 ⊕ {j : J // j ≠ k}) ≃ Option J where
  toFun c := match c with
    | Sum.inl i => if i = 0 then none else some k
    | Sum.inr j => some j.val
  invFun c := match c with
    | none => Sum.inl 0
    | some j => if h : j = k then Sum.inl 1 else Sum.inr ⟨j, h⟩
  left_inv c := by
    rcases c with i | j
    · fin_cases i <;> simp
    · simp [j.property]
  right_inv c := by
    cases c with
    | none => rfl
    | some j => by_cases h : j = k <;> simp [h]

theorem affinePairPivot_det {J : Type*} (t u : J → ℤ) (k : J) :
    (affinePairPivot t u k).det = u k - t k := by
  simp [affinePairPivot, Matrix.det_fin_two]

theorem affinePairPivot_columns {J : Type*} [DecidableEq J] (t u : J → ℤ) (k : J) :
    Matrix.fromCols (affinePairPivot t u k) (affinePairFree t u k) =
      (affinePairMatrix t u).submatrix id (affinePairColumnEquiv k) := by
  ext i c
  rcases c with j | j
  · fin_cases i <;> fin_cases j <;>
      simp [affinePairPivot, affinePairMatrix, affinePairColumnEquiv, Matrix.submatrix]
  · rfl

theorem affinePairPivot_image {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) :
    pivotFullImage (affinePairPivot t u k) (affinePairFree t u k) = affinePairImage t u := by
  rw [pivotFullImage_eq_range, affinePairPivot_columns]
  ext v
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w ∘ (affinePairColumnEquiv k).symm, ?_⟩
    change (affinePairMatrix t u).submatrix id (affinePairColumnEquiv k) *ᵥ w = v at hw
    rw [Matrix.submatrix_mulVec_equiv] at hw
    change affinePairMatrix t u *ᵥ (w ∘ (affinePairColumnEquiv k).symm) = v
    simpa only [Function.comp_id] using hw
  · rintro ⟨w, hw⟩
    change affinePairMatrix t u *ᵥ w = v at hw
    refine ⟨w ∘ affinePairColumnEquiv k, ?_⟩
    change (affinePairMatrix t u).submatrix id (affinePairColumnEquiv k) *ᵥ
      (w ∘ affinePairColumnEquiv k) = v
    rw [Matrix.submatrix_mulVec_equiv]
    simpa only [Function.comp_def, Equiv.apply_symm_apply, id_eq] using hw

theorem affinePairPivot_index {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) :
    (pivotFullImage (affinePairPivot t u k) (affinePairFree t u k)).toAddSubgroup.index =
      (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs := by
  rw [affinePairPivot_image, affinePairImage_index]

end Erdos3


namespace Erdos3

open scoped Classical

noncomputable def latticeStarMask {I : Type*}
    (L : Submodule ℤ ((Unit ⊕ I) → ℤ)) (m : ℕ) (a : (Unit ⊕ I) → ZMod m) : ℂ := by
  classical
  exact if spatialUnstar a ∈ residueLatticeImage L m then (L.toAddSubgroup.index : ℂ) else 0

theorem latticeStarMask_bound {I : Type*} (L : Submodule ℤ ((Unit ⊕ I) → ℤ)) (m : ℕ)
    {G : ℝ} (hindex : (L.toAddSubgroup.index : ℝ) ≤ G) (a : (Unit ⊕ I) → ZMod m) :
    ‖latticeStarMask L m a‖ ≤ G := by
  classical
  unfold latticeStarMask
  split_ifs
  · simpa using hindex
  · simpa using (Nat.cast_nonneg L.toAddSubgroup.index).trans hindex

theorem latticeStarMask_eval {I : Type*} [Fintype I]
    (L : Submodule ℤ ((Unit ⊕ I) → ℤ)) (m : ℕ)
    (hperiod : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤ L) (v : (Unit ⊕ I) → ℤ) :
    latticeStarMask L m (fun i => ((spatialStar v i : ℤ) : ZMod m)) =
      if v ∈ L then (L.toAddSubgroup.index : ℂ) else 0 := by
  classical
  simp only [latticeStarMask, spatialUnstar_residue_star, ← residueLatticeImage_mem_iff L m hperiod]

theorem maskedIntegerImageDensity_star {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ) (m : ℕ)
    (hperiod : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤ pivotFullImage A B)
    (H : ℝ) (f : ((Unit ⊕ I) → ℝ) → ℝ) (v : (Unit ⊕ I) → ℤ) :
    (maskedIntegerImageDensity A B (fun _ => H) f v : ℂ) =
      latticeStarMask (pivotFullImage A B) m (fun i => ((spatialStar v i : ℤ) : ZMod m)) *
        (f (spatialUnstar (fun i => ((spatialStar v i : ℤ) : ℝ) / H)) : ℂ) := by
  classical
  rw [latticeStarMask_eval _ _ hperiod, spatialUnstar_scaled_star]
  by_cases hv : v ∈ pivotFullImage A B
  · simp only [maskedIntegerImageDensity, hv, ite_true, Complex.ofReal_mul, Complex.ofReal_natCast]
  · simp only [maskedIntegerImageDensity, hv, ite_false, Complex.ofReal_zero, zero_mul]

end Erdos3


namespace Erdos3

open scoped BigOperators

noncomputable def liftResidueMatrix {I N : Type*} {m : ℕ} (r : Matrix I N (ZMod m)) : Matrix I N ℤ :=
  fun i n => (ZMod.intCast_surjective (r i n)).choose

theorem liftResidueMatrix_residue {I N : Type*} {m : ℕ} (r : Matrix I N (ZMod m)) :
    integerResidueMatrix (liftResidueMatrix r) m = r := by
  ext i n
  exact (ZMod.intCast_surjective (r i n)).choose_spec

noncomputable def residueSpatialWeight {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (P : I → ℝ) (f : (I → ℝ) → ℝ)
    {m : ℕ} (r : Matrix I N (ZMod m)) : (I → ℤ) → ℝ :=
  maskedIntegerImageDensity A (Matrix.fromCols B (liftResidueMatrix r)) P f

theorem maskedIntegerImageDensity_eq_residueWeight {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (C : Matrix I N ℤ)
    (P : I → ℝ) (f : (I → ℝ) → ℝ) (m : ℕ)
    (hperiod : integerScalarLattice I (m : ℤ) ≤ pivotFullImage A B) :
    maskedIntegerImageDensity A (Matrix.fromCols B C) P f =
      residueSpatialWeight A B P f (integerResidueMatrix C m) := by
  apply maskedIntegerImageDensity_eq_of_kernel_residues A B C _ m hperiod
  rw [liftResidueMatrix_residue]

theorem residueSpatialWeight_factor_average {X I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (s : Finset X) (A : Matrix I I ℤ) (B : Matrix I J ℤ) (C : X → Matrix I N ℤ)
    (P : I → ℝ) (f : (I → ℝ) → ℝ) (m : ℕ) (r : Matrix I N (ZMod m))
    (hperiod : integerScalarLattice I (m : ℤ) ≤ pivotFullImage A B)
    (hresidue : ∀ x ∈ s, integerResidueMatrix (C x) m = r)
    (D : X → ℝ) (v : I → ℤ) :
    (𝔼 x ∈ s, maskedIntegerImageDensity A (Matrix.fromCols B (C x)) P f v * D x) =
      residueSpatialWeight A B P f r v * (𝔼 x ∈ s, D x) := by
  rw [Finset.mul_expect]
  apply Finset.expect_congr rfl
  intro x hx
  rw [maskedIntegerImageDensity_eq_residueWeight A B (C x) P f m hperiod, hresidue x hx]

end Erdos3


namespace Erdos3

open scoped Matrix

noncomputable def affinePairScale (H L : ℝ) : Fin 2 → ℝ := ![H, H / L]

theorem affinePairScale_pos {H L : ℝ} (hH : 0 < H) (hL : 0 < L) :
    ∀ i, 0 < affinePairScale H L i := by
  intro i
  fin_cases i
  · exact hH
  · exact div_pos hH hL

theorem normalized_affinePairPivot {J : Type*} (t u : J → ℤ) (k : J)
    {H L : ℝ} (hH : H ≠ 0) (hL : L ≠ 0) :
    normalizedIntegerPivot (affinePairPivot t u k) (affinePairScale H L) (fun _ => H) =
      !![1, (t k : ℝ) / L; 1, (u k : ℝ) / L] := by
  ext i j
  rw [normalizedIntegerPivot_entry]
  fin_cases i <;> fin_cases j <;> simp [affinePairPivot, affinePairScale, hH] <;> field_simp

theorem normalized_affinePairFree {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) {H L : ℝ} (hH : H ≠ 0) (hL : L ≠ 0) :
    normalizedIntegerColumns (affinePairFree t u k) (fun _ => H / L) (fun _ => H) =
      (fun i j => ![(t j.val : ℝ) / L, (u j.val : ℝ) / L] i) := by
  ext i j
  fin_cases i <;>
    simp [normalizedIntegerColumns, Matrix.mul_diagonal, Matrix.diagonal_mul, affinePairFree] <;>
    field_simp

theorem normalized_affinePairPivot_det {J : Type*} (t u : J → ℤ) (k : J)
    {H L : ℝ} (hH : H ≠ 0) (hL : L ≠ 0) :
    (normalizedIntegerPivot (affinePairPivot t u k) (affinePairScale H L) (fun _ => H)).det =
      ((u k - t k : ℤ) : ℝ) / L := by
  rw [normalized_affinePairPivot t u k hH hL]
  simp [Matrix.det_fin_two, sub_div]

theorem normalized_affinePairPivot_inverse {J : Type*} (t u : J → ℤ) (k : J)
    {H L C κ : ℝ} (hH : H ≠ 0) (hL : L ≠ 0) (hC : 1 ≤ C) (hκ : 0 < κ)
    (ht : |(t k : ℝ) / L| ≤ C) (hu : |(u k : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|) :
    ‖(matrixSupCLM (normalizedIntegerPivot (affinePairPivot t u k)
      (affinePairScale H L) (fun _ => H))).inverse‖ ≤ 4 * C / κ := by
  have hentry : ∀ i j, |normalizedIntegerPivot (affinePairPivot t u k)
      (affinePairScale H L) (fun _ => H) i j| ≤ C := by
    rw [normalized_affinePairPivot t u k hH hL]
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using hC
    · exact ht
    · simpa using hC
    · exact hu
  have hd : κ ≤ |(normalizedIntegerPivot (affinePairPivot t u k)
      (affinePairScale H L) (fun _ => H)).det| := by
    rwa [normalized_affinePairPivot_det t u k hH hL]
  have h := (matrixSupCLM_inverse_norm_le _ (zero_le_one.trans hC) hentry hκ hd).2
  norm_num [mul_div_assoc, ← mul_assoc] at h
  simpa only [mul_div_assoc] using h

theorem normalized_affinePairFree_norm {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) {H L C : ℝ} (hH : H ≠ 0) (hL : L ≠ 0) (hC : 0 ≤ C)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C) :
    ‖matrixSupCLM (normalizedIntegerColumns (affinePairFree t u k)
      (fun _ => H / L) (fun _ => H))‖ ≤ (Fintype.card J : ℝ) * C := by
  apply (matrixSupCLM_norm_le _ hC ?_).trans
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Fintype.card_subtype_le _)) hC)
  rw [normalized_affinePairFree t u k hH hL]
  intro i j
  fin_cases i
  · exact ht j.val
  · exact hu j.val

end Erdos3


namespace Erdos3

open scoped BigOperators

theorem residueSpatialWeight_average_functional {X I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (s : Finset X) (outputs : Finset (I → ℤ))
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (C : X → Matrix I N ℤ)
    (P : I → ℝ) (f : (I → ℝ) → ℝ) (m : ℕ) (r : Matrix I N (ZMod m))
    (hperiod : integerScalarLattice I (m : ℤ) ≤ pivotFullImage A B)
    (hresidue : ∀ x ∈ s, integerResidueMatrix (C x) m = r)
    (D : X → (I → ℤ) → ℝ) (φ : (I → ℤ) → ℂ) :
    (𝔼 x ∈ s, 𝔼 v ∈ outputs,
      ((D x v * maskedIntegerImageDensity A (Matrix.fromCols B (C x)) P f v : ℝ) : ℂ) * φ v) =
    (𝔼 v ∈ outputs, ((residueSpatialWeight A B P f r v * (𝔼 x ∈ s, D x v) : ℝ) : ℂ) * φ v) := by
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro v _
  rw [← Finset.expect_mul]
  congr 1
  have hcast := map_expect (algebraMap ℝ ℂ)
    (fun x => D x v * maskedIntegerImageDensity A (Matrix.fromCols B (C x)) P f v) s
  simp only [Complex.coe_algebraMap] at hcast
  rw [← hcast]
  congr 1
  have h := residueSpatialWeight_factor_average s A B C P f m r hperiod hresidue (fun x => D x v) v
  convert h using 1
  apply Finset.expect_congr rfl
  intro x _
  ring

theorem residueSpatialWeight_average_comparison {X I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (s : Finset X) (outputs : Finset (I → ℤ))
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (C : X → Matrix I N ℤ)
    (P : I → ℝ) (f : (I → ℝ) → ℝ) (m : ℕ) (r : Matrix I N (ZMod m))
    (hperiod : integerScalarLattice I (m : ℤ) ≤ pivotFullImage A B)
    (hresidue : ∀ x ∈ s, integerResidueMatrix (C x) m = r)
    (mass D : X → (I → ℤ) → ℝ) (φ : (I → ℤ) → ℂ) {ε : ℝ}
    (hD : ∀ x ∈ s, ∀ v ∈ outputs, 0 ≤ D x v)
    (hφ : ∀ v ∈ outputs, ‖φ v‖ ≤ 1)
    (herror : ∀ x ∈ s, ∀ v ∈ outputs,
      |mass x v - maskedIntegerImageDensity A (Matrix.fromCols B (C x)) P f v| ≤ ε) :
    ‖(𝔼 x ∈ s, 𝔼 v ∈ outputs, ((D x v * mass x v : ℝ) : ℂ) * φ v) -
      (𝔼 v ∈ outputs, ((residueSpatialWeight A B P f r v * (𝔼 x ∈ s, D x v) : ℝ) : ℂ) * φ v)‖ ≤
        ε * (𝔼 x ∈ s, 𝔼 v ∈ outputs, D x v) := by
  classical
  rw [← residueSpatialWeight_average_functional s outputs A B C P f m r hperiod hresidue D φ]
  have h := norm_weighted_density_mean_sub_le (s.product outputs)
    (fun p => D p.1 p.2) (fun p => mass p.1 p.2)
    (fun p => maskedIntegerImageDensity A (Matrix.fromCols B (C p.1)) P f p.2)
    (fun p => φ p.2)
    (fun p hp => hD p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2)
    (fun p hp => hφ p.2 (Finset.mem_product.mp hp).2)
    (fun p hp => herror p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2)
  simp only [Finset.product_eq_sprod, Finset.expect_product] at h
  exact h

end Erdos3


namespace Erdos3

open scoped BigOperators

theorem weightedResidueSpatial_mixture_functional {X I J N : Type*}
    [Fintype X] [Fintype I] [DecidableEq I] [Fintype J] [Fintype N] [DecidableEq N]
    (p : FiniteProbabilityWeights X) (outputs : Finset (I → ℤ))
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (C : X → Matrix I N ℤ)
    (P : I → ℝ) (f : (I → ℝ) → ℝ) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ pivotFullImage A B)
    (D : X → (I → ℤ) → ℝ) (φ : (I → ℤ) → ℂ) :
    p.complexMean (fun x => 𝔼 v ∈ outputs,
      ((D x v * maskedIntegerImageDensity A (Matrix.fromCols B (C x)) P f v : ℝ) : ℂ) * φ v) =
    ∑ r : Matrix I N (ZMod m), 𝔼 v ∈ outputs,
      ((p.fiberMean (fun x => integerResidueMatrix (C x) m) r (fun x => D x v) *
        residueSpatialWeight A B P f r v : ℝ) : ℂ) * φ v := by
  classical
  calc
    _ = 𝔼 v ∈ outputs, ∑ r : Matrix I N (ZMod m),
        ((p.fiberMean (fun x => integerResidueMatrix (C x) m) r (fun x => D x v) *
          residueSpatialWeight A B P f r v : ℝ) : ℂ) * φ v := by
      rw [p.complexMean_finset_expect]
      apply Finset.expect_congr rfl
      intro v _
      simp_rw [maskedIntegerImageDensity_eq_residueWeight A B _ P f m hperiod]
      simpa only [Complex.ofReal_mul, mul_assoc] using
        p.complexMean_fiber_factor (fun x => integerResidueMatrix (C x) m) (fun x => D x v)
          (fun r => (residueSpatialWeight A B P f r v : ℂ) * φ v)
    _ = _ := Finset.expect_sum_comm _ _ _

theorem weightedResidueSpatial_mixture_comparison {X I J N : Type*}
    [Fintype X] [Fintype I] [DecidableEq I] [Fintype J] [Fintype N] [DecidableEq N]
    (p : FiniteProbabilityWeights X) (outputs : Finset (I → ℤ))
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (C : X → Matrix I N ℤ)
    (P : I → ℝ) (f : (I → ℝ) → ℝ) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ pivotFullImage A B)
    (mass D : X → (I → ℤ) → ℝ) (φ : (I → ℤ) → ℂ) {ε : ℝ}
    (hD : ∀ x, p.weight x ≠ 0 → ∀ v ∈ outputs, 0 ≤ D x v)
    (hφ : ∀ v ∈ outputs, ‖φ v‖ ≤ 1)
    (herror : ∀ x, p.weight x ≠ 0 → ∀ v ∈ outputs,
      |mass x v - maskedIntegerImageDensity A (Matrix.fromCols B (C x)) P f v| ≤ ε) :
    ‖p.complexMean (fun x => 𝔼 v ∈ outputs, ((D x v * mass x v : ℝ) : ℂ) * φ v) -
      ∑ r : Matrix I N (ZMod m), 𝔼 v ∈ outputs,
        ((p.fiberMean (fun x => integerResidueMatrix (C x) m) r (fun x => D x v) *
          residueSpatialWeight A B P f r v : ℝ) : ℂ) * φ v‖ ≤
      ε * p.mean (fun x => 𝔼 v ∈ outputs, D x v) := by
  rw [← weightedResidueSpatial_mixture_functional p outputs A B C P f m hperiod D φ]
  apply (p.norm_complexMean_sub_le _ _ (fun x => ε * (𝔼 v ∈ outputs, D x v)) ?_).trans_eq
    (p.mean_const_mul ε _)
  intro x hx
  exact norm_weighted_density_mean_sub_le outputs (D x) (mass x) _ φ
    (hD x hx) hφ (herror x hx)

end Erdos3


namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal BigOperators

theorem affinePair_mesh_bound {d : ℤ} (hd : d ≠ 0) {H L δ : ℝ}
    (hH : 0 < H) (hL : 1 ≤ L) (hmesh : (d.natAbs : ℝ) * L / H ≤ δ) :
    (∀ i, 1 / affinePairScale H L i ≤ δ) ∧ (d.natAbs : ℝ) / (H / L) ≤ δ := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hd1 : (1 : ℝ) ≤ d.natAbs := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hd))
  constructor
  · intro i
    fin_cases i
    · change 1 / H ≤ δ
      apply (div_le_div_of_nonneg_right (show (1 : ℝ) ≤ d.natAbs * L by nlinarith) hH.le).trans hmesh
    · change 1 / (H / L) ≤ δ
      have he : 1 / (H / L) = L / H := by field_simp
      rw [he]
      exact (div_le_div_of_nonneg_right (show L ≤ (d.natAbs : ℝ) * L by nlinarith) hH.le).trans hmesh
  · have he : (d.natAbs : ℝ) / (H / L) = (d.natAbs : ℝ) * L / H := by field_simp
    rwa [he]

noncomputable def affinePairRowDensity {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0) (H L : ℝ) (hH : 0 < H) (hL : 0 < L)
    (f : ({j : J // j ≠ k} → ℝ) × (Fin 2 → ℝ) → ℝ) : (Fin 2 → ℝ) → ℝ :=
  normalizedFiberDensity (affinePairPivot t u k) (by rwa [affinePairPivot_det])
    (affinePairFree t u k) (affinePairScale H L) (fun _ => H) (fun _ => H / L)
    (affinePairScale_pos hH hL) (fun _ => hH) f

theorem affinePair_probability_error {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0) (v : Fin 2 → ℤ)
    (hcong : BohrLattice.Primitive.content (fun j => u j - t j) ∣ v 1 - v 0)
    {H L C κ R F δ : ℝ} (Q : ℕ) (K : ℝ≥0)
    (hH : 0 < H) (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ)
    (hR : 0 ≤ R) (hF : 0 ≤ F) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (hQ : (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs ≤ Q)
    (hmesh : ((u k - t k).natAbs : ℝ) * L / H ≤ δ)
    (f : ({j : J // j ≠ k} → ℝ) × (Fin 2 → ℝ) → ℝ)
    (hf0 : ∀ z, 0 ≤ f z) (hf : LipschitzWith K f)
    (hsupport : ∀ z, R < ‖z‖ → f z = 0) (hmass : (∫ z, f z) = 1)
    (hsmall : (2 * R + 2) ^ (2 + Fintype.card {j : J // j ≠ k}) * K * δ ≤ 1 / 2)
    (hbound : ∀ z, ‖f z‖ ≤ F) :
    ∃ hM : 0 < scaledInputMass f (affinePairScale H L) (fun _ => H / L),
      |H ^ 2 * (integerImagePMF (affinePairPivot t u k) (affinePairFree t u k) f hf0
          (affinePairScale H L) (fun _ => H / L)
          (affinePairScale_pos hH (zero_lt_one.trans_le hL))
          (fun _ => div_pos hH (zero_lt_one.trans_le hL)) hsupport hM v).toReal -
        ((BohrLattice.Primitive.content (fun j => u j - t j)).natAbs : ℝ) *
          affinePairRowDensity t u k hne H L hH (zero_lt_one.trans_le hL) f
            (fun i => (v i : ℝ) / H)| ≤
        normalizedFiberErrorConstant 2 (Fintype.card {j : J // j ≠ k}) Q
          (4 * C / κ) ((Fintype.card J : ℝ) * C) R F K * δ := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hA : (affinePairPivot t u k).det ≠ 0 := by rwa [affinePairPivot_det]
  have hv : v ∈ pivotFullImage (affinePairPivot t u k) (affinePairFree t u k) := by
    rwa [affinePairPivot_image, affinePairImage_iff_content_dvd]
  have hm : (0 : ℤ) < (u k - t k).natAbs := by
    exact_mod_cast Int.natAbs_pos.mpr hne
  have hdiv : (affinePairPivot t u k).det ∣ ((u k - t k).natAbs : ℤ) := by
    rw [affinePairPivot_det]
    exact Int.dvd_natAbs_self
  have hmeshes := affinePair_mesh_bound hne hH hL hmesh
  have hi : ((pivotFullImage (affinePairPivot t u k) (affinePairFree t u k)).toAddSubgroup.index : ℝ) ≤ Q := by
    rw [affinePairPivot_index]
    exact_mod_cast hQ
  have hinv : ‖(normalizedPivotEquiv (affinePairPivot t u k) hA
      (affinePairScale H L) (fun _ => H) (affinePairScale_pos hH hL0) (fun _ => hH)).symm.toContinuousLinearMap‖ ≤
      4 * C / κ := by
    rw [normalizedPivotEquiv_inverse_eq]
    exact normalized_affinePairPivot_inverse t u k hH.ne' hL0.ne' hC hκ (ht k) (hu k) hgap
  have hcol := normalized_affinePairFree_norm t u k hH.ne' hL0.ne' (zero_le_one.trans hC) ht hu
  have h := normalizedIntegerFiber_uniform_error (affinePairPivot t u k) hA (affinePairFree t u k)
    (m := ((u k - t k).natAbs : ℤ)) v hv hm hdiv (affinePairScale H L) (fun _ => H) (fun _ => H / L)
    (affinePairScale_pos hH hL0) (fun _ => hH) (fun _ => div_pos hH hL0)
    f hf hR hδ hδ1 hF hmeshes.1 (fun _ => by
      rw [Int.cast_natCast]
      exact hmeshes.2)
    hsupport hmass (by simpa only [Fintype.card_fin] using hsmall) hbound hi hinv hcol
  obtain ⟨hM, he⟩ := h
  refine ⟨hM, ?_⟩
  rw [normalizedIntegerFiberOutputMass_pmf _ _ f hf0 _ _ _ (affinePairScale_pos hH hL0)
    (fun _ => div_pos hH hL0) hsupport hM v, affinePairPivot_index] at he
  simpa only [Fin.prod_univ_two, Fintype.card_fin, pow_two, affinePairRowDensity] using he

theorem affinePair_probability_law {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    {H L C κ R F δ : ℝ} (Q : ℕ) (K : ℝ≥0)
    (hH : 0 < H) (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ)
    (hR : 0 ≤ R) (hF : 0 ≤ F) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (hQ : (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs ≤ Q)
    (hmesh : ((u k - t k).natAbs : ℝ) * L / H ≤ δ)
    (f : ({j : J // j ≠ k} → ℝ) × (Fin 2 → ℝ) → ℝ)
    (hf0 : ∀ z, 0 ≤ f z) (hf : LipschitzWith K f)
    (hsupport : ∀ z, R < ‖z‖ → f z = 0) (hmass : (∫ z, f z) = 1)
    (hsmall : (2 * R + 2) ^ (2 + Fintype.card {j : J // j ≠ k}) * K * δ ≤ 1 / 2)
    (hbound : ∀ z, ‖f z‖ ≤ F) :
    ∃ hM : 0 < scaledInputMass f (affinePairScale H L) (fun _ => H / L), ∀ v,
      |H ^ 2 * (integerImagePMF (affinePairPivot t u k) (affinePairFree t u k) f hf0
          (affinePairScale H L) (fun _ => H / L)
          (affinePairScale_pos hH (zero_lt_one.trans_le hL))
          (fun _ => div_pos hH (zero_lt_one.trans_le hL)) hsupport hM v).toReal -
        (if BohrLattice.Primitive.content (fun j => u j - t j) ∣ v 1 - v 0 then
          ((BohrLattice.Primitive.content (fun j => u j - t j)).natAbs : ℝ) *
          affinePairRowDensity t u k hne H L hH (zero_lt_one.trans_le hL) f
            (fun i => (v i : ℝ) / H) else 0)| ≤
        normalizedFiberErrorConstant 2 (Fintype.card {j : J // j ≠ k}) Q
          (4 * C / κ) ((Fintype.card J : ℝ) * C) R F K * δ := by
  classical
  obtain ⟨hM, hzero⟩ := affinePair_probability_error t u k hne 0 (by simp) Q K
    hH hL hC hκ hR hF hδ hδ1 ht hu hgap hQ hmesh f hf0 hf hsupport hmass hsmall hbound
  refine ⟨hM, fun v => ?_⟩
  by_cases hc : BohrLattice.Primitive.content (fun j => u j - t j) ∣ v 1 - v 0
  · obtain ⟨hM', hv⟩ := affinePair_probability_error t u k hne v hc Q K
      hH hL hC hκ hR hF hδ hδ1 ht hu hgap hQ hmesh f hf0 hf hsupport hmass hsmall hbound
    simpa only [hc, ite_true] using hv
  · have hnot : v ∉ pivotFullImage (affinePairPivot t u k) (affinePairFree t u k) := by
      simpa only [affinePairPivot_image, affinePairImage_iff_content_dvd] using hc
    have hz := integerImagePMF_zero_off_image (affinePairPivot t u k) (affinePairFree t u k)
      f hf0 (affinePairScale H L) (fun _ => H / L)
      (affinePairScale_pos hH (zero_lt_one.trans_le hL))
      (fun _ => div_pos hH (zero_lt_one.trans_le hL)) hsupport hM v hnot
    simp only [hc, ite_false, hz, ENNReal.toReal_zero, mul_zero, sub_self, abs_zero]
    exact (abs_nonneg _).trans hzero

end Erdos3


namespace Erdos3

open scoped NNReal Matrix

noncomputable def smoothPairRowLipschitz {J : Type*} [Fintype J] [DecidableEq J] (k : J) : ℝ≥0 :=
  ((Fintype.card {j : J // j ≠ k} + 2 : ℕ) : ℝ≥0) * probabilityProfileLipschitz

theorem smooth_affinePair_probability_law {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    {H L C κ δ : ℝ} (Q : ℕ) (hH : 0 < H) (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (hQ : (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs ≤ Q)
    (hmesh : ((u k - t k).natAbs : ℝ) * L / H ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) *
      smoothPairRowLipschitz k * δ ≤ 1 / 2) :
    let f := splitSmoothProductProfile {j : J // j ≠ k} (Fin 2)
    ∃ hM : 0 < scaledInputMass f (affinePairScale H L) (fun _ => H / L), ∀ v,
      |H ^ 2 * (integerImagePMF (affinePairPivot t u k) (affinePairFree t u k) f
          (fun z => (splitSmoothProductProfile_range _ _ z).1)
          (affinePairScale H L) (fun _ => H / L)
          (affinePairScale_pos hH (zero_lt_one.trans_le hL))
          (fun _ => div_pos hH (zero_lt_one.trans_le hL))
          (splitSmoothProductProfile_zero_outside _ _) hM v).toReal -
        (if BohrLattice.Primitive.content (fun j => u j - t j) ∣ v 1 - v 0 then
          ((BohrLattice.Primitive.content (fun j => u j - t j)).natAbs : ℝ) *
            affinePairRowDensity t u k hne H L hH (zero_lt_one.trans_le hL) f
              (fun i => (v i : ℝ) / H) else 0)| ≤
        normalizedFiberErrorConstant 2 (Fintype.card {j : J // j ≠ k}) Q
          (4 * C / κ) ((Fintype.card J : ℝ) * C) 1 1 (smoothPairRowLipschitz k) * δ := by
  dsimp only
  have hLip : LipschitzWith (smoothPairRowLipschitz k)
      (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2)) := by
    simpa only [smoothPairRowLipschitz, Fintype.card_fin] using
      splitSmoothProductProfile_lipschitz {j : J // j ≠ k} (Fin 2)
  have hbound (z : ({j : J // j ≠ k} → ℝ) × (Fin 2 → ℝ)) :
      ‖splitSmoothProductProfile {j : J // j ≠ k} (Fin 2) z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (splitSmoothProductProfile_range _ _ z).1]
    exact (splitSmoothProductProfile_range _ _ z).2
  exact affinePair_probability_law t u k hne Q (smoothPairRowLipschitz k)
    hH hL hC hκ (by norm_num) (by norm_num) hδ hδ1 ht hu hgap hQ hmesh
    (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2))
    (fun z => (splitSmoothProductProfile_range _ _ z).1) hLip
    (splitSmoothProductProfile_zero_outside _ _) (splitSmoothProductProfile_integral _ _)
    (by simpa only [show 2 * (1 : ℝ) + 2 = 4 by norm_num] using hsmall) hbound

end Erdos3

end OAI
