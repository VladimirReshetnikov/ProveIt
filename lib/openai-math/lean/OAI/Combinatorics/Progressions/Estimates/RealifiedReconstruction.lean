/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Nilpotent.BCHSmoothPartitionBudget
import OAI.Combinatorics.Progressions.Polynomial.WeightedPolynomialPotentialExtension

namespace OAI

section

namespace Erdos3

variable {σ τ : Type*}

noncomputable def weightedLinearInverseMask
    (B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ)) (v : τ → ℕ) (w : σ → ℕ) :
    (σ → ℚ) →ₗ[ℚ] (τ → ℚ) where
  toFun x j := B (coordinateWeightProjection w (v j) x) j
  map_add' x y := by funext j; simp only [map_add, Pi.add_apply]
  map_smul' r x := by funext j; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

theorem weightedLinearInverseMask_apply [Fintype τ] [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ))
    (v : τ → ℕ) (w : σ → ℕ)
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (hBA : ∀ x, B (A x) = x) (x : τ → ℚ) :
    weightedLinearInverseMask B v w (A x) = x := by
  funext j
  change B (fun i => if w i = v j then A x i else 0) j = x j
  rw [← linearMap_coordinateGradeProjection A v w hweight, hBA]
  simp

theorem weightedLinearInverseMask_entry [DecidableEq σ]
    (B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (i : σ) (j : τ) :
    weightedLinearInverseMask B v w (Pi.single i 1) j =
      if w i = v j then B (Pi.single i 1) j else 0 := by
  have hproj : coordinateWeightProjection w (v j) (Pi.single i 1) =
      if w i = v j then Pi.single i 1 else 0 := by
    funext k
    by_cases hk : k = i
    · subst k
      by_cases hij : w i = v j <;> simp [coordinateWeightProjection, hij]
    · by_cases hij : w i = v j <;>
        simp [coordinateWeightProjection, hij, Pi.single_eq_of_ne hk]
  change B (coordinateWeightProjection w (v j) (Pi.single i 1)) j = _
  rw [hproj]
  split_ifs <;> simp

theorem weightedLinearInverseMask_weighted [DecidableEq σ]
    (B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (i : σ) (j : τ) (hij : w i ≠ v j) :
    weightedLinearInverseMask B v w (Pi.single i 1) j = 0 := by
  rw [weightedLinearInverseMask_entry, ite_eq_right hij]

theorem weightedLinearInverseMask_height [DecidableEq σ]
    (B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    {H : ℕ} (hB : ∀ j i, RationalHeightLE (B (Pi.single i 1) j) H)
    (i : σ) (j : τ) :
    RationalHeightLE (weightedLinearInverseMask B v w (Pi.single i 1) j) H := by
  rw [weightedLinearInverseMask_entry]
  split_ifs
  · exact hB j i
  · exact rationalHeightLE_zero ((B (Pi.single i 1) j).den_pos.trans_le (hB j i).2)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem exists_bounded_linear_section (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) (hφ : Function.Surjective φ) {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H) :
    ∃ σ : M →ₗ[ℚ] L, Function.RightInverse σ φ ∧
      ∀ i j, RationalHeightLE (e.repr (σ (f j)) i) (rationalSolveHeight (Fintype.card κ) H) := by
  classical
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_section (LinearMap.toMatrix e f φ)
    (basisMatrix_surjective e f φ hφ) hH (by
      intro i j
      rw [LinearMap.toMatrix_apply]
      exact hentries i j)
  refine ⟨Matrix.toLin f e S, basisMatrix_section e f φ S hS, ?_⟩
  intro i j
  have heq := LinearMap.toMatrix_apply f e (Matrix.toLin f e S) i j
  rw [LinearMap.toMatrix_toLin] at heq
  rw [← heq]
  exact hSH i j

omit [Fintype ι] [Fintype κ] in

theorem linearMap_baseChange_basis (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) (i : κ) (j : ι) :
    (f.baseChange ℝ).repr (φ.baseChange ℝ ((e.baseChange ℝ) j)) i =
      (f.repr (φ (e j)) i : ℝ) := by
  simp only [Basis.baseChange_apply, LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def]

theorem linearMap_baseChange_rightInverse (φ : L →ₗ[ℚ] M) (σ : M →ₗ[ℚ] L)
    (hσ : Function.RightInverse σ φ) :
    Function.RightInverse (σ.baseChange ℝ) (φ.baseChange ℝ) := by
  have heq : φ.comp σ = LinearMap.id := LinearMap.ext hσ
  have heqR := congrArg (fun T : M →ₗ[ℚ] M => T.baseChange ℝ) heq
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at heqR
  intro x
  exact DFunLike.congr_fun heqR x

theorem exists_bounded_realified_linear_section (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) (hφ : Function.Surjective φ) {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H) :
    ∃ σ : (ℝ ⊗[ℚ] M) →ₗ[ℝ] (ℝ ⊗[ℚ] L),
      Function.RightInverse σ (φ.baseChange ℝ) ∧
      ∀ i j, |(e.baseChange ℝ).repr (σ ((f.baseChange ℝ) j)) i| ≤
        (rationalSolveHeight (Fintype.card κ) H : ℝ) := by
  obtain ⟨σ, hσ, hσH⟩ := exists_bounded_linear_section e f φ hφ hH hentries
  refine ⟨σ.baseChange ℝ, linearMap_baseChange_rightInverse φ σ hσ, ?_⟩
  intro i j
  rw [linearMap_baseChange_basis]
  exact (hσH i j).abs_real_le

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

theorem exists_bounded_rational_image_section {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ S : Matrix κ ι ℚ, A * S * A = A ∧
      ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card ι) H) := by
  classical
  obtain ⟨r, hr, rows, _, hsurj, hker⟩ := exists_independent_defining_rows A
  let R := A.submatrix rows id
  let T := (1 : Matrix ι ι ℚ).submatrix rows id
  have hTA : T * A = R := by
    ext i j
    simp [T, R, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply]
  obtain ⟨U, hU, hUH⟩ := exists_bounded_rational_section R hsurj hH (fun i j => hA (rows i) j)
  let S := U * T
  have hpoint (x : κ → ℚ) : A *ᵥ (S *ᵥ (A *ᵥ x)) = A *ᵥ x := by
    have hzero : R *ᵥ (S *ᵥ (A *ᵥ x) - x) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      have hm : R * S * A = R := by
        dsimp [S]
        rw [← Matrix.mul_assoc, hU, Matrix.one_mul, hTA]
      rw [hm, sub_self]
    have hmem : S *ᵥ (A *ᵥ x) - x ∈ LinearMap.ker A.mulVecLin := by
      rw [← hker]
      exact hzero
    change A *ᵥ (S *ᵥ (A *ᵥ x) - x) = 0 at hmem
    rw [Matrix.mulVec_sub, sub_eq_zero] at hmem
    exact hmem
  refine ⟨S, Matrix.ext_iff_mulVec.mpr (fun x => by
    simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using hpoint x), ?_⟩
  have hT : ∀ i j, RationalHeightLE (T i j) 1 := by
    intro i j
    by_cases hij : rows i = j
    · simpa [T, Matrix.one_apply, hij] using rationalHeightLE_one (by decide : 1 ≤ 1)
    · simpa [T, Matrix.one_apply, hij] using rationalHeightLE_zero (by decide : 1 ≤ 1)
  intro i j
  have hs := rationalHeightLE_matrix_mul U T hUH hT i j
  apply hs.mono
  simp only [Fintype.card_fin, mul_one]
  apply le_trans _ (rationalKernelHeight_mono hH hr)
  unfold rationalKernelHeight
  apply Nat.mul_le_mul (by omega)
  apply pow_le_pow_left₀ (Nat.zero_le _)
  exact le_mul_of_one_le_right (Nat.zero_le _) hH

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem exists_bounded_linear_image_section (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H) :
    ∃ σ : M →ₗ[ℚ] L, (φ.comp σ).comp φ = φ ∧
      ∀ i j, RationalHeightLE (e.repr (σ (f j)) i) (rationalKernelHeight (Fintype.card κ) H) := by
  classical
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section (LinearMap.toMatrix e f φ) hH
    (by intro i j; rw [LinearMap.toMatrix_apply]; exact hentries i j)
  refine ⟨Matrix.toLin f e S, ?_, ?_⟩
  · apply (LinearMap.toMatrix e f).injective
    rw [LinearMap.toMatrix_comp e f f, LinearMap.toMatrix_comp f e f, LinearMap.toMatrix_toLin]
    exact hS
  · intro i j
    have heq := LinearMap.toMatrix_apply f e (Matrix.toLin f e S) i j
    rw [LinearMap.toMatrix_toLin] at heq
    rw [← heq]
    exact hSH i j

theorem linearMap_baseChange_image_section (φ : L →ₗ[ℚ] M) (σ : M →ₗ[ℚ] L)
    (hσ : (φ.comp σ).comp φ = φ) :
    ((φ.baseChange ℝ).comp (σ.baseChange ℝ)).comp (φ.baseChange ℝ) = φ.baseChange ℝ := by
  simpa only [LinearMap.baseChange_comp] using
    congrArg (fun T : L →ₗ[ℚ] M => T.baseChange ℝ) hσ

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ}

theorem exists_bounded_filtered_section
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {k | j ≤ τ k}))
    (φ : L →ₗ[ℚ] M)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H) :
    ∃ S : M →ₗ[ℚ] L,
      Function.RightInverse S φ ∧
      (∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j) ∧
      ∀ i k, RationalHeightLE (b.repr (S (c k)) i)
        (rationalKernelHeight (Fintype.card κ) H) := by
  classical
  have lifts (k : κ) : ∃ x : L,
      x ∈ F.layer (τ k) ∧ φ x = c k ∧
        ∀ i, RationalHeightLE (b.repr x i) (rationalKernelHeight (Fintype.card κ) H) := by
    let P := basisCoordinateProjection b {i | τ k ≤ ω i}
    have hmasked : ∀ a i, RationalHeightLE (c.repr ((φ.comp P) (b i)) a) H := by
      intro a i
      change RationalHeightLE (c.repr (φ (basisCoordinateProjection b {i | τ k ≤ ω i} (b i))) a) H
      rw [basisCoordinateProjection_basis]
      split_ifs
      · exact hentries a i
      · simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
    obtain ⟨T, hT, hTH⟩ := exists_bounded_linear_image_section b c (φ.comp P) hH hmasked
    have hck : c k ∈ G.layer (τ k) := by
      rw [hG]
      exact Submodule.subset_span ⟨k, (show τ k ≤ τ k from le_rfl), rfl⟩
    obtain ⟨y, hy, hφy⟩ := hsurj (τ k) (c k) hck
    have hPy : P y = y := by
      apply basisCoordinateProjection_eq_self
      rwa [← hF]
    have himage : (φ.comp P) y = c k := by
      change φ (P y) = c k
      rw [hPy, hφy]
    have hright : (φ.comp P) (T (c k)) = c k := by
      have ht := congrArg (fun A : L →ₗ[ℚ] M => A y) hT
      change (φ.comp P) (T ((φ.comp P) y)) = (φ.comp P) y at ht
      simpa only [himage] using ht
    refine ⟨P (T (c k)), ?_, hright, ?_⟩
    · rw [hF]
      exact basisCoordinateProjection_mem_span b _ _
    · intro i
      change RationalHeightLE
        (b.repr (basisCoordinateProjection b {i | τ k ≤ ω i} (T (c k))) i) _
      rw [basisCoordinateProjection_repr]
      split_ifs
      · exact hTH i k
      · exact rationalHeightLE_zero (rationalKernelHeight_pos _ hH)
  choose v hmem hright hheight using lifts
  let S := c.constr ℚ v
  have hS (k : κ) : S (c k) = v k := c.constr_basis ℚ v k
  refine ⟨S, ?_, ?_, ?_⟩
  · have hcomp : φ.comp S = LinearMap.id := by
      apply c.ext
      intro k
      change φ (S (c k)) = c k
      rw [hS, hright]
    intro y
    exact congrArg (fun A : M →ₗ[ℚ] M => A y) hcomp
  · intro j y hy
    have hle : G.layer j ≤ (F.layer j).comap S := by
      rw [hG]
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      change S (c k) ∈ F.layer j
      rw [hS]
      exact F.antitone hk (hmem k)
    exact hle hy
  · intro i k
    rw [hS]
    exact hheight k i

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open scoped Matrix

variable {σ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]

theorem exists_controlled_coordinate_leftInverse
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ j i, RationalHeightLE (A (Pi.single j 1) i) H) :
    ∃ B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ), (∀ x, B (A x) = x) ∧
      ∀ i j, RationalHeightLE (B (Pi.single i 1) j)
        (rationalKernelHeight (Fintype.card σ) H) := by
  let D := LinearMap.toMatrix' A
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section D hH
    (fun i j => hentries j i)
  refine ⟨S.mulVecLin, ?_, ?_⟩
  · intro x
    apply hA
    have hx : D *ᵥ (S *ᵥ (D *ᵥ x)) = D *ᵥ x := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hS]
    simpa only [D, LinearMap.toMatrix'_mulVec, Matrix.mulVecLin_apply] using hx
  · intro i j
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] using hSH j i

theorem exists_controlled_weighted_leftInverse
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (hA : Function.Injective A) {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ j i, RationalHeightLE (A (Pi.single j 1) i) H) :
    ∃ B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ),
      (∀ x, B (A x) = x) ∧
      (∀ i j, w i ≠ v j → B (Pi.single i 1) j = 0) ∧
      (∀ i j, RationalHeightLE (B (Pi.single i 1) j)
        (rationalKernelHeight (Fintype.card σ) H)) := by
  obtain ⟨B, hBA, hBH⟩ := exists_controlled_coordinate_leftInverse A hA hH hentries
  refine ⟨weightedLinearInverseMask B v w, ?_, ?_, ?_⟩
  · exact weightedLinearInverseMask_apply A B v w hweight hBA
  · exact weightedLinearInverseMask_weighted B v w
  · exact weightedLinearInverseMask_height B v w (fun j i => hBH i j)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped NNReal TensorProduct

noncomputable def rationalReconstructionLipschitzBound (s d n H : ℕ) (ℓ B : ℝ≥0) : ℝ≥0 :=
  let C := bchLogMetricConstant s n H 1
  let K := coordinateLipschitzBound d n (rationalSolveHeight n H) * (n + 1) * C
  max (ℓ * (2 * K)) (2 * B / (C⁻¹ / 2))

variable {ι κ L M E : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

open NilpotentLieBCHGroup

theorem realificationMap_lattice_cover (φ : L →ₗ⁅ℚ⁆ M)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL))
    (Λ : Subgroup (NilpotentLieBCHGroup M t hM))
    (hcover : Λ ≤ Γ.map (mapOfSteps φ)) :
    Λ.map realificationHom ≤ (Γ.map realificationHom).map (realificationMap (hnil := hL) (hM := hM) φ) := by
  rintro g ⟨y, hy, rfl⟩
  obtain ⟨x, hx, hxy⟩ := hcover hy
  refine ⟨realificationHom x, ⟨x, hx, rfl⟩, ?_⟩
  rw [realificationMap_realificationHom_ofSteps, hxy]

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] [NormedAddCommGroup E]

theorem exists_lipschitz_realification_reconstruction
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : Function.Surjective φ)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL))
    (Λ : Subgroup (NilpotentLieBCHGroup M t hM))
    (hcover : Λ ≤ Γ.map (mapOfSteps φ))
    (l m H : ℕ) (hl : 0 < l) (hm : 0 < m) (hH : 1 ≤ H)
    (hΓ : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (hΛ : bchSubgroupCoordinates f Λ ⊆ denominatorGrid m)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    (hstructure : ∀ i j k, RationalHeightLE (lieStructureConstants f i j k) H)
    (u : (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL) ⧸
      Γ.map realificationHom) → E)
    (hker : ∀ k ∈ (realificationMap (hnil := hL) (hM := hM) φ).ker, ∀ x,
      u (QuotientGroup.mk (k * x)) = u (QuotientGroup.mk x))
    (ℓ B : ℝ≥0)
    (hu : letI := realificationQuotientMetricSpace e Γ l hl hΓ; LipschitzWith ℓ u)
    (hub : ∀ x, ‖u x‖ ≤ B) :
    letI := realificationQuotientMetricSpace f Λ m hm hΛ
    ∃ v : (NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) t (realification_lowerCentralSeries_eq_bot hM) ⧸
      Λ.map realificationHom) → E,
      (∀ x, v (QuotientGroup.mk (realificationMap (hnil := hL) (hM := hM) φ x)) = u (QuotientGroup.mk x)) ∧
      LipschitzWith (rationalReconstructionLipschitzBound t (Fintype.card ι) (Fintype.card κ) H ℓ B) v ∧
      ∀ y, ‖v y‖ ≤ B := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (e.baseChange ℝ).finiteDimensional_of_finite
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] M) := (f.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hL) (e.baseChange ℝ)
  let := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hM) (f.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := realification_lowerCentralSeries_eq_bot hL) (e.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := realification_lowerCentralSeries_eq_bot hM) (f.baseChange ℝ)
  obtain ⟨σ, hσ, hσB⟩ := exists_bounded_realified_linear_section e f φ.toLinearMap hφ hH hentries
  have hsurj : Function.Surjective (realificationMap (hnil := hL) (hM := hM) φ) := by
    intro g
    exact ⟨⟨σ g.coord⟩, ext (hσ g.coord)⟩
  let C := bchLogMetricConstant t (Fintype.card κ) H 1
  let K := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ)
    (rationalSolveHeight (Fintype.card κ) H) * ((Fintype.card κ : ℝ≥0) + 1) * C
  have hC : 0 < C := bchLogMetricConstant_pos t (Fintype.card κ) H 1
  have hlift := exists_local_metric_lifts_of_section
    (hnil := realification_lowerCentralSeries_eq_bot hL) (hM := realification_lowerCentralSeries_eq_bot hM)
    (e.baseChange ℝ) (f.baseChange ℝ) (realificationLieHom φ) σ hσ
    (rationalSolveHeight (Fintype.card κ) H) hσB (lieStructureConstants f)
    (fun i j k => (realLieBasis_structure f i j k).symm) hstructure
  exact exists_lipschitz_observable_reconstruction (realificationMap (hnil := hL) (hM := hM) φ) hsurj
    (Γ.map realificationHom) (Λ.map realificationHom)
    (realification_subgroup_closed_discrete e Γ l hl hΓ).1
    (realification_subgroup_closed_discrete f Λ m hm hΛ).1
    (realificationMap_lattice_cover φ Γ Λ hcover) u hker ℓ K B C⁻¹ (inv_pos.mpr hC) hu hub hlift

end Erdos3

end

end OAI
