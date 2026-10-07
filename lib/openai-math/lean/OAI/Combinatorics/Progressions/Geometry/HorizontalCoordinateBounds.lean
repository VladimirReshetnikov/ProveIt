/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.HorizontalAmbientQuotient
import OAI.Combinatorics.Progressions.Estimates.RealProjectedCoefficientLift
import OAI.Combinatorics.Progressions.Nilpotent.AmbientBracketCorrectionPolynomials

namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s r : ℕ} (F : DegreeRankLieFiltration L s r)

def horizontalImageOfSubmodule (B : Submodule ℚ (Fin 4 → L)) (d : ℕ) :
    Submodule ℚ (Fin 4 → F.HigherHorizontal d) :=
  (B.comap (F.fourHorizontalLayer d).subtype).map (F.fourHorizontalMap d)

theorem layerHorizontalImage_eq_of_submodule (A : ℕ → Submodule ℚ M)
    (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
    (hφ : ∀ d x, x ∈ A d → ∀ k, φ x k ∈ F.layer d 1) (d : ℕ) :
    F.layerHorizontalImage A φ hφ d =
      F.horizontalImageOfSubmodule ((A d).map φ.toLinearMap) d := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨φ x.val, (F.mem_fourHorizontalLayer d _).mpr (hφ d x.val x.property)⟩, ?_, rfl⟩
    exact ⟨x.val, x.property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hy
    refine ⟨⟨x, hx⟩, ?_⟩
    apply congrArg (F.fourHorizontalMap d)
    exact Subtype.ext hxy

theorem layerHorizontalImage_eq_of_map_eq {M' : Type*} [LieRing M'] [LieAlgebra ℚ M']
    (A : ℕ → Submodule ℚ M) (A' : ℕ → Submodule ℚ M')
    (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L)) (ψ : M' →ₗ⁅ℚ⁆ (Fin 4 → L))
    (hφ : ∀ d x, x ∈ A d → ∀ k, φ x k ∈ F.layer d 1)
    (hψ : ∀ d x, x ∈ A' d → ∀ k, ψ x k ∈ F.layer d 1)
    (d : ℕ) (heq : (A d).map φ.toLinearMap = (A' d).map ψ.toLinearMap) :
    F.layerHorizontalImage A φ hφ d = F.layerHorizontalImage A' ψ hψ d := by
  rw [F.layerHorizontalImage_eq_of_submodule, F.layerHorizontalImage_eq_of_submodule, heq]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module

variable {ι μ L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ) (f : Basis ι ℚ (L ⧸ F.layer d 2))

noncomputable def higherHorizontalCoordinates : F.HigherHorizontal d →ₗ[ℚ] (ι → ℚ) :=
  f.equivFun.toLinearMap.comp (F.higherHorizontalAmbient d)

noncomputable def ambientHorizontalCoordinates : L →ₗ[ℚ] (ι → ℚ) :=
  f.equivFun.toLinearMap.comp (F.layer d 2).mkQ

theorem higherHorizontalCoordinates_injective : Function.Injective (F.higherHorizontalCoordinates d f) :=
  f.equivFun.injective.comp (F.higherHorizontalAmbient_injective d)

noncomputable def fourHorizontalCoordinates :
    (Fin 4 → F.HigherHorizontal d) →ₗ[ℚ] (Fin 4 → ι → ℚ) :=
  LinearMap.pi (fun k => (F.higherHorizontalCoordinates d f).comp (LinearMap.proj k))

noncomputable def fourAmbientCoordinates : (Fin 4 → L) →ₗ[ℚ] (Fin 4 → ι → ℚ) :=
  LinearMap.pi (fun k => (F.ambientHorizontalCoordinates d f).comp (LinearMap.proj k))

theorem fourHorizontalCoordinates_injective : Function.Injective (F.fourHorizontalCoordinates d f) := by
  intro x y h
  funext k
  exact F.higherHorizontalCoordinates_injective d f (congrFun h k)

theorem fourHorizontalCoordinates_map (x : F.fourHorizontalLayer d) :
    F.fourHorizontalCoordinates d f (F.fourHorizontalMap d x) =
      F.fourAmbientCoordinates d f x.val := by
  ext k i
  rfl

theorem horizontalImage_coordinates (B : Submodule ℚ (Fin 4 → L))
    (hB : B ≤ F.fourHorizontalLayer d) :
    (F.horizontalImageOfSubmodule B d).map (F.fourHorizontalCoordinates d f) =
      B.map (F.fourAmbientCoordinates d f) := by
  ext v
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x.val, hx, (F.fourHorizontalCoordinates_map d f x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    let y : F.fourHorizontalLayer d := ⟨x, hB hx⟩
    exact ⟨F.fourHorizontalMap d y, ⟨y, hx, rfl⟩, F.fourHorizontalCoordinates_map d f y⟩

theorem fourAmbientCoordinates_height [Fintype μ] (b : Basis μ ℚ L) {H K : ℕ}
    (hf : ∀ i j, RationalHeightLE (f.repr ((F.layer d 2).mkQ (b j)) i) H)
    (x : Fin 4 → L) (hx : ∀ k j, RationalHeightLE (b.repr (x k) j) K)
    (k : Fin 4) (i : ι) :
    RationalHeightLE (F.fourAmbientCoordinates d f x k i)
      ((Fintype.card μ + 1) * (K * H) ^ Fintype.card μ) :=
  linearMap_coordinate_height b f (F.layer d 2).mkQ (fun j i => hf i j) (x k) (hx k) i

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ) (f : Basis ι ℚ (L ⧸ F.layer d 2))

noncomputable def realFourCoordinateEquiv :
    (ℝ ⊗[ℚ] (Fin 4 → ι → ℚ)) ≃ₗ[ℝ] ((Σ _ : Fin 4, ι) → ℝ) :=
  ((Pi.basis (fun _ : Fin 4 => Pi.basisFun ℚ ι)).baseChange ℝ).equivFun

noncomputable def realFourHorizontalCoordinates :
    (ℝ ⊗[ℚ] (Fin 4 → F.HigherHorizontal d)) →ₗ[ℝ] ((Σ _ : Fin 4, ι) → ℝ) :=
  (realFourCoordinateEquiv (ι := ι)).toLinearMap.comp
    ((F.fourHorizontalCoordinates d f).baseChange ℝ)

noncomputable def realFourAmbientCoordinates :
    (ℝ ⊗[ℚ] (Fin 4 → L)) →ₗ[ℝ] ((Σ _ : Fin 4, ι) → ℝ) :=
  (realFourCoordinateEquiv (ι := ι)).toLinearMap.comp
    ((F.fourAmbientCoordinates d f).baseChange ℝ)

theorem realFourHorizontalCoordinates_injective :
    Function.Injective (F.realFourHorizontalCoordinates d f) := by
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  exact (realFourCoordinateEquiv (ι := ι)).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ)
      (F.fourHorizontalCoordinates d f) (F.fourHorizontalCoordinates_injective d f))

theorem realFourHorizontalCoordinates_tensor_map (x : ℝ ⊗[ℚ] F.fourHorizontalLayer d) :
    F.realFourHorizontalCoordinates d f ((F.fourHorizontalMap d).baseChange ℝ x) =
      F.realFourAmbientCoordinates d f ((F.fourHorizontalLayer d).subtype.baseChange ℝ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    change realFourCoordinateEquiv
      ((F.fourHorizontalCoordinates d f).baseChange ℝ ((F.fourHorizontalMap d).baseChange ℝ (a ⊗ₜ[ℚ] x))) =
        realFourCoordinateEquiv
          ((F.fourAmbientCoordinates d f).baseChange ℝ
            ((F.fourHorizontalLayer d).subtype.baseChange ℝ (a ⊗ₜ[ℚ] x)))
    simp only [LinearMap.baseChange_tmul, F.fourHorizontalCoordinates_map]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realFourHorizontalCoordinates_map (x : (F.fourHorizontalLayer d).baseChange ℝ) :
    F.realFourHorizontalCoordinates d f (F.realFourHorizontalMap d x) =
      F.realFourAmbientCoordinates d f x.val := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv (F.fourHorizontalLayer d)).surjective x
  rw [F.realFourHorizontalMap_baseChange]
  exact F.realFourHorizontalCoordinates_tensor_map d f v

theorem realFourHorizontalCoordinates_image (J : Submodule ℚ (Fin 4 → F.HigherHorizontal d)) :
    (J.baseChange ℝ).map (F.realFourHorizontalCoordinates d f) =
      ((J.map (F.fourHorizontalCoordinates d f)).baseChange ℝ).map
        (realFourCoordinateEquiv (ι := ι)).toLinearMap := by
  rw [realification_map]
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(F.fourHorizontalCoordinates d f).baseChange ℝ x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem realFourAmbientCoordinates_component (x : ℝ ⊗[ℚ] (Fin 4 → L)) (k : Fin 4) (i : ι) :
    F.realFourAmbientCoordinates d f x ⟨k, i⟩ =
      (f.baseChange ℝ).repr ((F.layer d 2).mkQ.baseChange ℝ ((LinearMap.proj k).baseChange ℝ x)) i := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    change ((Pi.basis (fun _ : Fin 4 => Pi.basisFun ℚ ι)).baseChange ℝ).repr
      (a ⊗ₜ[ℚ] F.fourAmbientCoordinates d f x) ⟨k, i⟩ =
        (f.baseChange ℝ).repr (a ⊗ₜ[ℚ] (F.layer d 2).mkQ (x k)) i
    rw [Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul, Pi.basis_repr]
    rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, Finsupp.add_apply, hx, hy]

theorem realFourHorizontalCoordinates_component
    (x : ℝ ⊗[ℚ] (Fin 4 → F.HigherHorizontal d)) (k : Fin 4) (i : ι) :
    F.realFourHorizontalCoordinates d f x ⟨k, i⟩ =
      (f.baseChange ℝ).repr
        ((F.higherHorizontalAmbient d).baseChange ℝ ((LinearMap.proj k).baseChange ℝ x)) i := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    change ((Pi.basis (fun _ : Fin 4 => Pi.basisFun ℚ ι)).baseChange ℝ).repr
      (a ⊗ₜ[ℚ] F.fourHorizontalCoordinates d f x) ⟨k, i⟩ =
        (f.baseChange ℝ).repr (a ⊗ₜ[ℚ] F.higherHorizontalAmbient d (x k)) i
    rw [Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul, Pi.basis_repr]
    rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, Finsupp.add_apply, hx, hy]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ : Type*} [Fintype ι]

noncomputable def realRationalCoordinateEquiv : (ℝ ⊗[ℚ] (ι → ℚ)) ≃ₗ[ℝ] (ι → ℝ) :=
  ((Pi.basisFun ℚ ι).baseChange ℝ).equivFun

theorem realRationalCoordinateEquiv_tmul (a : ℝ) (x : ι → ℚ) (i : ι) :
    realRationalCoordinateEquiv (a ⊗ₜ[ℚ] x) i = a * (x i : ℝ) := by
  change ((Pi.basisFun ℚ ι).baseChange ℝ).repr (a ⊗ₜ[ℚ] x) i = _
  rw [Basis.baseChange_repr_tmul]
  change (x i) • a = _
  simp only [Rat.smul_def, mul_comm]

theorem realFourCoordinateEquiv_tmul (a : ℝ) (x : Fin 4 → ι → ℚ) (j : Σ _ : Fin 4, ι) :
    DegreeRankLieFiltration.realFourCoordinateEquiv (a ⊗ₜ[ℚ] x) j = a * (x j.1 j.2 : ℝ) := by
  change ((Pi.basis (fun _ : Fin 4 => Pi.basisFun ℚ ι)).baseChange ℝ).repr
    (a ⊗ₜ[ℚ] x) j = _
  rw [Basis.baseChange_repr_tmul, Pi.basis_repr]
  change (x j.1 j.2) • a = _
  simp only [Rat.smul_def, mul_comm]

noncomputable def realRationalCoordinateSpan (U : Submodule ℚ (ι → ℚ)) : Submodule ℝ (ι → ℝ) :=
  (U.baseChange ℝ).map realRationalCoordinateEquiv.toLinearMap

noncomputable def realFourCoordinateSpan (J : Submodule ℚ (Fin 4 → ι → ℚ)) :
    Submodule ℝ ((Σ _ : Fin 4, ι) → ℝ) :=
  (J.baseChange ℝ).map DegreeRankLieFiltration.realFourCoordinateEquiv.toLinearMap

theorem realCoordinate_projection (x : ℝ ⊗[ℚ] (Fin 4 → ι → ℚ)) (k : Fin 4) (i : ι) :
    realRationalCoordinateEquiv ((LinearMap.proj k).baseChange ℝ x) i =
      DegreeRankLieFiltration.realFourCoordinateEquiv x ⟨k, i⟩ := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, realRationalCoordinateEquiv_tmul, realFourCoordinateEquiv_tmul]
    rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem realFourCoordinateSpan_span (v : κ → Fin 4 → ι → ℚ) :
    realFourCoordinateSpan (Submodule.span ℚ (Set.range v)) =
      Submodule.span ℝ (Set.range (fun a (j : Σ _ : Fin 4, ι) => (v a j.1 j.2 : ℝ))) := by
  unfold realFourCoordinateSpan
  rw [Submodule.baseChange_span, Submodule.map_span, Set.image_image]
  apply congrArg (Submodule.span ℝ)
  ext x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    refine ⟨a, ?_⟩
    funext j
    change (v a j.1 j.2 : ℝ) =
      DegreeRankLieFiltration.realFourCoordinateEquiv (1 ⊗ₜ[ℚ] v a) j
    simpa only [one_mul] using (realFourCoordinateEquiv_tmul (1 : ℝ) (v a) j).symm
  · rintro ⟨a, rfl⟩
    refine ⟨v a, ⟨a, rfl⟩, ?_⟩
    funext j
    change DegreeRankLieFiltration.realFourCoordinateEquiv (1 ⊗ₜ[ℚ] v a) j =
      (v a j.1 j.2 : ℝ)
    simpa only [one_mul] using realFourCoordinateEquiv_tmul (1 : ℝ) (v a) j

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {L ι μ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  {E V : Submodule ℚ L}

noncomputable def realQuotientCoordinateMap (f : Basis ι ℚ (L ⧸ V)) :
    (ℝ ⊗[ℚ] L) →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.pi (fun i => ((f.baseChange ℝ).coord i).comp (V.mkQ.baseChange ℝ))

@[simp] theorem realQuotientCoordinateMap_apply (f : Basis ι ℚ (L ⧸ V))
    (x : ℝ ⊗[ℚ] L) (i : ι) :
    realQuotientCoordinateMap f x i = (f.baseChange ℝ).repr (V.mkQ.baseChange ℝ x) i := rfl

theorem realQuotientCoordinateMap_tmul_one (f : Basis ι ℚ (L ⧸ V)) (x : L) (i : ι) :
    realQuotientCoordinateMap f ((1 : ℝ) ⊗ₜ[ℚ] x) i = (f.repr (V.mkQ x) i : ℝ) := by
  rw [realQuotientCoordinateMap_apply, LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def]

theorem realQuotientCoordinateMap_eq_zero_iff (f : Basis ι ℚ (L ⧸ V)) (x : ℝ ⊗[ℚ] L) :
    realQuotientCoordinateMap f x = 0 ↔ x ∈ V.baseChange ℝ := by
  rw [← realification_mkQ_eq_zero_iff]
  constructor
  · intro h
    apply (f.baseChange ℝ).repr.injective
    ext i
    simpa only [realQuotientCoordinateMap_apply, map_zero, Finsupp.zero_apply, Pi.zero_apply]
      using congrFun h i
  · intro h
    funext i
    simp only [realQuotientCoordinateMap_apply, h, map_zero, Finsupp.zero_apply, Pi.zero_apply]

noncomputable def subspaceQuotientMatrix (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) :
    Matrix ι ν ℚ := fun i n => f.repr (V.mkQ (e n : L)) i

theorem subspaceQuotientMatrix_real_apply [Fintype ν]
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (x : ν → ℝ) :
    (fun i n => (subspaceQuotientMatrix e f i n : ℝ)) *ᵥ x =
      realQuotientCoordinateMap f (bracketSystemLift e x) := by
  classical
  have h : Matrix.mulVecLin (fun i n => (subspaceQuotientMatrix e f i n : ℝ)) =
      (realQuotientCoordinateMap f).comp (bracketSystemLift e) := by
    apply (Pi.basisFun ℝ ν).ext
    intro n
    change Matrix.of (fun i t => (subspaceQuotientMatrix e f i t : ℝ)) *ᵥ Pi.single n 1 =
      realQuotientCoordinateMap f (bracketSystemLift e (Pi.single n 1))
    rw [Matrix.mulVec_single_one, bracketSystemLift_single]
    funext i
    exact (realQuotientCoordinateMap_tmul_one f (e n : L) i).symm
  exact DFunLike.congr_fun h x

theorem exists_subspace_basis_coordinates [Fintype ν] (e : Basis ν ℚ E)
    (x : ℝ ⊗[ℚ] L) (hx : x ∈ E.baseChange ℝ) :
    ∃ v : ν → ℝ, bracketSystemLift e v = x := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨(e.baseChange ℝ).equivFun y, ?_⟩
  simp only [bracketSystemLift, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

theorem subspaceQuotientMatrix_height [Fintype μ] (b : Basis μ ℚ L)
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) {H J : ℕ}
    (hq : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b i)) n) H)
    (he : ∀ n i, RationalHeightLE (b.repr (e n : L) i) J) (i : ι) (n : ν) :
    RationalHeightLE (subspaceQuotientMatrix e f i n)
      ((Fintype.card μ + 1) * (J * H) ^ Fintype.card μ) :=
  linearMap_coordinate_height b f V.mkQ hq (e n : L) (he n) i

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {ι κ : Type*} [Fintype ι]

theorem realRationalCoordinateSpan_span (v : κ → ι → ℚ) :
    realRationalCoordinateSpan (Submodule.span ℚ (Set.range v)) =
      Submodule.span ℝ (Set.range (fun a i => (v a i : ℝ))) := by
  unfold realRationalCoordinateSpan
  rw [Submodule.baseChange_span, Submodule.map_span, Set.image_image]
  apply congrArg (Submodule.span ℝ)
  ext x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    refine ⟨a, ?_⟩
    funext i
    change (v a i : ℝ) = realRationalCoordinateEquiv (1 ⊗ₜ[ℚ] v a) i
    simpa only [one_mul] using (realRationalCoordinateEquiv_tmul (1 : ℝ) (v a) i).symm
  · rintro ⟨a, rfl⟩
    refine ⟨v a, ⟨a, rfl⟩, ?_⟩
    funext i
    change realRationalCoordinateEquiv (1 ⊗ₜ[ℚ] v a) i = (v a i : ℝ)
    simpa only [one_mul] using realRationalCoordinateEquiv_tmul (1 : ℝ) (v a) i

theorem realRationalCoordinateSpan_eq_image [Fintype κ]
    (U : Submodule ℚ (ι → ℚ)) (v : κ → ι → ℚ)
    (hv : Submodule.span ℚ (Set.range v) = U) :
    realRationalCoordinateSpan U =
      LinearMap.range (Matrix.mulVecLin (fun i a => (v a i : ℝ))) := by
  rw [← hv, realRationalCoordinateSpan_span]
  ext x
  exact real_column_span_mem_iff (fun i a => v a i) x

end Erdos3

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ) (f : Basis ι ℚ (L ⧸ F.layer d 2))

noncomputable def realHigherHorizontalCoordinates : (ℝ ⊗[ℚ] F.HigherHorizontal d) →ₗ[ℝ] (ι → ℝ) :=
  realRationalCoordinateEquiv.toLinearMap.comp ((F.higherHorizontalCoordinates d f).baseChange ℝ)

theorem realHigherHorizontalCoordinates_component (x : ℝ ⊗[ℚ] F.HigherHorizontal d) (i : ι) :
    F.realHigherHorizontalCoordinates d f x i =
      (f.baseChange ℝ).repr ((F.higherHorizontalAmbient d).baseChange ℝ x) i := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    change ((Pi.basisFun ℚ ι).baseChange ℝ).repr
      (a ⊗ₜ[ℚ] F.higherHorizontalCoordinates d f x) i =
        (f.baseChange ℝ).repr (a ⊗ₜ[ℚ] F.higherHorizontalAmbient d x) i
    rw [Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul]
    rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, Finsupp.add_apply, hx, hy]

theorem realHigherHorizontalCoordinates_injective :
    Function.Injective (F.realHigherHorizontalCoordinates d f) := by
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  exact realRationalCoordinateEquiv.injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ)
      (F.higherHorizontalCoordinates d f) (F.higherHorizontalCoordinates_injective d f))

theorem realHigherHorizontalCoordinates_image (U : Submodule ℚ (F.HigherHorizontal d)) :
    (U.baseChange ℝ).map (F.realHigherHorizontalCoordinates d f) =
      realRationalCoordinateSpan (U.map (F.higherHorizontalCoordinates d f)) := by
  unfold realRationalCoordinateSpan
  rw [realification_map]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(F.higherHorizontalCoordinates d f).baseChange ℝ x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {L ι μ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype ι] [Fintype μ] {V : Submodule ℚ L}

noncomputable def quotientCoordinateMatrix (b : Basis μ ℚ L) (f : Basis ι ℚ (L ⧸ V)) :
    Matrix ι μ ℚ := fun i j => f.repr (V.mkQ (b j)) i

omit [Fintype ι] in
theorem realQuotientCoordinateMap_eq_matrix (b : Basis μ ℚ L) (f : Basis ι ℚ (L ⧸ V))
    (x : ℝ ⊗[ℚ] L) :
    realQuotientCoordinateMap f x =
      (fun i j => (quotientCoordinateMatrix b f i j : ℝ)) *ᵥ (b.baseChange ℝ).equivFun x := by
  classical
  have h : (realQuotientCoordinateMap f).comp
      (b.baseChange ℝ).equivFun.symm.toLinearMap =
        Matrix.mulVecLin (fun i j => (quotientCoordinateMatrix b f i j : ℝ)) := by
    apply (Pi.basisFun ℝ μ).ext
    intro j
    change realQuotientCoordinateMap f ((b.baseChange ℝ).equivFun.symm (Pi.single j 1)) =
      Matrix.of (fun i n => (quotientCoordinateMatrix b f i n : ℝ)) *ᵥ Pi.single j 1
    rw [Basis.equivFun_symm_single, Matrix.mulVec_single_one, Basis.baseChange_apply]
    funext i
    exact realQuotientCoordinateMap_tmul_one f (b j) i
  have hx := DFunLike.congr_fun h ((b.baseChange ℝ).equivFun x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at hx
  exact hx.trans (Matrix.mulVecLin_apply _ _)

theorem realQuotientCoordinateMap_norm_bound (b : Basis μ ℚ L) (f : Basis ι ℚ (L ⧸ V))
    {H : ℕ} (hf : ∀ i j, RationalHeightLE (f.repr (V.mkQ (b j)) i) H)
    (x : ℝ ⊗[ℚ] L) :
    ‖realQuotientCoordinateMap f x‖ ≤
      ((Fintype.card μ : ℝ) + 1) * (H + 1) * ‖(b.baseChange ℝ).equivFun x‖ := by
  rw [realQuotientCoordinateMap_eq_matrix b f x]
  exact norm_matrix_mulVec_le _ (H : ℝ≥0) (fun i j => (hf i j).abs_real_le) _

theorem realQuotientCoordinateMap_grid (b : Basis μ ℚ L) (f : Basis ι ℚ (L ⧸ V))
    (l : ℕ) (x : ℝ ⊗[ℚ] L) (hx : (b.baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    realQuotientCoordinateMap f x ∈
      realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix b f) * l) := by
  rw [realQuotientCoordinateMap_eq_matrix b f x]
  exact real_matrix_denominator_grid (quotientCoordinateMatrix b f) l _ hx

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem real_pi_projection_coordinates {μ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (b : Basis μ ℚ L) (x : ℝ ⊗[ℚ] (Fin 4 → L)) (k : Fin 4) (i : μ) :
    (b.baseChange ℝ).repr ((LinearMap.proj k).baseChange ℝ x) i =
      ((Pi.basis (fun _ : Fin 4 => b)).baseChange ℝ).repr x ⟨k, i⟩ :=
  (realification_pi_basis_repr (fun _ : Fin 4 => b) x k i).symm

namespace DegreeRankLieFiltration

variable {ι μ L : Type*} [Fintype ι] [Fintype μ] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ) (f : Basis ι ℚ (L ⧸ F.layer d 2))
  (b : Basis μ ℚ L)

theorem realFourAmbientCoordinates_bound {H : ℕ}
    (hf : ∀ i j, RationalHeightLE (f.repr ((F.layer d 2).mkQ (b j)) i) H)
    (x : ℝ ⊗[ℚ] (Fin 4 → L)) {B : ℝ} (hB : 0 ≤ B)
    (hx : ∀ j, |((Pi.basis (fun _ : Fin 4 => b)).baseChange ℝ).repr x j| ≤ B)
    (k : Fin 4) (i : ι) :
    |F.realFourAmbientCoordinates d f x ⟨k, i⟩| ≤
      ((Fintype.card μ : ℝ) + 1) * (H + 1) * B := by
  let y := (LinearMap.proj k).baseChange ℝ x
  have hy : ‖(b.baseChange ℝ).equivFun y‖ ≤ B := by
    apply (pi_norm_le_iff_of_nonneg hB).mpr
    intro j
    rw [Real.norm_eq_abs]
    change |(b.baseChange ℝ).repr ((LinearMap.proj k).baseChange ℝ x) j| ≤ B
    rw [real_pi_projection_coordinates]
    exact hx ⟨k, j⟩
  rw [F.realFourAmbientCoordinates_component]
  calc
    _ = ‖realQuotientCoordinateMap f y i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖realQuotientCoordinateMap f y‖ := norm_le_pi_norm _ i
    _ ≤ ((Fintype.card μ : ℝ) + 1) * (H + 1) * ‖(b.baseChange ℝ).equivFun y‖ :=
      realQuotientCoordinateMap_norm_bound b f hf y
    _ ≤ _ := mul_le_mul_of_nonneg_left hy (by positivity)

theorem realFourAmbientCoordinates_grid (l : ℕ) (x : ℝ ⊗[ℚ] (Fin 4 → L))
    (hx : (fun j => ((Pi.basis (fun _ : Fin 4 => b)).baseChange ℝ).repr x j) ∈ realDenominatorGrid l) :
    F.realFourAmbientCoordinates d f x ∈
      realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix b f) * l) := by
  obtain ⟨z, hz⟩ := hx
  have hsource (k : Fin 4) :
      (b.baseChange ℝ).equivFun ((LinearMap.proj k).baseChange ℝ x) ∈ realDenominatorGrid l := by
    refine ⟨fun i => z ⟨k, i⟩, ?_⟩
    funext i
    exact (congrFun hz ⟨k, i⟩).trans
      (congrArg (fun y : ℝ => (l : ℝ) * y) (real_pi_projection_coordinates b x k i).symm)
  choose a ha using fun k => realQuotientCoordinateMap_grid b f l
    ((LinearMap.proj k).baseChange ℝ x) (hsource k)
  refine ⟨fun j => a j.1 j.2, ?_⟩
  funext j
  exact (congrFun (ha j.1) j.2).trans
    (congrArg (fun y : ℝ => ((matrixDenominator (quotientCoordinateMatrix b f) * l : ℕ) : ℝ) * y)
      (F.realFourAmbientCoordinates_component d f x j.1 j.2).symm)

end DegreeRankLieFiltration

end Erdos3

end

end OAI
