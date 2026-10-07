/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.ReducedNativeFactorization
import OAI.Combinatorics.Progressions.Geometry.RealSubspaceCoordinateRetraction
import OAI.Combinatorics.Progressions.Linear.BaseChangeCoordinateProjection
import OAI.Combinatorics.Progressions.Linear.RealFirstCoefficientBasis

namespace OAI

section

namespace Erdos3

open Module

variable {K E H : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup H] [Module K H] {a d : ℕ}

def extendInitialCoordinates : (Fin a → K) →ₗ[K] (Fin d → K) where
  toFun x j := if h : j.val < a then x ⟨j.val, h⟩ else 0
  map_add' x y := by funext j; by_cases h : j.val < a <;> simp [h]
  map_smul' c x := by funext j; by_cases h : j.val < a <;> simp [h]

@[simp] theorem extendInitialCoordinates_castLE (ha : a ≤ d) (x : Fin a → K) (i : Fin a) :
    extendInitialCoordinates x (Fin.castLE ha i) = x i := by
  simp [extendInitialCoordinates, i.isLt]

noncomputable def initialHorizontalEquiv (ha : a ≤ d) (b : Basis (Fin d) K E)
    (P : E →ₗ[K] H) (S : H →ₗ[K] E)
    (hsection : ∀ x, P (S x) = x)
    (hproj : ∀ x j, b.equivFun (S (P x)) j =
      if j.val < a then b.equivFun x j else 0) : (Fin a → K) ≃ₗ[K] H where
  toFun y := P (b.equivFun.symm (extendInitialCoordinates y))
  invFun x i := b.equivFun (S x) (Fin.castLE ha i)
  left_inv y := by
    funext i
    change b.equivFun (S (P (b.equivFun.symm (extendInitialCoordinates y))))
      (Fin.castLE ha i) = y i
    rw [hproj]
    simp only [LinearEquiv.apply_symm_apply, Fin.val_castLE, i.isLt, ite_true,
      extendInitialCoordinates_castLE]
  right_inv x := by
    have he : b.equivFun.symm
        (extendInitialCoordinates (fun i => b.equivFun (S x) (Fin.castLE ha i))) = S x := by
      apply b.equivFun.injective
      funext j
      rw [LinearEquiv.apply_symm_apply]
      change (if h : j.val < a then
        b.equivFun (S x) (Fin.castLE ha ⟨j.val, h⟩) else 0) = b.equivFun (S x) j
      split_ifs with hj
      · rfl
      · have h := hproj (S x) j
        simpa only [hsection, hj, ite_false] using h.symm
    change P (b.equivFun.symm
      (extendInitialCoordinates (fun i => b.equivFun (S x) (Fin.castLE ha i)))) = x
    rw [he, hsection]
  map_add' x y := by simp only [map_add]
  map_smul' c x := by simp only [map_smul, RingHom.id_apply]

theorem initialHorizontalEquiv_symm_projection (ha : a ≤ d) (b : Basis (Fin d) K E)
    (P : E →ₗ[K] H) (S : H →ₗ[K] E)
    (hsection : ∀ x, P (S x) = x)
    (hproj : ∀ x j, b.equivFun (S (P x)) j =
      if j.val < a then b.equivFun x j else 0) (x : E) :
    (initialHorizontalEquiv ha b P S hsection hproj).symm (P x) =
      fun i => b.equivFun x (Fin.castLE ha i) := by
  funext i
  change b.equivFun (S (P x)) (Fin.castLE ha i) = _
  rw [hproj]
  simp only [Fin.val_castLE, i.isLt, ite_true]

theorem initialHorizontalEquiv_projection (ha : a ≤ d) (b : Basis (Fin d) K E)
    (P : E →ₗ[K] H) (S : H →ₗ[K] E)
    (hsection : ∀ x, P (S x) = x)
    (hproj : ∀ x j, b.equivFun (S (P x)) j =
      if j.val < a then b.equivFun x j else 0) (x : E) :
    initialHorizontalEquiv ha b P S hsection hproj
      (fun i => b.equivFun x (Fin.castLE ha i)) = P x := by
  rw [← initialHorizontalEquiv_symm_projection ha b P S hsection hproj x,
    LinearEquiv.apply_symm_apply]

end Erdos3

end

section

namespace Erdos3

theorem realDenominatorGrid_single {ι : Type*} [DecidableEq ι] (l : ℕ) (i : ι) :
    Pi.single i (1 : ℝ) ∈ realDenominatorGrid l := by
  refine ⟨Pi.single i (l : ℤ), ?_⟩
  funext j
  change ((Pi.single i (l : ℤ) : ι → ℤ) j : ℝ) =
    (l : ℝ) * (Pi.single i (1 : ℝ) : ι → ℝ) j
  by_cases h : j = i <;> simp [h]

theorem extendInitialCoordinates_grid {a d : ℕ} (l : ℕ) (x : Fin a → ℝ)
    (hx : x ∈ realDenominatorGrid l) :
    (extendInitialCoordinates x : Fin d → ℝ) ∈ realDenominatorGrid l := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨fun i => if hi : i.val < a then z ⟨i.val, hi⟩ else 0, ?_⟩
  funext i
  change ((if hi : i.val < a then z ⟨i.val, hi⟩ else 0 : ℤ) : ℝ) =
    (l : ℝ) * (if hi : i.val < a then x ⟨i.val, hi⟩ else 0)
  by_cases hi : i.val < a
  · simpa only [hi, dite_true, Pi.smul_apply, smul_eq_mul] using congrFun hz ⟨i.val, hi⟩
  · simp only [hi, dite_false, Int.cast_zero, mul_zero]

theorem norm_extendInitialCoordinates_le {a d : ℕ} (x : Fin a → ℝ) :
    ‖(extendInitialCoordinates x : Fin d → ℝ)‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  change ‖if hi : i.val < a then x ⟨i.val, hi⟩ else 0‖ ≤ ‖x‖
  split_ifs with hi
  · exact norm_le_pi_norm x ⟨i.val, hi⟩
  · simpa only [norm_zero] using norm_nonneg x

theorem norm_extendInitialCoordinates {a d : ℕ} (ha : a ≤ d) (x : Fin a → ℝ) :
    ‖(extendInitialCoordinates x : Fin d → ℝ)‖ = ‖x‖ := by
  apply le_antisymm (norm_extendInitialCoordinates_le x)
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  have h := norm_le_pi_norm (extendInitialCoordinates x : Fin d → ℝ) (Fin.castLE ha i)
  simpa only [extendInitialCoordinates_castLE] using h

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem firstCoefficientHorizontal_projector_repr
    (x : F.FirstCoefficientModule w) (z : FirstCoefficientIndex w ω) :
    (F.firstCoefficientBasis b ω hF w).repr
        (F.firstCoefficientHorizontalSection w (F.firstCoefficientHorizontal w x)) z =
      if z.val.1 = 0 then (F.firstCoefficientBasis b ω hF w).repr x z else 0 := by
  classical
  obtain ⟨p, rfl⟩ := F.firstCoefficientMap_surjective w x
  rw [F.firstCoefficientHorizontal_map, F.firstCoefficientHorizontalSection_mk]
  change (F.firstCoefficientBasis b ω hF w).repr
      (F.firstCoefficientMap w ⟨F.adaptedConstant w (coefficients p.val.val 0), _⟩) z = _
  rw [F.firstCoefficientBasis_repr_map, F.firstCoefficientBasis_repr_map]
  change b.repr (coefficients (monomial 0 (coefficients p.val.val 0)) z.val.1) z.val.2 = _
  by_cases hz : z.val.1 = 0
  · simp [hz, coefficients_monomial]
  · simp [hz, coefficients_monomial, Finsupp.single_eq_of_ne hz]

theorem firstCoefficientHorizontal_projector (x : F.FirstCoefficientModule w) :
    F.firstCoefficientHorizontalSection w (F.firstCoefficientHorizontal w x) =
      basisCoordinateProjection (F.firstCoefficientBasis b ω hF w) {z | z.val.1 = 0} x := by
  classical
  apply (F.firstCoefficientBasis b ω hF w).repr.injective
  ext z
  rw [F.firstCoefficientHorizontal_projector_repr, basisCoordinateProjection_repr]
  rfl

theorem firstCoefficientHorizontal_eq_zero_iff
    (x : F.FirstCoefficientModule w) :
    F.firstCoefficientHorizontal w x = 0 ↔
      ∀ z : FirstCoefficientIndex w ω, z.val.1 = 0 →
        (F.firstCoefficientBasis b ω hF w).repr x z = 0 := by
  classical
  constructor
  · intro hx z hz
    have h := F.firstCoefficientHorizontal_projector_repr b ω hF w x z
    simpa only [hx, map_zero, Finsupp.zero_apply, hz, ite_true] using h.symm
  · intro hx
    have hp : F.firstCoefficientHorizontalSection w (F.firstCoefficientHorizontal w x) = 0 := by
      apply (F.firstCoefficientBasis b ω hF w).repr.injective
      ext z
      rw [F.firstCoefficientHorizontal_projector_repr, map_zero, Finsupp.zero_apply]
      split_ifs with hz
      · exact hx z hz
      · rfl
    have h := congrArg (F.firstCoefficientHorizontal w) hp
    simpa only [F.firstCoefficientHorizontal_section, map_zero] using h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem firstCoefficientRealEquiv_coordinates (x : ℝ ⊗[ℚ] F.FirstCoefficientModule w)
    (z : FirstCoefficientIndex w ω) :
    (F.realFirstCoefficientBasis b ω hF w).repr (F.firstCoefficientRealEquiv w x) z =
      ((F.firstCoefficientBasis b ω hF w).baseChange ℝ).repr x z := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul r x =>
    obtain ⟨p, rfl⟩ := F.firstCoefficientMap_surjective w x
    have ht : r ⊗ₜ[ℚ] F.firstCoefficientMap w p =
        (F.firstCoefficientMap w).baseChange ℝ (r ⊗ₜ[ℚ] p) := rfl
    rw [ht, F.firstCoefficientRealEquiv_map]
    let q : F.realShiftedCoefficientSubmodule w 1 :=
      ⟨r ⊗ₜ[ℚ] p.val, Submodule.tmul_mem_baseChange_of_mem r p.property⟩
    change (F.realFirstCoefficientBasis b ω hF w).repr (F.realFirstCoefficientMap w q) z =
      ((F.firstCoefficientBasis b ω hF w).baseChange ℝ).repr (r ⊗ₜ[ℚ] F.firstCoefficientMap w p) z
    rw [F.realFirstCoefficientBasis_repr_map]
    change ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ).repr (r ⊗ₜ[ℚ] p.val)
        ((firstCoefficientSurvivorEquiv w ω).symm z).val.val =
      ((F.firstCoefficientBasis b ω hF w).baseChange ℝ).repr (r ⊗ₜ[ℚ] F.firstCoefficientMap w p) z
    rw [Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul,
      F.adaptedMonomialBasis_repr, F.firstCoefficientBasis_repr_map]
    rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realFirstCoefficientHorizontal_projector_repr
    (x : F.RealFirstCoefficientModule w) (z : FirstCoefficientIndex w ω) :
    (F.realFirstCoefficientBasis b ω hF w).repr
        (F.realFirstCoefficientHorizontalSection w (F.realFirstCoefficientHorizontal w x)) z =
      if z.val.1 = 0 then (F.realFirstCoefficientBasis b ω hF w).repr x z else 0 := by
  classical
  obtain ⟨x, rfl⟩ := (F.firstCoefficientRealEquiv w).surjective x
  change (F.realFirstCoefficientBasis b ω hF w).repr
    (F.firstCoefficientRealEquiv w ((F.firstCoefficientHorizontalSection w).baseChange ℝ
      ((F.firstCoefficientHorizontal w).baseChange ℝ
        ((F.firstCoefficientRealEquiv w).symm (F.firstCoefficientRealEquiv w x))))) z = _
  rw [LinearEquiv.symm_apply_apply, F.firstCoefficientRealEquiv_coordinates,
    F.firstCoefficientRealEquiv_coordinates]
  exact baseChange_coordinate_projector_repr (F.firstCoefficientBasis b ω hF w)
    (F.firstCoefficientHorizontal w) (F.firstCoefficientHorizontalSection w)
    (fun z => z.val.1 = 0) (F.firstCoefficientHorizontal_projector_repr b ω hF w) x z

theorem realFirstCoefficientHorizontal_projector (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientHorizontalSection w (F.realFirstCoefficientHorizontal w x) =
      basisCoordinateProjection (F.realFirstCoefficientBasis b ω hF w) {z | z.val.1 = 0} x := by
  classical
  apply (F.realFirstCoefficientBasis b ω hF w).repr.injective
  ext z
  rw [F.realFirstCoefficientHorizontal_projector_repr, basisCoordinateProjection_repr]
  rfl

theorem realFirstCoefficientHorizontal_eq_zero_iff
    (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientHorizontal w x = 0 ↔
      ∀ z : FirstCoefficientIndex w ω, z.val.1 = 0 →
        (F.realFirstCoefficientBasis b ω hF w).repr x z = 0 := by
  classical
  constructor
  · intro hx z hz
    have h := F.realFirstCoefficientHorizontal_projector_repr b ω hF w x z
    simpa only [hx, map_zero, Finsupp.zero_apply, hz, ite_true] using h.symm
  · intro hx
    have hp : F.realFirstCoefficientHorizontalSection w (F.realFirstCoefficientHorizontal w x) = 0 := by
      apply (F.realFirstCoefficientBasis b ω hF w).repr.injective
      ext z
      rw [F.realFirstCoefficientHorizontal_projector_repr, map_zero, Finsupp.zero_apply]
      split_ifs with hz
      · exact hx z hz
      · rfl
    have h := congrArg (F.realFirstCoefficientHorizontal w) hp
    simpa only [F.realFirstCoefficientHorizontal_section, map_zero] using h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
  (b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
    F.realFirstCoefficientFastSubmodule w hw U))
  (rows : Fin d → FirstCoefficientIndex w ω)
  (hblock : ∀ i j, (rows j).val.1 ≠ i.val.1 →
    b.repr ((F.realFirstCoefficientFastSubmodule w hw U).mkQ
      (F.realFirstCoefficientBasis e ω hF w i)) j = 0)

include hblock

theorem realFastCoefficientHorizontal_projector
    (x : F.RealFirstCoefficientModule w ⧸ F.realFirstCoefficientFastSubmodule w hw U) :
    F.realFastCoefficientHorizontalSection w hw U (F.realFastCoefficientHorizontal w hw U x) =
      basisCoordinateProjection b {j | (rows j).val.1 = 0} x := by
  classical
  obtain ⟨x, rfl⟩ := (F.realFirstCoefficientFastSubmodule w hw U).mkQ_surjective x
  change (F.realFirstCoefficientFastSubmodule w hw U).mkQ
    (F.realFirstCoefficientHorizontalSection w (F.realFirstCoefficientHorizontal w x)) = _
  rw [F.realFirstCoefficientHorizontal_projector e ω hF w]
  exact basisBlockMap_commutes (F.realFirstCoefficientBasis e ω hF w) b
    (fun i => i.val.1) (fun j => (rows j).val.1)
    (F.realFirstCoefficientFastSubmodule w hw U).mkQ hblock 0 x

theorem realFastCoefficientHorizontal_projector_repr
    (x : F.RealFirstCoefficientModule w ⧸ F.realFirstCoefficientFastSubmodule w hw U)
    (j : Fin d) :
    b.repr (F.realFastCoefficientHorizontalSection w hw U
      (F.realFastCoefficientHorizontal w hw U x)) j =
      if (rows j).val.1 = 0 then b.repr x j else 0 := by
  rw [F.realFastCoefficientHorizontal_projector e ω hF w hw U b rows hblock]
  exact basisCoordinateProjection_repr b {j | (rows j).val.1 = 0} x j

noncomputable def realFastCoefficientHorizontalEquiv {a : ℕ} (ha : a ≤ d)
    (hprefix : ∀ j, j.val < a ↔ (rows j).val.1 = 0) :
    (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :=
  initialHorizontalEquiv ha b (F.realFastCoefficientHorizontal w hw U)
    (F.realFastCoefficientHorizontalSection w hw U)
    (F.realFastCoefficientHorizontal_section w hw U) (fun x j => by
      change b.repr (F.realFastCoefficientHorizontalSection w hw U
        (F.realFastCoefficientHorizontal w hw U x)) j = _
      rw [F.realFastCoefficientHorizontal_projector_repr e ω hF w hw U b rows hblock]
      simp only [← hprefix j, Basis.equivFun_apply])

theorem realFastCoefficientHorizontalEquiv_projection {a : ℕ} (ha : a ≤ d)
    (hprefix : ∀ j, j.val < a ↔ (rows j).val.1 = 0)
    (x : F.RealFirstCoefficientModule w ⧸ F.realFirstCoefficientFastSubmodule w hw U) :
    F.realFastCoefficientHorizontalEquiv e ω hF w hw U b rows hblock ha hprefix
      (fun i => b.equivFun x (Fin.castLE ha i)) = F.realFastCoefficientHorizontal w hw U x :=
  initialHorizontalEquiv_projection ha b (F.realFastCoefficientHorizontal w hw U)
    (F.realFastCoefficientHorizontalSection w hw U)
    (F.realFastCoefficientHorizontal_section w hw U) _ x

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct Matrix

section Ambient

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem firstCoefficientRealEquiv_basis (i : FirstCoefficientIndex w ω) :
    F.firstCoefficientRealEquiv w ((F.firstCoefficientBasis e ω hF w).baseChange ℝ i) =
      F.realFirstCoefficientBasis e ω hF w i := by
  apply (F.realFirstCoefficientBasis e ω hF w).repr.injective
  ext j
  rw [F.firstCoefficientRealEquiv_coordinates]
  simp only [Basis.repr_self]

end Ambient

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

noncomputable def fastCoefficientRealEquiv :
    (ℝ ⊗[ℚ] (F.FirstCoefficientModule w ⧸ F.firstCoefficientFastSubmodule w hw U)) ≃ₗ[ℝ]
      (F.RealFirstCoefficientModule w ⧸ F.realFirstCoefficientFastSubmodule w hw U) :=
  realTransportedQuotientEquiv (F.firstCoefficientFastSubmodule w hw U)
    (F.firstCoefficientRealEquiv w)

theorem fastCoefficientRealEquiv_mk (x : ℝ ⊗[ℚ] F.FirstCoefficientModule w) :
    F.fastCoefficientRealEquiv w hw U
        ((F.firstCoefficientFastSubmodule w hw U).mkQ.baseChange ℝ x) =
      (F.realFirstCoefficientFastSubmodule w hw U).mkQ (F.firstCoefficientRealEquiv w x) :=
  realTransportedQuotientEquiv_mk _ _ x

noncomputable def realFastCoefficientBasis
    (b : Basis κ ℚ (F.FirstCoefficientModule w ⧸ F.firstCoefficientFastSubmodule w hw U)) :
    Basis κ ℝ (F.RealFirstCoefficientModule w ⧸ F.realFirstCoefficientFastSubmodule w hw U) :=
  realTransportedQuotientBasis (F.firstCoefficientFastSubmodule w hw U)
    (F.firstCoefficientRealEquiv w) b

theorem realFastCoefficientBasis_repr_basis
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (b : Basis κ ℚ (F.FirstCoefficientModule w ⧸ F.firstCoefficientFastSubmodule w hw U))
    (i : FirstCoefficientIndex w ω) (j : κ) :
    (F.realFastCoefficientBasis w hw U b).repr
        ((F.realFirstCoefficientFastSubmodule w hw U).mkQ
          (F.realFirstCoefficientBasis e ω hF w i)) j =
      (b.repr ((F.firstCoefficientFastSubmodule w hw U).mkQ
        (F.firstCoefficientBasis e ω hF w i)) j : ℝ) := by
  rw [← F.firstCoefficientRealEquiv_basis e ω hF w i]
  exact realTransportedQuotientBasis_repr_basis _ _ _ b i j

theorem realFastCoefficientBasis_matrix
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
    [Fintype κ] [DecidableEq κ]
    (b : Basis κ ℚ (F.FirstCoefficientModule w ⧸ F.firstCoefficientFastSubmodule w hw U)) :
    LinearMap.toMatrix (F.realFirstCoefficientBasis e ω hF w)
        (F.realFastCoefficientBasis w hw U b) (F.realFirstCoefficientFastSubmodule w hw U).mkQ =
      (LinearMap.toMatrix (F.firstCoefficientBasis e ω hF w) b
        (F.firstCoefficientFastSubmodule w hw U).mkQ).map (Rat.castHom ℝ) := by
  ext j i
  simp only [Matrix.map_apply, LinearMap.toMatrix_apply]
  exact F.realFastCoefficientBasis_repr_basis w hw U e ω hF b i j

theorem realFastCoefficientBasis_symm
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
    [Fintype κ] [DecidableEq κ]
    (b : Basis κ ℚ (F.FirstCoefficientModule w ⧸ F.firstCoefficientFastSubmodule w hw U))
    (D : Matrix κ (FirstCoefficientIndex w ω) ℚ)
    (S : Matrix (FirstCoefficientIndex w ω) κ ℚ)
    (hD : LinearMap.toMatrix (F.firstCoefficientBasis e ω hF w) b
      (F.firstCoefficientFastSubmodule w hw U).mkQ = D)
    (hDS : D * S = 1) (y : κ → ℝ) :
    (F.realFastCoefficientBasis w hw U b).equivFun.symm y =
      (F.realFirstCoefficientFastSubmodule w hw U).mkQ
        ((F.realFirstCoefficientBasis e ω hF w).equivFun.symm
          (S.map (Rat.castHom ℝ) *ᵥ y)) := by
  apply quotient_basis_representative (F.realFirstCoefficientBasis e ω hF w)
    (F.realFastCoefficientBasis w hw U b) _ (D.map (Rat.castHom ℝ)) _ ?_
    (real_matrix_right_inverse D S hDS) y
  rw [F.realFastCoefficientBasis_matrix, hD]

end Erdos3.NilpotentLieFiltration

end

end OAI
