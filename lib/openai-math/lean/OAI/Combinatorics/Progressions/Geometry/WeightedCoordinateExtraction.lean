import Mathlib.Algebra.Module.Submodule.Map
import OAI.Combinatorics.Progressions.Estimates.ReindexedDerivativePoints
import OAI.Combinatorics.Progressions.Lattices.FirstCoefficientLatticeCoordinates
import OAI.Combinatorics.Progressions.Lattices.UniformDerivativeLatticeExtraction

namespace OAI

section

namespace Erdos3

structure CoordinateDerivativeSystem {σ : Type*} [Fintype σ] [DecidableEq σ] {m a : ℕ}
    (ha : a ≤ m)
    (T : σ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) (scale : Fin m → ℝ) (bound : ℝ) where
  K : Submodule ℝ (Fin a → ℝ)
  k : ℕ
  heightBound : ℕ
  height_le : (heightBound : ℝ) ≤ bound
  basisMatrix : Matrix (Fin a) (Fin k) ℚ
  basis_height : ∀ i j, RationalHeightLE (basisMatrix i j) heightBound
  independent_rat : LinearIndependent ℚ basisMatrix.col
  independent_real : LinearIndependent ℝ (basisMatrix.map (Rat.castHom ℝ)).col
  span_eq : K = Submodule.span ℝ (Set.range (basisMatrix.map (Rat.castHom ℝ)).col)
  rationalLift : K →ₗ[ℝ] (Fin m → ℝ)
  geometricLift : K →ₗ[ℝ] (Fin m → ℝ)
  factorization : geometricLift = A.toLinearMap.comp rationalLift
  rational_horizontal : ∀ x i, rationalLift x (Fin.castLE ha i) = x.val i
  geometric_horizontal : ∀ x i, geometricLift x (Fin.castLE ha i) = x.val i
  norm_scaled : ∀ x,
    ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * geometricLift x j)‖ ≤ bound * ‖x‖
  liftDenominator : ℕ
  liftDenominator_pos : 0 < liftDenominator
  liftDenominator_le : (liftDenominator : ℝ) ≤ bound
  rational_on_basis : ∀ j, ∃ x : K,
    x.val = (basisMatrix.map (Rat.castHom ℝ)).col j ∧ rationalLift x ∈ realDenominatorGrid liftDenominator
  derivativeDenominator : ℕ
  derivativeDenominator_pos : 0 < derivativeDenominator
  derivativeDenominator_le : (derivativeDenominator : ℝ) ≤ bound
  slow : σ → Fin m → ℝ
  rational : σ → Fin m → ℝ
  horizontal : σ → K
  derivative_eq : ∀ i, Y (Pi.basisFun ℝ σ i) = slow i + A (rational i) + geometricLift (horizontal i)
  derivative_grid : ∀ i, rational i ∈ realDenominatorGrid derivativeDenominator
  slow_bound : ∀ i,
    ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * slow i j)‖ ≤ bound / T i

theorem coordinateDerivativeSystem_of_lifts
    {σ E : Type*} [Fintype σ] [DecidableEq σ] [AddCommGroup E] [Module ℝ E]
    {m a k H : ℕ} (T : σ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) (scale : Fin m → ℝ)
    (P : E →ₗ[ℝ] (Fin a → ℝ)) (ha : a ≤ m) (N bound : ℝ)
    (lifts : RationalHorizontalLift k P ha A scale N H)
    (hN : N ≤ bound) (hH : (H : ℝ) ≤ bound)
    (D : ℕ) (hD : 0 < D) (hDb : (D : ℝ) ≤ bound)
    (hderiv : ∀ i, ∃ (s r : Fin m → ℝ) (q : LinearMap.range P),
      Y (Pi.basisFun ℝ σ i) = s + A r + lifts.geometricLift q ∧
      r ∈ realDenominatorGrid D ∧
      ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * s j)‖ ≤ bound / T i) :
    Nonempty (CoordinateDerivativeSystem ha T Y A scale bound) := by
  choose s r q heq hgrid hsmall using hderiv
  exact ⟨{
    K := LinearMap.range P
    k := k
    heightBound := H
    height_le := hH
    basisMatrix := lifts.basisMatrix
    basis_height := lifts.basis_height
    independent_rat := lifts.independent_rat
    independent_real := lifts.independent_real
    span_eq := lifts.span_eq
    rationalLift := lifts.rationalLift
    geometricLift := lifts.geometricLift
    factorization := lifts.factorization
    rational_horizontal := lifts.rational_horizontal
    geometric_horizontal := lifts.geometric_horizontal
    norm_scaled := fun x => (lifts.norm_scaled x).trans (mul_le_mul_of_nonneg_right hN (norm_nonneg x))
    liftDenominator := lifts.denominator
    liftDenominator_pos := lifts.denominator_pos
    liftDenominator_le := (Nat.cast_le.mpr lifts.denominator_le).trans hH
    rational_on_basis := lifts.rational_on_basis
    derivativeDenominator := D
    derivativeDenominator_pos := hD
    derivativeDenominator_le := hDb
    slow := s
    rational := r
    horizontal := q
    derivative_eq := heq
    derivative_grid := hgrid
    slow_bound := hsmall
  }⟩

end Erdos3

end

section

namespace Erdos3

open Module

theorem transport_coordinate_derivative_system
    {σ E H : Type*} [Fintype σ] [DecidableEq σ]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup H] [Module ℝ H]
    {a d : ℕ} (ha : a ≤ d) (b : Basis (Fin d) ℝ E)
    (η : (Fin a → ℝ) ≃ₗ[ℝ] H) (P : E →ₗ[ℝ] H)
    (hP : ∀ x, η (fun i => b.equivFun x (Fin.castLE ha i)) = P x)
    (T : σ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] E) (f : E ≃ₗ[ℝ] E)
    (scale : Fin d → ℝ) (bound : ℝ)
    (D : CoordinateDerivativeSystem ha T (b.equivFun.toLinearMap.comp Y)
      (b.equivFun.symm.trans (f.trans b.equivFun)) scale bound) :
    let K := D.K.map η.toLinearMap
    K = Submodule.span ℝ (Set.range (fun j => η ((D.basisMatrix.map (Rat.castHom ℝ)).col j))) ∧
    ∃ R S : K →ₗ[ℝ] E,
      S = f.toLinearMap.comp R ∧
      (∀ x, P (R x) = x.val) ∧ (∀ x, P (S x) = x.val) ∧
      (∀ x, ‖(EuclideanSpace.equiv (Fin d) ℝ).symm
        (fun j => scale j * b.equivFun (S x) j)‖ ≤ bound * ‖η.symm x.val‖) ∧
      (∀ j, ∃ x : K, x.val = η ((D.basisMatrix.map (Rat.castHom ℝ)).col j) ∧
        b.equivFun (R x) ∈ realDenominatorGrid D.liftDenominator) ∧
      ∀ i, ∃ (s r : E) (k : K),
        Y (Pi.basisFun ℝ σ i) = s + f r + S k ∧
        b.equivFun r ∈ realDenominatorGrid D.derivativeDenominator ∧
        ‖(EuclideanSpace.equiv (Fin d) ℝ).symm
          (fun j => scale j * b.equivFun s j)‖ ≤ bound / T i := by
  let K := D.K.map η.toLinearMap
  let eK : D.K ≃ₗ[ℝ] K := η.submoduleMap D.K
  let R : K →ₗ[ℝ] E := b.equivFun.symm.toLinearMap.comp
    (D.rationalLift.comp eK.symm.toLinearMap)
  let S : K →ₗ[ℝ] E := b.equivFun.symm.toLinearMap.comp
    (D.geometricLift.comp eK.symm.toLinearMap)
  have hR (x : K) : b.equivFun (R x) = D.rationalLift (eK.symm x) :=
    b.equivFun.apply_symm_apply _
  have hS (x : K) : b.equivFun (S x) = D.geometricLift (eK.symm x) :=
    b.equivFun.apply_symm_apply _
  have heK (x : K) : (eK.symm x).val = η.symm x.val := rfl
  constructor
  · rw [D.span_eq, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨_, ⟨j, rfl⟩, rfl⟩
  refine ⟨R, S, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    apply b.equivFun.injective
    rw [hS, D.factorization]
    change b.equivFun (f (b.equivFun.symm (D.rationalLift (eK.symm x)))) =
      b.equivFun (f (R x))
    rfl
  · intro x
    rw [← hP, hR]
    have h : (fun i => D.rationalLift (eK.symm x) (Fin.castLE ha i)) =
        (eK.symm x).val := funext (D.rational_horizontal (eK.symm x))
    rw [h, heK, LinearEquiv.apply_symm_apply]
  · intro x
    rw [← hP, hS]
    have h : (fun i => D.geometricLift (eK.symm x) (Fin.castLE ha i)) =
        (eK.symm x).val := funext (D.geometric_horizontal (eK.symm x))
    rw [h, heK, LinearEquiv.apply_symm_apply]
  · intro x
    simp only [hS]
    exact D.norm_scaled (eK.symm x)
  · intro j
    obtain ⟨x, hx, hgrid⟩ := D.rational_on_basis j
    refine ⟨eK x, ?_, ?_⟩
    · change η x.val = _
      rw [hx]
    · rw [hR, LinearEquiv.symm_apply_apply]
      exact hgrid
  · intro i
    refine ⟨b.equivFun.symm (D.slow i), b.equivFun.symm (D.rational i),
      eK (D.horizontal i), ?_, ?_, ?_⟩
    · apply b.equivFun.injective
      simp only [map_add, LinearEquiv.apply_symm_apply, hS, LinearEquiv.symm_apply_apply]
      exact D.derivative_eq i
    · simpa only [LinearEquiv.apply_symm_apply] using D.derivative_grid i
    · simpa only [LinearEquiv.apply_symm_apply] using D.slow_bound i

end Erdos3

end

section

namespace Erdos3

theorem exists_uniform_coordinate_derivative_system
    {σ : Type*} [Fintype σ] [DecidableEq σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 1 ≤ R) (hδ : 0 < δ)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → Fin m → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (a : ℕ) (ha : a ≤ m) (Tmin : ℝ)
    (hscalehor : ∀ j, j.val < a → scale j = 1)
    (hblock : ∀ i j, i.val < a → j.val < a →
      (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (hfar : ∀ i, a ≤ i.val → Tmin ≤ scale i)
    (p : ℝ) (hp : 0 ≤ p)
    (hdim : ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) ≤ p)
    (hlcap : (l : ℝ) ≤ Real.exp p) (hRcap : R ≤ Real.exp p)
    (hδcap : δ⁻¹ ≤ Real.exp p)
    (hmin : Real.exp ((p + 2) ^ 3) < Tmin) (hside : ∀ i, Tmin ≤ T i) :
    Nonempty (CoordinateDerivativeSystem ha T Y A scale (Real.exp ((p + 2) ^ 3))) := by
  obtain ⟨lifts, hN, hheight, I, hI, hIcap, hdecomp⟩ :=
    euclideanDerivative_uniform_lattice_extraction T hT scale hscale Y A hA hdiag
      l hl R δ hR hδ H r hr hnorm hdense a ha Tmin hscalehor hblock hfar
      p hp hdim hlcap hRcap hδcap hmin hside
  exact coordinateDerivativeSystem_of_lifts T Y A scale _ ha _ _ lifts hN hheight
    (l * I) (Nat.mul_pos hl hI) hIcap hdecomp

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem firstCoefficient_coordinate_system
    {σ ι E : Type*} [Fintype σ] [DecidableEq σ] [AddCommGroup E] [Module ℝ E] {d : ℕ}
    (ω : ι → ℕ) (rows : Fin d → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (b : Basis (Fin d) ℝ E) (Y : (σ → ℝ) →ₗ[ℝ] E) (f : E ≃ₗ[ℝ] E)
    (hf : ∀ i j, ω (rows i).val.2 ≤ ω (rows j).val.2 →
      LinearMap.toMatrix b b f.toLinearMap i j = (1 : Matrix (Fin d) (Fin d) ℝ) i j)
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i) (l : ℕ) (hl : 0 < l)
    (R δ : ℝ) (hR : 1 ≤ R) (hδ : 0 < δ) (H : Finset (σ → ℤ))
    (r : (σ → ℤ) → Fin d → ℝ) (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T (fun i => monomialScale T (rows i).val.1)
        (b.equivFun.toLinearMap.comp Y) (LinearMap.toMatrix b b f.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (p : ℝ) (hp : 0 ≤ p)
    (hdim : ((Fintype.card σ + Fintype.card (Fin d) : ℕ) : ℝ) ≤ p)
    (hlcap : (l : ℝ) ≤ Real.exp p) (hRcap : R ≤ Real.exp p) (hδcap : δ⁻¹ ≤ Real.exp p)
    (Tmin : ℝ) (hmin : Real.exp ((p + 2) ^ 3) < Tmin) (hside : ∀ i, Tmin ≤ T i) :
    ∃ (e : Equiv.Perm (Fin d)) (a : ℕ) (ha : a ≤ d),
      (∀ i, i.val < a ↔ (rows (e i)).val.1 = 0) ∧
      let b' := b.reindex e.symm
      let Y' := b'.equivFun.toLinearMap.comp Y
      let A' := b'.equivFun.symm.trans (f.trans b'.equivFun)
      Nonempty (CoordinateDerivativeSystem ha T Y' A'
        (fun i => monomialScale T (rows (e i)).val.1) (Real.exp ((p + 2) ^ 3))) := by
  obtain ⟨e, a, ha, hzero, haction⟩ := exists_lattice_ready_firstCoefficient_basis ω rows b
  obtain ⟨htri, hdiag, hblock⟩ := haction f hf
  let b' := b.reindex e.symm
  let Y' := b'.equivFun.toLinearMap.comp Y
  let A' := b'.equivFun.symm.trans (f.trans b'.equivFun)
  let scale := fun i => monomialScale T (rows (e i)).val.1
  let r' := fun h => r h ∘ e
  have hY : Y' = (LinearMap.funLeft ℝ ℝ e).comp (b.equivFun.toLinearMap.comp Y) := by
    apply LinearMap.ext
    intro x
    funext i
    exact congrFun (basis_reindex_equivFun b e (Y x)) i
  have hA : LinearMap.toMatrix' A'.toLinearMap =
      (LinearMap.toMatrix b b f.toLinearMap).submatrix e e := by
    rw [basis_coordinate_linearEquiv_matrix]
    ext i j
    exact basis_reindex_toMatrix b e f.toLinearMap i j
  have hscale : ∀ i, 1 ≤ scale i := fun i => one_le_monomialScale T hT _
  have hTmin : 1 ≤ Tmin := (Real.one_le_exp (by positivity)).trans hmin.le
  obtain ⟨hhor, hfar⟩ := sorted_firstCoefficient_scale_bounds ω (rows ∘ e) hzero T Tmin hTmin hside
  have hr' : ∀ h ∈ H, r' h ∈ realDenominatorGrid l :=
    fun h hh => realDenominatorGrid_comp l (r h) (hr h hh) e
  have hnorm' : ∀ h ∈ H, ‖derivativeGridPoint T scale Y' (LinearMap.toMatrix' A'.toLinearMap)
      h (r' h)‖ ≤ R := by
    intro h hh
    rw [hY, hA]
    exact (derivativeGridPoint_reindex_norm T (fun i => monomialScale T (rows i).val.1)
      (b.equivFun.toLinearMap.comp Y) (LinearMap.toMatrix b b f.toLinearMap) e h (r h)).le.trans
        (hnorm h hh)
  refine ⟨e, a, ha, hzero, ?_⟩
  exact exists_uniform_coordinate_derivative_system T hT scale hscale Y' A' htri hdiag
    l hl R δ hR hδ H r' hr' hnorm' hdense a ha Tmin hhor hblock hfar
    p hp hdim hlcap hRcap hδcap hmin hside

end Erdos3.NilpotentLieFiltration

end

end OAI
