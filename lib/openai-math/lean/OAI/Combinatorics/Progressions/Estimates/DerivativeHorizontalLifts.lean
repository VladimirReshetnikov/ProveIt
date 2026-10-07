import Mathlib.Analysis.InnerProductSpace.PiL2
import OAI.Combinatorics.Progressions.Lattices.DerivativeLatticeDivision
import OAI.Combinatorics.Progressions.Linear.EuclideanVerticalProjection
import OAI.Combinatorics.Progressions.Linear.RationalTagConstraintChartBasis
import OAI.Combinatorics.Progressions.Linear.ScaledBasisNorm

namespace OAI

section

namespace Erdos3

structure RationalHorizontalLift {E : Type*} [AddCommGroup E] [Module ℝ E]
    {m a : ℕ} (k : ℕ) (P : E →ₗ[ℝ] (Fin a → ℝ)) (ha : a ≤ m)
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) (scale : Fin m → ℝ)
    (normBound : ℝ) (heightBound : ℕ) where
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_le : denominator ≤ heightBound
  basisMatrix : Matrix (Fin a) (Fin k) ℚ
  basis_height : ∀ i j, RationalHeightLE (basisMatrix i j) heightBound
  independent_rat : LinearIndependent ℚ basisMatrix.col
  independent_real : LinearIndependent ℝ (basisMatrix.map (Rat.castHom ℝ)).col
  span_eq : LinearMap.range P =
    Submodule.span ℝ (Set.range (basisMatrix.map (Rat.castHom ℝ)).col)
  rationalLift : LinearMap.range P →ₗ[ℝ] (Fin m → ℝ)
  geometricLift : LinearMap.range P →ₗ[ℝ] (Fin m → ℝ)
  factorization : geometricLift = A.toLinearMap.comp rationalLift
  rational_horizontal : ∀ x i, rationalLift x (Fin.castLE ha i) = x.val i
  geometric_horizontal : ∀ x i, geometricLift x (Fin.castLE ha i) = x.val i
  norm_scaled : ∀ x,
    ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * geometricLift x j)‖ ≤
      normBound * ‖x‖
  rational_on_basis : ∀ j, ∃ x : LinearMap.range P,
    x.val = (basisMatrix.map (Rat.castHom ℝ)).col j ∧
    rationalLift x ∈ realDenominatorGrid denominator

end Erdos3

end

section

namespace Erdos3

theorem exists_basis_linear_lift {K E F G ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
    [AddCommGroup G] [Module K G]
    (b : Module.Basis ι K E) (f : E →ₗ[K] F) (W : G →ₗ[K] F)
    (v : ι → G) (hrep : ∀ j, f (b j) = W (v j)) :
    ∃ g : E →ₗ[K] G, (∀ j, g (b j) = v j) ∧ W.comp g = f := by
  refine ⟨b.constr K v, fun j => b.constr_basis K v j, ?_⟩
  apply b.ext
  intro j
  change W ((b.constr K v) (b j)) = f (b j)
  rw [Module.Basis.constr_basis]
  exact (hrep j).symm

theorem euclideanVerticalMap_norm_eq {σ κ : Type*} [Fintype σ] [Fintype κ]
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (x : κ → ℝ) :
    ‖euclideanVerticalMap (σ := σ) scale hscale A x‖ =
      ‖(EuclideanSpace.equiv κ ℝ).symm (fun j => scale j * A x j)‖ := by
  have hs : ‖euclideanVerticalMap (σ := σ) scale hscale A x‖ ^ 2 =
      ‖(EuclideanSpace.equiv κ ℝ).symm (fun j => scale j * A x j)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [Fintype.sum_sum_type, euclideanVerticalMap_apply_inl,
      euclideanVerticalMap_apply_inr, norm_zero, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero, zero_add]
    rfl
  nlinarith [norm_nonneg (euclideanVerticalMap (σ := σ) scale hscale A x),
    norm_nonneg ((EuclideanSpace.equiv κ ℝ).symm (fun j => scale j * A x j))]

end Erdos3

end

section

namespace Erdos3

theorem graph_derivative_decomposition
    {σ : Type*} [Fintype σ] {m a k : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : Fin m → ℝ) (hs : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ Fin m)))
    (ha : a ≤ m) (N : ℝ) (H : ℕ) :
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
    ∀ (lifts : RationalHorizontalLift k P ha A scale N H),
      (∀ v : V, euclideanVerticalMap scale hs A (lifts.rationalLift ⟨P v, v, rfl⟩) = v.val.val) →
      ∀ (G : (σ → ℝ) →ₗ[ℝ] Z), (∀ y i, (G y).val (Sum.inl i) = y i) →
      ∀ (x : Z) (y : σ → ℝ) (r : Fin m → ℝ),
        (∀ j, x.val (Sum.inr j) = scale j * (Y y j - A r j)) →
        ∃ (s : Fin m → ℝ) (q : LinearMap.range P),
          Y y = s + A r + lifts.geometricLift q ∧
          ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * s j)‖ ≤
            ‖G (fun i => x.val (Sum.inl i))‖ := by
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
  dsimp only
  intro lifts hrecovers G hG x y r hx
  let w := G (fun i => x.val (Sum.inl i))
  let v : V := ⟨x - w, euclidean_graph_residual_mem_kernel T hT Z G hG x⟩
  let q : LinearMap.range P := ⟨P v, v, rfl⟩
  let s : Fin m → ℝ := fun j => w.val (Sum.inr j) / scale j
  have hscale (j) : scale j * s j = w.val (Sum.inr j) := mul_div_cancel₀ _ (hs j)
  have hS (j) : scale j * lifts.geometricLift q j =
      x.val (Sum.inr j) - w.val (Sum.inr j) := by
    calc
      _ = euclideanVerticalMap scale hs A (lifts.rationalLift q) (Sum.inr j) := by
        rw [lifts.factorization]
        rfl
      _ = v.val.val (Sum.inr j) := congrArg (fun z => z (Sum.inr j)) (hrecovers v)
      _ = _ := rfl
  refine ⟨s, q, ?_, ?_⟩
  · funext j
    change Y y j = s j + A r j + lifts.geometricLift q j
    apply mul_left_cancel₀ (hs j)
    nlinarith [hS j, hscale j, hx j]
  · have he : (fun j => scale j * s j) = fun j => w.val (Sum.inr j) := funext hscale
    rw [he]
    exact euclideanVerticalProjection_norm_le w.val

end Erdos3

end

section

namespace Erdos3

theorem assemble_rational_horizontal_lift
    {E σ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype σ]
    {m a k : ℕ} (b : Module.Basis (Fin k) ℝ E)
    (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ (σ ⊕ Fin m))
    (P : E →ₗ[ℝ] (Fin a → ℝ)) (hPinj : Function.Injective P) (ha : a ≤ m)
    (hP : ∀ v i, P v i = f v (Sum.inr (Fin.castLE ha i)))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hAhor : ∀ x i, A x (Fin.castLE ha i) = x (Fin.castLE ha i))
    (scale : Fin m → ℝ) (hs0 : ∀ j, scale j ≠ 0)
    (hscalehor : ∀ i : Fin a, scale (Fin.castLE ha i) = 1)
    (B : Matrix (Fin m) (Fin k) ℝ)
    (hrep : ∀ j, f (b j) = euclideanVerticalMap scale hs0 A (B.col j))
    (p : Fin k → Fin a) (hp : (B.submatrix (Fin.castLE ha ∘ p) id).det ≠ 0)
    (Q : Matrix (Fin m) (Fin k) ℚ)
    (hQ : Q.map (Rat.castHom ℝ) = B * (B.submatrix (Fin.castLE ha ∘ p) id)⁻¹)
    (hQid : Q.submatrix (Fin.castLE ha ∘ p) id = 1)
    (D H : ℕ) (hD : 0 < D) (hDH : D ≤ H)
    (hgrid : ∀ j, Q.col j ∈ denominatorGrid D)
    (hheight : ∀ i j, RationalHeightLE (Q (Fin.castLE ha i) j) H)
    (N : ℝ) (hnorm : ∀ v, ‖v‖ ≤ N * ‖P v‖) :
    ∃ lifts : RationalHorizontalLift k P ha A scale N H,
      ∀ v, euclideanVerticalMap scale hs0 A (lifts.rationalLift ⟨P v, v, rfl⟩) = f v := by
  let W := euclideanVerticalMap (σ := σ) scale hs0 A
  obtain ⟨g, hgb, hgf⟩ := exists_basis_linear_lift b f.toLinearMap W B.col hrep
  have hW (v) : W (g v) = f v := LinearMap.congr_fun hgf v
  have hhor (v) (i : Fin a) : g v (Fin.castLE ha i) = P v i := by
    calc
      _ = A (g v) (Fin.castLE ha i) := (hAhor (g v) i).symm
      _ = W (g v) (Sum.inr (Fin.castLE ha i)) := by
        change _ = scale (Fin.castLE ha i) * A (g v) (Fin.castLE ha i)
        rw [hscalehor, one_mul]
      _ = f v (Sum.inr (Fin.castLE ha i)) := congrArg (fun z => z (Sum.inr (Fin.castLE ha i))) (hW v)
      _ = P v i := (hP v i).symm
  have hbound (v) : ‖W (g v)‖ ≤ N * ‖P v‖ := by
    rw [hW, f.norm_map]
    exact hnorm v
  have hB (i j) : B i j = g (b j) i := (congrFun (hgb j) i).symm
  obtain ⟨R, hRhor, hRbound, hRsection, hspan, hLIreal, hLIrat, hRbasis⟩ :=
    exists_bounded_rational_projection_lift b P hPinj g (Fin.castLE ha) hhor W N hbound
      B hB p hp Q hQ hQid
  refine ⟨{
    denominator := D
    denominator_pos := hD
    denominator_le := hDH
    basisMatrix := Q.submatrix (Fin.castLE ha) id
    basis_height := hheight
    independent_rat := hLIrat
    independent_real := hLIreal
    span_eq := hspan
    rationalLift := R
    geometricLift := A.toLinearMap.comp R
    factorization := rfl
    rational_horizontal := hRhor
    geometric_horizontal := ?_
    norm_scaled := ?_
    rational_on_basis := ?_
  }, ?_⟩
  · intro x i
    change A (R x) (Fin.castLE ha i) = x.val i
    rw [hAhor, hRhor]
  · intro x
    have h := hRbound x
    change ‖euclideanVerticalMap (σ := σ) scale hs0 A (R x)‖ ≤ N * ‖x‖ at h
    rw [euclideanVerticalMap_norm_eq] at h
    exact h
  · intro j
    obtain ⟨x, hx, hrx⟩ := hRbasis j
    refine ⟨x, hx, ?_⟩
    rw [hrx]
    exact (real_cast_mem_denominatorGrid_iff D (Q.col j)).mpr (hgrid j)
  · intro v
    change W (R ⟨P v, v, rfl⟩) = f v
    rw [hRsection]
    exact hW v

end Erdos3

end

section

namespace Erdos3

theorem indexed_derivative_decomposition
    {σ : Type*} [Fintype σ] [DecidableEq σ] {m a k : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (hTpos : ∀ i, 0 < T i)
    (scale : Fin m → ℝ) (hs : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) (l : ℕ) (hl : 0 < l)
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ Fin m)))
    (ha : a ≤ m) (N B : ℝ) (H : ℕ) :
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
    ∀ (lifts : RationalHorizontalLift k P ha A scale N H),
      (∀ v : V, euclideanVerticalMap scale hs A (lifts.rationalLift ⟨P v, v, rfl⟩) = v.val.val) →
      ∀ (G : (σ → ℝ) →ₗ[ℝ] Z), (∀ y i, (G y).val (Sum.inl i) = y i) →
      (∀ i, ‖G (Pi.basisFun ℝ σ i)‖ ≤ B) →
      ∀ (I : ℕ), 0 < I →
      (∀ i, ∃ v : Z, v.val ∈ euclideanDerivativeLattice T hT scale hs Y A l hl ∧
        euclideanDerivativeShiftMap T hT v.val = (I : ℝ) • Pi.basisFun ℝ σ i) →
      ∀ i, ∃ (s r : Fin m → ℝ) (q : LinearMap.range P),
        Y (Pi.basisFun ℝ σ i) = s + A r + lifts.geometricLift q ∧
        r ∈ realDenominatorGrid (l * I) ∧
        ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * s j)‖ ≤ B / T i := by
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
  dsimp only
  intro lifts hrecovers G hG hGB I hI hI_lifts i
  obtain ⟨v, hv, hshift⟩ := hI_lifts i
  let x : Z := (I : ℝ)⁻¹ • v
  obtain ⟨r, hr, hright⟩ := divided_derivative_lattice_coordinates T hT scale hs Y A l hl
    I hI (Pi.basisFun ℝ σ i) v.val hv hshift
  obtain ⟨s, q, heq, hsmall⟩ := graph_derivative_decomposition T hT scale hs Y A Z ha N H
    lifts hrecovers G hG x (Pi.basisFun ℝ σ i) r hright
  refine ⟨s, r, q, heq, hr, ?_⟩
  have hleft : (fun j => x.val (Sum.inl j)) =
      fun j => (Pi.basisFun ℝ σ i) j / T j :=
    funext (divided_derivative_horizontal_coordinates T hT I hI (Pi.basisFun ℝ σ i) v.val hshift)
  rw [hleft] at hsmall
  exact hsmall.trans (linearMap_divided_basis_norm_le G T i (hTpos i) B (hGB i))

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_horizontal_norm_bound
    {σ : Type*} [Fintype σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R : ℝ) (a : ℕ) (ha : a ≤ m) (Tmin C : ℝ)
    (hscalehor : ∀ j, j.val < a → scale j = 1)
    (hblock : ∀ i j, i.val < a → j.val < a →
      (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (hfar : ∀ i, a ≤ i.val → Tmin ≤ scale i) (hlarge : C * (l : ℝ) ^ m < Tmin) :
    let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
    let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
    let Z := shortVectorSpan Λ R
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let L := latticeKernel (shortVectorLattice Λ R) π
    let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
    let k := Module.finrank ℝ V
    ZLattice.covolume L (MeasureTheory.volume (α := V)) ≤ C →
      ∀ v : V, ‖v‖ ≤ (Fintype.card (σ ⊕ Fin m) : ℝ) * k *
        (C * (l : ℝ) ^ k) * ‖P v‖ := by
  let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
  let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let L := latticeKernel (shortVectorLattice Λ R) π
  let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
  let k := Module.finrank ℝ V
  change ZLattice.covolume L (MeasureTheory.volume (α := V)) ≤ C →
    ∀ v : V, ‖v‖ ≤ (Fintype.card (σ ⊕ Fin m) : ℝ) * k *
      (C * (l : ℝ) ^ k) * ‖P v‖
  intro hupper v
  let : IsZLattice ℝ L := euclideanDerivative_vertical_lattice_full T hT scale hs0 Y A l hl R
  obtain ⟨b, B, _, hgrid, hrep, p, _, hdet⟩ := euclideanDerivative_horizontal_basis_data
    T hT scale hscale Y A hA hdiag l hl R a ha Tmin C hfar hlarge hupper
  let f : V →ₗᵢ[ℝ] EuclideanSpace ℝ (σ ⊕ Fin m) := Z.subtypeₗᵢ.comp V.subtypeₗᵢ
  let e : Fin a → σ ⊕ Fin m := fun i => Sum.inr (Fin.castLE ha i)
  let H := B.submatrix (Fin.castLE ha) id
  have hH (i j) : H i j = f (b j).val (e i) := by
    change B (Fin.castLE ha i) j = (b j).val.val.val (Sum.inr (Fin.castLE ha i))
    rw [hrep]
    exact (euclideanVerticalMap_horizontal scale hs0 hscalehor A hA hblock (B.col j)
      (Fin.castLE ha i) i.isLt).symm
  have hHgrid (j) : H.col j ∈ realDenominatorGrid l := by
    obtain ⟨z, hz⟩ := hgrid j
    refine ⟨fun i => z (Fin.castLE ha i), ?_⟩
    funext i
    exact congrFun hz (Fin.castLE ha i)
  have hdetH : (H.submatrix p id).det ≠ 0 := hdet
  have hn := lattice_norm_le_projection_of_grid_minor
    (ι := σ ⊕ Fin m) (κ := Fin a) (E := V) (k := k)
    L b f e l hl H hH hHgrid p hdetH C hupper v
  have heP : (fun i => f v (e i)) = P v := rfl
  rw [heP] at hn
  exact hn

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_horizontal_lifts
    {σ : Type*} [Fintype σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R : ℝ) (a : ℕ) (ha : a ≤ m) (Tmin C : ℝ)
    (hscalehor : ∀ j, j.val < a → scale j = 1)
    (hblock : ∀ i j, i.val < a → j.val < a →
      (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (hfar : ∀ i, a ≤ i.val → Tmin ≤ scale i) (hlarge : C * (l : ℝ) ^ m < Tmin) :
    let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
    let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
    let Z := shortVectorSpan Λ R
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let L := latticeKernel (shortVectorLattice Λ R) π
    let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
    let k := Module.finrank ℝ V
    let N := (Fintype.card (σ ⊕ Fin m) : ℝ) * k * (C * (l : ℝ) ^ k)
    let H := Nat.ceil (C * (l : ℝ) ^ k)
    ZLattice.covolume L (MeasureTheory.volume (α := V)) ≤ C →
      ∃ lifts : RationalHorizontalLift k P ha A scale N H,
        ∀ v : V, euclideanVerticalMap scale hs0 A (lifts.rationalLift ⟨P v, v, rfl⟩) = v.val.val := by
  let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
  let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let L := latticeKernel (shortVectorLattice Λ R) π
  let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
  let k := Module.finrank ℝ V
  let N := (Fintype.card (σ ⊕ Fin m) : ℝ) * k * (C * (l : ℝ) ^ k)
  let H := Nat.ceil (C * (l : ℝ) ^ k)
  change ZLattice.covolume L (MeasureTheory.volume (α := V)) ≤ C →
    ∃ lifts : RationalHorizontalLift k P ha A scale N H,
      ∀ v : V, euclideanVerticalMap scale hs0 A (lifts.rationalLift ⟨P v, v, rfl⟩) = v.val.val
  intro hupper
  let : IsZLattice ℝ L := euclideanDerivative_vertical_lattice_full T hT scale hs0 Y A l hl R
  obtain ⟨b, B, p, _, hrep, hp, D, hD, hDH, Q, hgrid, hQ, hQid, hheight⟩ :=
    euclideanDerivative_rational_lift_matrix_data T hT scale hscale Y A hA hdiag
      l hl R a ha Tmin C hscalehor hblock hfar hlarge hupper
  let bR := b.ofZLatticeBasis ℝ L
  let f : V →ₗᵢ[ℝ] EuclideanSpace ℝ (σ ⊕ Fin m) := Z.subtypeₗᵢ.comp V.subtypeₗᵢ
  have hbrep (j) : f (bR j) = euclideanVerticalMap scale hs0 A (B.col j) := by
    simp only [bR, Module.Basis.ofZLatticeBasis_apply]
    exact hrep j
  have hP : ∀ v i, P v i = f v (Sum.inr (Fin.castLE ha i)) := fun _ _ => rfl
  have hPinj : Function.Injective P := euclideanDerivative_horizontal_injective
    T hT scale hscale Y A hA hdiag l hl R a ha Tmin C hscalehor hblock hfar hlarge hupper
  have hAhor (x) (i : Fin a) : A x (Fin.castLE ha i) = x (Fin.castLE ha i) := by
    have h := euclideanVerticalMap_horizontal (σ := σ) scale hs0 hscalehor A hA hblock
      x (Fin.castLE ha i) i.isLt
    rw [euclideanVerticalMap_apply_inr, hscalehor (Fin.castLE ha i) i.isLt, one_mul] at h
    exact h
  have hn : ∀ v : V, ‖v‖ ≤ N * ‖P v‖ := euclideanDerivative_horizontal_norm_bound
    T hT scale hscale Y A hA hdiag l hl R a ha Tmin C hscalehor hblock hfar hlarge hupper
  exact assemble_rational_horizontal_lift (E := V) (σ := σ) (m := m) (a := a) (k := k)
    bR f P hPinj ha hP A hAhor scale hs0 (fun i => hscalehor _ i.isLt)
    B hbrep p hp Q hQ hQid D H hD hDH hgrid hheight N hn

end Erdos3

end

end OAI
