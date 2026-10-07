/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.ControlledLinearSubspaceLift
import OAI.Combinatorics.Progressions.Linear.ReducedSquareFastKernel
import OAI.Combinatorics.Progressions.Linear.SynchronizeSplittingProjection
import OAI.Combinatorics.Progressions.Sampling.RealAdaptedCoefficientGrid

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem normalizedRelativeSubmodule_lie_mem (a p : F.adaptedLieSubalgebra w)
    (hp : p ∈ F.normalizedRelativeSubmodule w) :
    ⁅a, p⁆ ∈ F.normalizedRelativeSubmodule w := by
  refine ⟨(F.shiftedAdaptedIdeal w).lie_mem hp.1, ?_⟩
  change coefficients ⁅a.val, p.val⁆ 0 ∈ F.layer 2
  rw [← eval_zero_eq_coefficient]
  change evalLie (0 : σ → ℚ) ⁅a.val, p.val⁆ ∈ F.layer 2
  rw [LieHom.map_lie]
  apply (F.layerIdeal 2).lie_mem
  change eval (fun _ : σ => 0) p.val ∈ F.layer 2
  rw [eval_zero_eq_coefficient]
  exact hp.2

noncomputable def normalizedRelativeIdeal : LieIdeal ℚ (F.adaptedLieSubalgebra w) :=
  { F.normalizedRelativeSubmodule w with
    lie_mem := fun {a p} hp => F.normalizedRelativeSubmodule_lie_mem w a p hp }

theorem normalizedRelativeSubmodule_adjoint_mem (g : (F.adaptedPolynomialFiltration w).Group)
    (p : F.normalizedRelativeSubmodule w) :
    dualAdjoint g p.val ∈ F.normalizedRelativeSubmodule w :=
  dualAdjoint_mem_ideal (F.normalizedRelativeIdeal w) g p.val p.property

theorem relativeSquareLift_lie (hw : ∀ i, 0 < w i)
    (a : F.adaptedLieSubalgebra w) (p : F.normalizedRelativeSubmodule w) :
    F.relativeSquareLift w hw ⟨⁅a, p.val⁆, F.normalizedRelativeSubmodule_lie_mem w a p.val p.property⟩ =
      ⁅F.squareDiagonalPolynomialMap w a, F.relativeSquareLift w hw p⁆ := by
  apply F.square_polynomial_ext w
  · rw [F.squareFstPolynomialMap_relative, LieHom.map_lie,
      F.squareFstPolynomialMap_diagonal, F.squareFstPolynomialMap_relative]
  · rw [F.squareSndPolynomialMap_relative, LieHom.map_lie,
      F.squareSndPolynomialMap_relative, lie_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

noncomputable def realLinearCoordinateLift (σ : M →ₗ[ℚ] L)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) t (realification_lowerCentralSeries_eq_bot hM)) :
    NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL) :=
  ⟨σ.baseChange ℝ g.coord⟩

@[simp] theorem realLinearCoordinateLift_coord (σ : M →ₗ[ℚ] L)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) t (realification_lowerCentralSeries_eq_bot hM)) :
    (realLinearCoordinateLift (hL := hL) (hM := hM) σ g).coord = σ.baseChange ℝ g.coord := rfl

theorem exists_controlled_fast_lift {ι κ μ δ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (hL : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (hM : LieModule.lowerCentralSeries ℚ M M t = ⊥)
    (e : Basis ι ℚ L) (f : Basis μ ℚ M) (c : ι → δ) (r : μ → δ)
    (U : LieSubalgebra ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    (hU : BasisBlockInvariant e c U.toSubmodule)
    (φ : L →ₗ⁅ℚ⁆ M) (hblock : ∀ i j, r i ≠ c j → f.repr (φ (e j)) i = 0)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ j i, RationalHeightLE (e.repr (v j) i) H)
    (hφ : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (ι ⊕ μ) : ℝ) ≤ p)
    (hcols : ((Fintype.card ι * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    let q := (p + 2) ^ 10
    ∃ (σ : M →ₗ[ℚ] L) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((q + 2) ^ 36) ∧ l ∣ m ∧
      (∀ g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) t (realification_lowerCentralSeries_eq_bot hM),
        g ∈ realificationSubgroup (hnil := hM) (U.map φ) →
          realLinearCoordinateLift (hL := hL) (hM := hM) σ g ∈ realificationSubgroup (hnil := hL) U ∧
          realificationMap (hnil := hL) (hM := hM) φ (realLinearCoordinateLift (hL := hL) (hM := hM) σ g) = g) ∧
      (∀ (W : δ → ℝ), (∀ d, 0 < W d) → ∀ (B : ℝ), 0 ≤ B →
        ∀ g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) t (realification_lowerCentralSeries_eq_bot hM),
          (∀ i, |(f.baseChange ℝ).equivFun g.coord i| ≤ B / W (r i)) →
            ∀ i, |(e.baseChange ℝ).equivFun (realLinearCoordinateLift (hL := hL) (hM := hM) σ g).coord i| ≤
              Real.exp ((q + 2) ^ 18) * B / W (c i)) ∧
      (∀ g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) t (realification_lowerCentralSeries_eq_bot hM),
        (f.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid l →
          (e.baseChange ℝ).equivFun (realLinearCoordinateLift (hL := hL) (hM := hM) σ g).coord ∈
            realDenominatorGrid m) := by
  obtain ⟨σ, m, hm, hmp, hlm, _, hsolve, hslow, hgrid⟩ :=
    exists_controlled_linear_subspace_lift e f c r U.toSubmodule v hspan hU φ.toLinearMap hblock
      hH hl hv hφ hp hrows hcols hHp hlp
  refine ⟨σ, m, hm, hmp, hlm, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨hmem, hproj⟩ := hsolve g.coord hg
    exact ⟨hmem, NilpotentLieBCHGroup.ext hproj⟩
  · intro W hW B hB g hg
    exact hslow W hW B hB g.coord hg
  · intro g hg
    exact hgrid g.coord hg

theorem synchronize_with_linear_fast_lift (U : LieSubalgebra ℚ L) (φ : L →ₗ⁅ℚ⁆ M)
    (σ : M →ₗ[ℚ] L)
    (hσ : ∀ g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) t (realification_lowerCentralSeries_eq_bot hM),
      g ∈ realificationSubgroup (hnil := hM) (U.map φ) →
        realLinearCoordinateLift (hL := hL) (hM := hM) σ g ∈ realificationSubgroup (hnil := hL) U ∧
        realificationMap (hnil := hL) (hM := hM) φ (realLinearCoordinateLift (hL := hL) (hM := hM) σ g) = g)
    (E P R : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL))
    (A D : NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) t (realification_lowerCentralSeries_eq_bot hM))
    (hP : P ∈ realificationSubgroup (hnil := hL) U)
    (hleft : A⁻¹ * realificationMap (hnil := hL) (hM := hM) φ E ∈ realificationSubgroup (hnil := hM) (U.map φ))
    (hright : realificationMap (hnil := hL) (hM := hM) φ R * D⁻¹ ∈ realificationSubgroup (hnil := hM) (U.map φ)) :
    let a := realLinearCoordinateLift (hL := hL) (hM := hM) σ (A⁻¹ * realificationMap (hnil := hL) (hM := hM) φ E)
    let d := realLinearCoordinateLift (hL := hL) (hM := hM) σ (realificationMap (hnil := hL) (hM := hM) φ R * D⁻¹)
    (E * a⁻¹) * (a * P * d) * (d⁻¹ * R) = E * P * R ∧
      a * P * d ∈ realificationSubgroup (hnil := hL) U ∧
      realificationMap (hnil := hL) (hM := hM) φ (E * a⁻¹) = A ∧ realificationMap (hnil := hL) (hM := hM) φ (d⁻¹ * R) = D ∧
      realificationMap (hnil := hL) (hM := hM) φ (a * P * d) = A⁻¹ * realificationMap (hnil := hL) (hM := hM) φ (E * P * R) * D⁻¹ := by
  obtain ⟨ha, haq⟩ := hσ _ hleft
  obtain ⟨hd, hdq⟩ := hσ _ hright
  exact synchronize_splitting_projection (realificationMap (hnil := hL) (hM := hM) φ) (realificationSubgroup (hnil := hL) U)
    E P R _ _ A D hP ha hd haq hdq

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def reducedSquareRealSymbolHom :
    F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w →*
      F.quotientTop.RealPolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := F.squareFiltration.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (hM := F.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w) (F.reducedSquareSndSymbolMap w)

noncomputable def reducedSquareRealLinearLift
    (S : F.quotientTop.PolynomialSymbol w →ₗ[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w)
    (g : F.quotientTop.RealPolynomialSymbolGroup w) :
    F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w := ⟨S.baseChange ℝ g.coord⟩

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]

theorem exists_controlled_reduced_fast_lift {κ : Type*} [Fintype κ]
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    (hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun z => z.val.1) U.toSubmodule)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ j i, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hrows : (Fintype.card (ReducedSquareSymbolIndex s w ω ⊕ QuotientTopSymbolIndex s w ω) : ℝ) ≤ p)
    (hcols : ((Fintype.card (ReducedSquareSymbolIndex s w ω) * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    let q := (p + 2) ^ 10
    ∃ (S : F.quotientTop.PolynomialSymbol w →ₗ[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w)
      (m : ℕ), 0 < m ∧ (m : ℝ) ≤ Real.exp ((q + 2) ^ 36) ∧ l ∣ m ∧
      (∀ g : F.quotientTop.RealPolynomialSymbolGroup w,
        g.coord ∈ realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) →
          (F.reducedSquareRealLinearLift w S g).coord ∈ realificationLieSubalgebra U ∧
          F.reducedSquareRealSymbolHom w (F.reducedSquareRealLinearLift w S g) = g) ∧
      (∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ (B : ℝ), 0 ≤ B →
        ∀ g : F.quotientTop.RealPolynomialSymbolGroup w,
          F.quotientTop.SymbolSlowBound (F.quotientTopBasis e ω hF)
            (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T B g →
          F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
            (Real.exp ((q + 2) ^ 18) * B) (F.reducedSquareRealLinearLift w S g)) ∧
      (∀ g : F.quotientTop.RealPolynomialSymbolGroup w,
        F.quotientTop.SymbolRationalGrid (F.quotientTopBasis e ω hF)
          (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w l g →
        F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w m
          (F.reducedSquareRealLinearLift w S g)) := by
  obtain ⟨S, m, hm, hmp, hlm, hsolve, hslow, hgrid⟩ :=
    NilpotentLieBCHGroup.exists_controlled_fast_lift
      (F.squareFiltration.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w)
      (F.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w)
      (F.reducedSquareSymbolBasis e ω hF w) (F.quotientTopSymbolBasis e ω hF w)
      (fun z => z.val.1) (fun z => z.val.1) U v hspan hU (F.reducedSquareSndSymbolMap w)
      (fun i j hij => F.reducedSquareSndSymbolMap_monomial_blocks e ω hF w j i hij)
      hH hl hv (fun i j => (F.reducedSquareSndSymbolMap_basis_height e ω hF w j i).mono hH)
      hp hrows hcols hHp hlp
  refine ⟨S, m, hm, hmp, hlm, ?_, ?_, ?_⟩
  · intro g hg
    exact hsolve g hg
  · intro T hT B hB g hg
    exact hslow (monomialScale T) (monomialScale_pos T hT) B hB g hg
  · intro g hg
    exact hgrid g hg

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem reducedSquareRealSymbolKernel_eq :
    (F.reducedSquareSndSymbolMap w).ker.toSubmodule.baseChange ℝ =
      LinearMap.ker ((F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ) :=
  realification_ker (F.reducedSquareSndSymbolMap w).toLinearMap

theorem reducedSquareRealSymbolKernel_lie_eq_zero (hw : ∀ i, 0 < w i)
    {x y : ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w}
    (hx : (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ x = 0)
    (hy : (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ y = 0) :
    ⁅x, y⁆ = 0 := by
  have hx' : x ∈ (F.reducedSquareSndSymbolMap w).ker.toSubmodule.baseChange ℝ := by
    rw [F.reducedSquareRealSymbolKernel_eq]
    exact hx
  have hy' : y ∈ (F.reducedSquareSndSymbolMap w).ker.toSubmodule.baseChange ℝ := by
    rw [F.reducedSquareRealSymbolKernel_eq]
    exact hy
  have hh := lie_mem_real_baseChange (F.reducedSquareSndSymbolMap w).ker.toSubmodule
    (F.reducedSquareSndSymbolMap w).ker.toSubmodule ⊥
    (fun a ha b hb => (Submodule.mem_bot ℚ).mpr
      (F.reducedSquareSndSymbolKernel_lie_eq_zero w hw ha hb)) hx' hy'
  simpa only [Submodule.baseChange_bot, Submodule.mem_bot] using hh

theorem reducedSquareRealSymbolKernel_bch (hw : ∀ i, 0 < w i)
    {x y : ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w}
    (hx : (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ x = 0)
    (hy : (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ y = 0) :
    lieBCH s x y = x + y :=
  lieBCH_eq_add_of_lie_eq_zero
    (realification_lowerCentralSeries_eq_bot
      (F.squareFiltration.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w))
    (F.reducedSquareRealSymbolKernel_lie_eq_zero w hw hx hy)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def reducedSquareRealDiagonalHom :
    F.quotientTop.RealPolynomialSymbolGroup w →*
      F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w :=
  realificationMap
    (hnil := F.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (hM := F.squareFiltration.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (F.reducedSquareDiagonalSymbolMap w)

@[simp] theorem reducedSquareRealSymbolHom_diagonal (g : F.quotientTop.RealPolynomialSymbolGroup w) :
    F.reducedSquareRealSymbolHom w (F.reducedSquareRealDiagonalHom w g) = g := by
  have h : (F.reducedSquareSndSymbolMap w).toLinearMap.comp
      (F.reducedSquareDiagonalSymbolMap w).toLinearMap = LinearMap.id := by
    ext x
    exact F.reducedSquareSndSymbolMap_diagonal w x
  have hr := congrArg (fun f : F.quotientTop.PolynomialSymbol w →ₗ[ℚ]
    F.quotientTop.PolynomialSymbol w => f.baseChange ℝ) h
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at hr
  apply NilpotentLieBCHGroup.ext
  exact DFunLike.congr_fun hr g.coord

noncomputable def reducedSquareRealRelativePart
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w :=
  splitRelativePart (F.reducedSquareRealSymbolHom w) (F.reducedSquareRealDiagonalHom w) g

@[simp] theorem reducedSquareRealRelativePart_projection
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    F.reducedSquareRealSymbolHom w (F.reducedSquareRealRelativePart w g) = 1 :=
  splitRelativePart_projection _ _ (F.reducedSquareRealSymbolHom_diagonal w) g

theorem reducedSquareRealRelativePart_coord_kernel
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ
      (F.reducedSquareRealRelativePart w g).coord = 0 :=
  congrArg NilpotentLieBCHGroup.coord (F.reducedSquareRealRelativePart_projection w g)

theorem reducedSquareRealRelativePart_factorization
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    F.reducedSquareRealRelativePart w g *
      F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w g) = g :=
  splitRelativePart_factorization _ _ g

theorem reducedSquareRealRelativePart_mul
    (g h : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    F.reducedSquareRealRelativePart w (g * h) = F.reducedSquareRealRelativePart w g *
      (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w g) *
        F.reducedSquareRealRelativePart w h *
        (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w g))⁻¹) :=
  splitRelativePart_mul _ _ g h

theorem reducedSquareRealRelativePart_mul_coord (hw : ∀ i, 0 < w i)
    (g h : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    (F.reducedSquareRealRelativePart w (g * h)).coord =
      (F.reducedSquareRealRelativePart w g).coord +
      (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w g) *
        F.reducedSquareRealRelativePart w h *
        (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w g))⁻¹).coord := by
  have hk : F.reducedSquareRealSymbolHom w
      (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w g) *
        F.reducedSquareRealRelativePart w h *
        (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w g))⁻¹) = 1 := by
    simp only [map_mul, map_inv, F.reducedSquareRealSymbolHom_diagonal,
      F.reducedSquareRealRelativePart_projection, mul_one, mul_inv_cancel]
  rw [F.reducedSquareRealRelativePart_mul, coord_mul]
  exact F.reducedSquareRealSymbolKernel_bch w hw
    (F.reducedSquareRealRelativePart_coord_kernel w g) (congrArg NilpotentLieBCHGroup.coord hk)

theorem reducedSquareRealRelative_same_diagonal_mod_kernel (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    {g h : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w}
    (hg : g.coord ∈ realificationLieSubalgebra U) (hh : h.coord ∈ realificationLieSubalgebra U)
    (hproj : F.reducedSquareRealSymbolHom w g = F.reducedSquareRealSymbolHom w h) :
    (F.reducedSquareRealRelativePart w g).coord - (F.reducedSquareRealRelativePart w h).coord ∈
      (F.reducedSquareFastRelativeSubmodule w U).baseChange ℝ := by
  have hpair := splitRelativePart_pair_mem (F.reducedSquareRealSymbolHom w)
    (F.reducedSquareRealDiagonalHom w) (F.reducedSquareRealSymbolHom_diagonal w)
    (realificationSubgroup
      (hnil := F.squareFiltration.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w) U)
    hg hh hproj
  have hneg : (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ
      (-(F.reducedSquareRealRelativePart w h).coord) = 0 := by
    rw [map_neg, F.reducedSquareRealRelativePart_coord_kernel, neg_zero]
  have he : (F.reducedSquareRealRelativePart w g * (F.reducedSquareRealRelativePart w h)⁻¹).coord =
      (F.reducedSquareRealRelativePart w g).coord - (F.reducedSquareRealRelativePart w h).coord := by
    rw [coord_mul, coord_inv, F.reducedSquareRealSymbolKernel_bch w hw
      (F.reducedSquareRealRelativePart_coord_kernel w g) hneg, sub_eq_add_neg]
  change _ ∈ (U.toSubmodule ⊓ (F.reducedSquareSndSymbolMap w).ker.toSubmodule).baseChange ℝ
  rw [realification_inf, F.reducedSquareRealSymbolKernel_eq]
  constructor
  · have hm : (F.reducedSquareRealRelativePart w g * (F.reducedSquareRealRelativePart w h)⁻¹).coord ∈
        realificationLieSubalgebra U := hpair.1
    rwa [he] at hm
  · change (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ
      ((F.reducedSquareRealRelativePart w g).coord - (F.reducedSquareRealRelativePart w h).coord) = 0
    rw [map_sub, F.reducedSquareRealRelativePart_coord_kernel,
      F.reducedSquareRealRelativePart_coord_kernel, sub_self]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

noncomputable def realReducedRelativeSquareSymbolMap :
    (ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) →ₗ[ℝ]
      (ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w) :=
  (F.reducedRelativeSquareSymbolMap w hw).baseChange ℝ

theorem realReducedRelativeSquareSymbolMap_range :
    LinearMap.range (F.realReducedRelativeSquareSymbolMap w hw) =
      LinearMap.ker ((F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ) := by
  have h := realification_map (⊤ : Submodule ℚ (F.normalizedRelativeSubmodule w))
    (F.reducedRelativeSquareSymbolMap w hw)
  simp only [Submodule.map_top, Submodule.baseChange_top] at h
  change LinearMap.range ((F.reducedRelativeSquareSymbolMap w hw).baseChange ℝ) = _
  rw [← h, F.reducedRelativeSquareSymbolMap_range, F.reducedSquareRealSymbolKernel_eq]

@[simp] theorem realReducedRelativeSquareSymbolMap_projection
    (p : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ
      (F.realReducedRelativeSquareSymbolMap w hw p) = 0 := by
  have h : F.realReducedRelativeSquareSymbolMap w hw p ∈
      LinearMap.range (F.realReducedRelativeSquareSymbolMap w hw) := ⟨p, rfl⟩
  rw [F.realReducedRelativeSquareSymbolMap_range] at h
  exact h

theorem reducedSquareRealRelativePart_exists_preimage
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    ∃ p : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w,
      F.realReducedRelativeSquareSymbolMap w hw p = (F.reducedSquareRealRelativePart w g).coord := by
  change (F.reducedSquareRealRelativePart w g).coord ∈
    LinearMap.range (F.realReducedRelativeSquareSymbolMap w hw)
  rw [F.realReducedRelativeSquareSymbolMap_range]
  exact F.reducedSquareRealRelativePart_coord_kernel w g

theorem reducedSquareRealRelativePart_of_factors
    (k : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (x : F.quotientTop.RealPolynomialSymbolGroup w)
    (hk : F.reducedSquareRealSymbolHom w k = 1) :
    F.reducedSquareRealRelativePart w (k * F.reducedSquareRealDiagonalHom w x) = k := by
  change (k * F.reducedSquareRealDiagonalHom w x) *
    (F.reducedSquareRealDiagonalHom w
      (F.reducedSquareRealSymbolHom w (k * F.reducedSquareRealDiagonalHom w x)))⁻¹ = k
  rw [map_mul, F.reducedSquareRealSymbolHom_diagonal, hk, one_mul]
  group

include hw in
theorem reducedSquareRealRelativePart_triple_coord
    (E P R : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    (F.reducedSquareRealRelativePart w (E * P * R)).coord =
      (F.reducedSquareRealRelativePart w E).coord +
        (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w E) *
          F.reducedSquareRealRelativePart w P *
            (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w E))⁻¹).coord +
        (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w (E * P)) *
          F.reducedSquareRealRelativePart w R *
            (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w (E * P)))⁻¹).coord := by
  rw [F.reducedSquareRealRelativePart_mul_coord w hw (E * P) R,
    F.reducedSquareRealRelativePart_mul_coord w hw E P]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

theorem realNormalizedFirstCoefficientMap_ker :
    LinearMap.ker (F.realNormalizedFirstCoefficientMap w) =
      LinearMap.ker (F.realReducedRelativeSquareSymbolMap w hw) := by
  have hk : LinearMap.ker ((F.normalizedFirstCoefficientMap w).baseChange ℝ) =
      LinearMap.ker ((F.reducedRelativeSquareSymbolMap w hw).baseChange ℝ) := by
    rw [← realification_ker, ← realification_ker, F.normalizedFirstCoefficientMap_ker w hw]
  ext x
  change F.firstCoefficientRealEquiv w ((F.normalizedFirstCoefficientMap w).baseChange ℝ x) = 0 ↔
    (F.reducedRelativeSquareSymbolMap w hw).baseChange ℝ x = 0
  rw [LinearEquiv.map_eq_zero_iff]
  exact SetLike.ext_iff.mp hk x

noncomputable def realFirstCoefficientRelativeRangeEquiv :
    LinearMap.range (F.realNormalizedFirstCoefficientMap w) ≃ₗ[ℝ]
      LinearMap.range (F.realReducedRelativeSquareSymbolMap w hw) :=
  commonKernelRangeEquiv _ _ (F.realNormalizedFirstCoefficientMap_ker w hw)

theorem realFirstCoefficientRelativeRangeEquiv_apply (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    (F.realFirstCoefficientRelativeRangeEquiv w hw
      ⟨F.realNormalizedFirstCoefficientMap w x, ⟨x, rfl⟩⟩ :
        ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w) =
      F.realReducedRelativeSquareSymbolMap w hw x :=
  commonKernelRangeEquiv_apply _ _ _ x

noncomputable def realFirstCoefficientRelativeEquiv :
    LinearMap.ker (F.realFirstCoefficientHorizontal w) ≃ₗ[ℝ]
      LinearMap.ker ((F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ) :=
  commonKernelSubmoduleEquiv (F.realNormalizedFirstCoefficientMap w)
    (F.realReducedRelativeSquareSymbolMap w hw)
    (LinearMap.ker (F.realFirstCoefficientHorizontal w))
    (LinearMap.ker ((F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ))
    (F.realNormalizedFirstCoefficientMap_ker w hw)
    (F.realNormalizedFirstCoefficientMap_range w)
    (F.realReducedRelativeSquareSymbolMap_range w hw)

theorem realFirstCoefficientRelativeEquiv_apply (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w)
    (hx : F.realNormalizedFirstCoefficientMap w x ∈ LinearMap.ker (F.realFirstCoefficientHorizontal w)) :
    (F.realFirstCoefficientRelativeEquiv w hw ⟨F.realNormalizedFirstCoefficientMap w x, hx⟩ :
      ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w) =
      F.realReducedRelativeSquareSymbolMap w hw x :=
  commonKernelSubmoduleEquiv_apply (F.realNormalizedFirstCoefficientMap w)
    (F.realReducedRelativeSquareSymbolMap w hw) _ _ _ _ _ x hx

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def adaptedReducedSymbolMap :
    F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.quotientTop.PolynomialSymbol w :=
  (F.quotientTopSymbolMap w).comp (F.polynomialSymbolMap w)

noncomputable def adaptedReducedRealSymbolHom :
    F.RealAdaptedPolynomialGroup w →* F.quotientTop.RealPolynomialSymbolGroup w :=
  realificationMap
    (hnil := (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (hM := F.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (F.adaptedReducedSymbolMap w)

noncomputable def realNormalizedRelativeAdjoint (g : F.RealAdaptedPolynomialGroup w) :
    (ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) ≃ₗ[ℝ]
      (ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :=
  realIdealAdjoint (F.normalizedRelativeIdeal w)
    (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot g

theorem realNormalizedRelativeAdjoint_inclusion (g : F.RealAdaptedPolynomialGroup w)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    (F.normalizedRelativeSubmodule w).subtype.baseChange ℝ (F.realNormalizedRelativeAdjoint w g x) =
      dualAdjoint g ((F.normalizedRelativeSubmodule w).subtype.baseChange ℝ x) :=
  realIdealAdjoint_inclusion (F.normalizedRelativeIdeal w)
    (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot g x

theorem reducedRelativeSquareSymbolMap_lie (hw : ∀ i, 0 < w i)
    (a : F.adaptedLieSubalgebra w) (p : F.normalizedRelativeSubmodule w) :
    F.reducedRelativeSquareSymbolMap w hw
        ⟨⁅a, p.val⁆, F.normalizedRelativeSubmodule_lie_mem w a p.val p.property⟩ =
      ⁅F.reducedSquareDiagonalSymbolMap w (F.adaptedReducedSymbolMap w a),
        F.reducedRelativeSquareSymbolMap w hw p⁆ := by
  change F.reducedSquareSymbolMap w
      (F.squareFiltration.polynomialSymbolMap w
        (F.relativeSquareLift w hw ⟨⁅a, p.val⁆, _⟩)) = _
  rw [F.relativeSquareLift_lie, LieHom.map_lie, LieHom.map_lie,
    ← F.squareDiagonalSymbolMap_symbol, ← F.reducedSquareDiagonalSymbolMap_quotient]
  rfl

theorem realReducedRelativeSquareSymbolMap_adjoint (hw : ∀ i, 0 < w i)
    (g : F.RealAdaptedPolynomialGroup w) (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realReducedRelativeSquareSymbolMap w hw (F.realNormalizedRelativeAdjoint w g x) =
      dualAdjoint (F.reducedSquareRealDiagonalHom w (F.adaptedReducedRealSymbolHom w g))
        (F.realReducedRelativeSquareSymbolMap w hw x) := by
  let B := (F.reducedSquareDiagonalSymbolMap w).comp (F.adaptedReducedSymbolMap w)
  have hb : realificationMap
      (hnil := (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
      (hM := F.squareFiltration.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w) B g =
      F.reducedSquareRealDiagonalHom w (F.adaptedReducedRealSymbolHom w g) := by
    apply NilpotentLieBCHGroup.ext
    change ((F.reducedSquareDiagonalSymbolMap w).toLinearMap.comp
      (F.adaptedReducedSymbolMap w).toLinearMap).baseChange ℝ g.coord =
      (F.reducedSquareDiagonalSymbolMap w).toLinearMap.baseChange ℝ
        ((F.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ g.coord)
    rw [LinearMap.baseChange_comp, LinearMap.comp_apply]
  have he := realIdealMap_adjoint (F.normalizedRelativeIdeal w)
    (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot
    (F.squareFiltration.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w)
    B (F.reducedRelativeSquareSymbolMap w hw) (F.reducedRelativeSquareSymbolMap_lie w hw) g x
  rw [hb] at he
  exact he

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

noncomputable def realFirstCoefficientFastSubmodule : Submodule ℝ (F.RealFirstCoefficientModule w) :=
  ((F.firstCoefficientFastSubmodule w hw U).baseChange ℝ).map (F.firstCoefficientRealEquiv w).toLinearMap

theorem realFirstCoefficientFastSubmodule_le_horizontal_ker :
    F.realFirstCoefficientFastSubmodule w hw U ≤ LinearMap.ker (F.realFirstCoefficientHorizontal w) := by
  rintro x ⟨y, hy, rfl⟩
  change (F.firstCoefficientHorizontal w).baseChange ℝ
    ((F.firstCoefficientRealEquiv w).symm (F.firstCoefficientRealEquiv w y)) = 0
  rw [LinearEquiv.symm_apply_apply]
  have hm := Submodule.baseChange_mono ℝ (F.firstCoefficientFastSubmodule_le_horizontal_ker w hw U) hy
  rw [realification_ker] at hm
  exact hm

theorem realNormalizedFirstCoefficientMap_mem_fast_iff (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realNormalizedFirstCoefficientMap w x ∈ F.realFirstCoefficientFastSubmodule w hw U ↔
      F.realReducedRelativeSquareSymbolMap w hw x ∈ U.baseChange ℝ := by
  have hp : (F.firstCoefficientFastSubmodule w hw U).comap (F.normalizedFirstCoefficientMap w) =
      U.comap (F.reducedRelativeSquareSymbolMap w hw) := by
    ext p
    exact F.normalizedFirstCoefficientMap_mem_fast_iff w hw U p
  have hr := congrArg (fun P : Submodule ℚ (F.normalizedRelativeSubmodule w) => P.baseChange ℝ) hp
  rw [realification_comap, realification_comap] at hr
  have he : (F.normalizedFirstCoefficientMap w).baseChange ℝ x ∈
        (F.firstCoefficientFastSubmodule w hw U).baseChange ℝ ↔
      F.realReducedRelativeSquareSymbolMap w hw x ∈ U.baseChange ℝ := SetLike.ext_iff.mp hr x
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hyx : y = (F.normalizedFirstCoefficientMap w).baseChange ℝ x :=
      (F.firstCoefficientRealEquiv w).injective hxy
    rw [hyx] at hy
    exact he.mp hy
  · intro hx
    exact ⟨(F.normalizedFirstCoefficientMap w).baseChange ℝ x, he.mpr hx, rfl⟩

theorem realNormalizedFirstCoefficientMap_sub_mem_fast_iff
    (x y : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realNormalizedFirstCoefficientMap w x - F.realNormalizedFirstCoefficientMap w y ∈
        F.realFirstCoefficientFastSubmodule w hw U ↔
      F.realReducedRelativeSquareSymbolMap w hw x - F.realReducedRelativeSquareSymbolMap w hw y ∈
        U.baseChange ℝ := by
  rw [← map_sub, ← map_sub]
  exact F.realNormalizedFirstCoefficientMap_mem_fast_iff w hw U (x - y)

noncomputable def realFastCoefficientHorizontal :
    (F.RealFirstCoefficientModule w ⧸ F.realFirstCoefficientFastSubmodule w hw U) →ₗ[ℝ]
      (ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :=
  (F.realFirstCoefficientFastSubmodule w hw U).liftQ (F.realFirstCoefficientHorizontal w)
    (F.realFirstCoefficientFastSubmodule_le_horizontal_ker w hw U)

noncomputable def realFastCoefficientHorizontalSection :
    (ℝ ⊗[ℚ] (L ⧸ F.layer 2)) →ₗ[ℝ]
      (F.RealFirstCoefficientModule w ⧸ F.realFirstCoefficientFastSubmodule w hw U) :=
  (F.realFirstCoefficientFastSubmodule w hw U).mkQ.comp (F.realFirstCoefficientHorizontalSection w)

theorem realFastCoefficientHorizontal_section (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    F.realFastCoefficientHorizontal w hw U (F.realFastCoefficientHorizontalSection w hw U x) = x :=
  F.realFirstCoefficientHorizontal_section w x

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

include hw in
theorem reducedSquareRealRelative_conjugation
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (x : ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hx : (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ x = 0) :
    dualAdjoint g x =
      (g * (⟨x⟩ : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) * g⁻¹).coord := by
  let I := (realLieHomToRat (realificationLieHom (F.reducedSquareSndSymbolMap w))).ker
  apply dualAdjoint_eq_conjugation_of_abelian_ideal I _ g x hx
  intro a ha b hb
  exact F.reducedSquareRealSymbolKernel_lie_eq_zero w hw ha hb

theorem realReducedRelativeSquareSymbolMap_conjugation
    (g : F.RealAdaptedPolynomialGroup w) (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realReducedRelativeSquareSymbolMap w hw (F.realNormalizedRelativeAdjoint w g x) =
      (F.reducedSquareRealDiagonalHom w (F.adaptedReducedRealSymbolHom w g) *
        (⟨F.realReducedRelativeSquareSymbolMap w hw x⟩ :
          F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) *
        (F.reducedSquareRealDiagonalHom w (F.adaptedReducedRealSymbolHom w g))⁻¹).coord := by
  rw [F.realReducedRelativeSquareSymbolMap_adjoint]
  exact F.reducedSquareRealRelative_conjugation w hw _ _
    (F.realReducedRelativeSquareSymbolMap_projection w hw x)

theorem realReducedRelativeSquareSymbolMap_conjugation_of_eq
    (g : F.RealAdaptedPolynomialGroup w) (h : F.quotientTop.RealPolynomialSymbolGroup w)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w)
    (r : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (hg : F.adaptedReducedRealSymbolHom w g = h)
    (hx : F.realReducedRelativeSquareSymbolMap w hw x = r.coord) :
    F.realReducedRelativeSquareSymbolMap w hw (F.realNormalizedRelativeAdjoint w g x) =
      (F.reducedSquareRealDiagonalHom w h * r * (F.reducedSquareRealDiagonalHom w h)⁻¹).coord := by
  rw [F.realReducedRelativeSquareSymbolMap_conjugation, hg, hx]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

def reducedNativeIndex (s : ℕ) (w : σ → ℕ) (ω : ι → ℕ)
    (z : SymbolBasisIndex w (fun i : QuotientTopBasisIndex s ω => ω i.val)) :
    AdaptedBasisIndex w ω :=
  ⟨(z.val.1, z.val.2.val), z.property.le⟩

theorem reducedNativeIndex_injective (s : ℕ) (w : σ → ℕ) (ω : ι → ℕ) :
    Function.Injective (reducedNativeIndex s w ω) := by
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z : AdaptedBasisIndex w ω => z.val.1) h
  · apply Subtype.ext
    exact congrArg (fun z : AdaptedBasisIndex w ω => z.val.2) h

variable (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

local notation "bq" => F.quotientTopBasis b ω hF
local notation "ωq" => (fun i : QuotientTopBasisIndex s ω => ω (Subtype.val i))
local notation "hq" => F.quotientTopBasis_layers b ω hF
local notation "Bq" => F.quotientTop.polynomialSymbolBasis bq ωq hq w
local notation "Ba" => F.adaptedMonomialBasis b ω hF w

noncomputable def reducedNativeSection : F.quotientTop.PolynomialSymbol w →ₗ[ℚ] F.adaptedLieSubalgebra w :=
  (Bq).constr ℚ (fun z => Ba (reducedNativeIndex s w ω z))

@[simp] theorem reducedNativeSection_basis (z : SymbolBasisIndex w ωq) :
    F.reducedNativeSection b ω hF w (Bq z) = Ba (reducedNativeIndex s w ω z) :=
  Basis.constr_basis _ _ _ z

theorem adaptedReducedSymbolMap_native_basis (z : SymbolBasisIndex w ωq) :
    F.adaptedReducedSymbolMap w (Ba (reducedNativeIndex s w ω z)) = Bq z := by
  classical
  change F.quotientTop.polynomialSymbolMap w
    (F.quotientTopPolynomialMap w (Ba (reducedNativeIndex s w ω z))) = Bq z
  rw [F.quotientTop.polynomialSymbolBasis_apply]
  congr 1
  apply Subtype.ext
  apply coefficients.injective
  ext α
  change coefficients (VectorPolynomial.map (lieQuotientMap (F.layerIdeal (s + 1))).toLinearMap
    (Ba (reducedNativeIndex s w ω z)).val) α = _
  rw [coefficients_map, F.adaptedMonomialBasis_coe,
    F.quotientTop.adaptedMonomialBasis_coe, coefficients_monomial, coefficients_monomial]
  by_cases h : α = z.val.1
  · subst α
    simp only [reducedNativeIndex, Finsupp.single_eq_same, F.quotientTopBasis_apply]
    rfl
  · simp only [reducedNativeIndex, Finsupp.single_eq_of_ne h, map_zero]

theorem reducedNativeSection_rightInverse (x : F.quotientTop.PolynomialSymbol w) :
    F.adaptedReducedSymbolMap w (F.reducedNativeSection b ω hF w x) = x := by
  have he : (F.adaptedReducedSymbolMap w).toLinearMap.comp (F.reducedNativeSection b ω hF w) =
      LinearMap.id := by
    apply (Bq).ext
    intro z
    exact (congrArg (F.adaptedReducedSymbolMap w) (F.reducedNativeSection_basis b ω hF w z)).trans
      (F.adaptedReducedSymbolMap_native_basis b ω hF w z)
  exact DFunLike.congr_fun he x

theorem reducedNativeSection_coordinate (x : F.quotientTop.PolynomialSymbol w)
    (z : SymbolBasisIndex w ωq) :
    (Ba).repr (F.reducedNativeSection b ω hF w x) (reducedNativeIndex s w ω z) = (Bq).repr x z := by
  classical
  have he : ((Ba).coord (reducedNativeIndex s w ω z)).comp (F.reducedNativeSection b ω hF w) =
      (Bq).coord z := by
    apply (Bq).ext
    intro j
    change (Ba).repr (F.reducedNativeSection b ω hF w (Bq j)) (reducedNativeIndex s w ω z) =
      (Bq).repr (Bq j) z
    rw [F.reducedNativeSection_basis, Basis.repr_self, Basis.repr_self]
    simp only [Finsupp.single_apply, (reducedNativeIndex_injective s w ω).eq_iff]
  exact DFunLike.congr_fun he x

theorem reducedNativeSection_coordinate_zero (x : F.quotientTop.PolynomialSymbol w)
    (z : AdaptedBasisIndex w ω)
    (hz : ∀ j, reducedNativeIndex s w ω j ≠ z) :
    (Ba).repr (F.reducedNativeSection b ω hF w x) z = 0 := by
  classical
  have he : ((Ba).coord z).comp (F.reducedNativeSection b ω hF w) = 0 := by
    apply (Bq).ext
    intro j
    change (Ba).repr (F.reducedNativeSection b ω hF w (Bq j)) z = 0
    rw [F.reducedNativeSection_basis, Basis.repr_self]
    exact Finsupp.single_eq_of_ne (hz j).symm
  exact DFunLike.congr_fun he x

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

noncomputable def realReducedRelativeCoefficient
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    F.RealFirstCoefficientModule w :=
  ((F.realFirstCoefficientRelativeEquiv w hw).symm
    ⟨(F.reducedSquareRealRelativePart w g).coord, F.reducedSquareRealRelativePart_coord_kernel w g⟩).val

theorem realReducedRelativeCoefficient_horizontal
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    F.realFirstCoefficientHorizontal w (F.realReducedRelativeCoefficient w hw g) = 0 :=
  ((F.realFirstCoefficientRelativeEquiv w hw).symm
    ⟨(F.reducedSquareRealRelativePart w g).coord, F.reducedSquareRealRelativePart_coord_kernel w g⟩).property

theorem realReducedRelativeCoefficient_of_preimage
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w)
    (hx : F.realReducedRelativeSquareSymbolMap w hw x = (F.reducedSquareRealRelativePart w g).coord) :
    F.realNormalizedFirstCoefficientMap w x = F.realReducedRelativeCoefficient w hw g :=
  commonKernelSubmoduleEquiv_symm_apply (F.realNormalizedFirstCoefficientMap w)
    (F.realReducedRelativeSquareSymbolMap w hw)
    (LinearMap.ker (F.realFirstCoefficientHorizontal w))
    (LinearMap.ker ((F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ))
    (F.realNormalizedFirstCoefficientMap_ker w hw)
    (F.realNormalizedFirstCoefficientMap_range w)
    (F.realReducedRelativeSquareSymbolMap_range w hw) x
    ⟨(F.reducedSquareRealRelativePart w g).coord, F.reducedSquareRealRelativePart_coord_kernel w g⟩ hx

theorem realReducedRelativeCoefficient_same_diagonal
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    {g h : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w}
    (hg : g.coord ∈ realificationLieSubalgebra U) (hh : h.coord ∈ realificationLieSubalgebra U)
    (hproj : F.reducedSquareRealSymbolHom w g = F.reducedSquareRealSymbolHom w h) :
    F.realReducedRelativeCoefficient w hw g - F.realReducedRelativeCoefficient w hw h ∈
      F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U) := by
  obtain ⟨x, hx⟩ := F.reducedSquareRealRelativePart_exists_preimage w hw g
  obtain ⟨y, hy⟩ := F.reducedSquareRealRelativePart_exists_preimage w hw h
  rw [← F.realReducedRelativeCoefficient_of_preimage w hw g x hx,
    ← F.realReducedRelativeCoefficient_of_preimage w hw h y hy,
    F.realNormalizedFirstCoefficientMap_sub_mem_fast_iff w hw]
  rw [hx, hy]
  exact F.reducedSquareRealRelative_same_diagonal_mod_kernel w hw U hg hh hproj

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

local notation "bq" => F.quotientTopBasis b ω hF
local notation "ωq" => (fun i : QuotientTopBasisIndex s ω => ω (Subtype.val i))
local notation "hq" => F.quotientTopBasis_layers b ω hF
local notation "Bq" => F.quotientTop.polynomialSymbolBasis bq ωq hq w
local notation "Ba" => F.adaptedMonomialBasis b ω hF w

theorem reducedNativeSection_real_coordinate (x : F.quotientTop.RealPolynomialSymbol w)
    (z : SymbolBasisIndex w ωq) :
    ((Ba).baseChange ℝ).repr ((F.reducedNativeSection b ω hF w).baseChange ℝ x)
      (reducedNativeIndex s w ω z) = ((Bq).baseChange ℝ).repr x z := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul,
      F.reducedNativeSection_coordinate]

theorem reducedNativeSection_real_coordinate_zero (x : F.quotientTop.RealPolynomialSymbol w)
    (z : AdaptedBasisIndex w ω) (hz : ∀ j, reducedNativeIndex s w ω j ≠ z) :
    ((Ba).baseChange ℝ).repr ((F.reducedNativeSection b ω hF w).baseChange ℝ x) z = 0 := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_zero]
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul,
      F.reducedNativeSection_coordinate_zero b ω hF w x z hz]
    simp

noncomputable def realReducedNativeLift (g : F.quotientTop.RealPolynomialSymbolGroup w) :
    F.RealAdaptedPolynomialGroup w :=
  ⟨(F.reducedNativeSection b ω hF w).baseChange ℝ g.coord⟩

@[simp] theorem adaptedReducedRealSymbolHom_lift (g : F.quotientTop.RealPolynomialSymbolGroup w) :
    F.adaptedReducedRealSymbolHom w (F.realReducedNativeLift b ω hF w g) = g := by
  apply NilpotentLieBCHGroup.ext
  change (F.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ
    ((F.reducedNativeSection b ω hF w).baseChange ℝ g.coord) = g.coord
  have he : ∀ x : F.quotientTop.RealPolynomialSymbol w,
      (F.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ
        ((F.reducedNativeSection b ω hF w).baseChange ℝ x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
      exact congrArg (fun y => a ⊗ₜ[ℚ] y) (F.reducedNativeSection_rightInverse b ω hF w x)
  exact he g.coord

theorem realReducedNativeLift_slow (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) (g : F.quotientTop.RealPolynomialSymbolGroup w)
    (hg : F.quotientTop.SymbolSlowBound bq ωq hq w T M g) :
    F.RealAdaptedCoefficientBound b ω hF w T M (F.realReducedNativeLift b ω hF w g).coord := by
  intro z
  by_cases hz : ∃ j, reducedNativeIndex s w ω j = z
  · obtain ⟨j, rfl⟩ := hz
    change |((Ba).baseChange ℝ).repr ((F.reducedNativeSection b ω hF w).baseChange ℝ g.coord)
      (reducedNativeIndex s w ω j)| ≤ _
    rw [F.reducedNativeSection_real_coordinate]
    exact hg j
  · change |((Ba).baseChange ℝ).repr ((F.reducedNativeSection b ω hF w).baseChange ℝ g.coord) z| ≤ _
    rw [F.reducedNativeSection_real_coordinate_zero b ω hF w g.coord z (fun j hj => hz ⟨j, hj⟩), abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT z.val.1).le

theorem realReducedNativeLift_grid (l : ℕ) (g : F.quotientTop.RealPolynomialSymbolGroup w)
    (hg : F.quotientTop.SymbolRationalGrid bq ωq hq w l g) :
    F.RealAdaptedCoefficientGrid b ω hF w l (F.realReducedNativeLift b ω hF w g).coord := by
  classical
  obtain ⟨a, ha⟩ := hg
  refine ⟨fun z => if hz : ∃ j, reducedNativeIndex s w ω j = z then a hz.choose else 0, ?_⟩
  funext z
  change ((if hz : ∃ j, reducedNativeIndex s w ω j = z then a hz.choose else 0 : ℤ) : ℝ) =
    (l : ℝ) * ((Ba).baseChange ℝ).repr ((F.reducedNativeSection b ω hF w).baseChange ℝ g.coord) z
  by_cases hz : ∃ j, reducedNativeIndex s w ω j = z
  · rw [dite_eq_left hz]
    have hc := F.reducedNativeSection_real_coordinate b ω hF w g.coord hz.choose
    have he := congrArg (fun t => ((Ba).baseChange ℝ).repr
      ((F.reducedNativeSection b ω hF w).baseChange ℝ g.coord) t) hz.choose_spec
    rw [he.symm.trans hc]
    exact congrFun ha hz.choose
  · rw [dite_eq_right hz, Int.cast_zero,
      F.reducedNativeSection_real_coordinate_zero b ω hF w g.coord z (fun j hj => hz ⟨j, hj⟩), mul_zero]

theorem realReducedNativeLift_constant (g : F.quotientTop.RealPolynomialSymbolGroup w) :
    coefficients (F.realAdaptedPolynomialMap w (F.realReducedNativeLift b ω hF w g).coord) 0 = 0 := by
  apply (b.baseChange ℝ).repr.injective
  ext i
  change (b.baseChange ℝ).repr
    (coefficients (F.realAdaptedPolynomialMap w (F.realReducedNativeLift b ω hF w g).coord) 0) i = 0
  let z : AdaptedBasisIndex w ω := ⟨(0, i), by simp⟩
  have hz : ∀ j, reducedNativeIndex s w ω j ≠ z := by
    intro j hj
    have hmono := congrArg (fun t : AdaptedBasisIndex w ω => Finsupp.weight w t.val.1) hj
    change Finsupp.weight w j.val.1 = Finsupp.weight w 0 at hmono
    rw [map_zero] at hmono
    exact (F.adaptedBasis_weight_pos b ω hF j.val.2.val).ne' (j.property.symm.trans hmono)
  exact (F.realAdaptedPolynomialTensor_coordinates w b ω hF _ z).trans
    (F.reducedNativeSection_real_coordinate_zero b ω hF w g.coord z hz)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

local notation "bq" => F.quotientTopBasis b ω hF
local notation "ωq" => (fun i : QuotientTopBasisIndex s ω => ω (Subtype.val i))
local notation "hq" => F.quotientTopBasis_layers b ω hF

theorem exists_reduced_native_factorization (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) (l : ℕ) (g : F.RealAdaptedPolynomialGroup w)
    (A P R : F.quotientTop.RealPolynomialSymbolGroup w)
    (hprod : A * P * R = F.adaptedReducedRealSymbolHom w g)
    (hA : F.quotientTop.SymbolSlowBound bq ωq hq w T M A)
    (hR : F.quotientTop.SymbolRationalGrid bq ωq hq w l R) :
    ∃ a p r : F.RealAdaptedPolynomialGroup w,
      a * p * r = g ∧ F.adaptedReducedRealSymbolHom w a = A ∧
      F.adaptedReducedRealSymbolHom w p = P ∧ F.adaptedReducedRealSymbolHom w r = R ∧
      F.RealAdaptedCoefficientBound b ω hF w T M a.coord ∧
      F.RealAdaptedCoefficientGrid b ω hF w l r.coord ∧
      coefficients (F.realAdaptedPolynomialMap w a.coord) 0 = 0 ∧
      coefficients (F.realAdaptedPolynomialMap w r.coord) 0 = 0 ∧
      coefficients (F.realAdaptedPolynomialMap w p.coord) 0 =
        coefficients (F.realAdaptedPolynomialMap w g.coord) 0 := by
  let a := F.realReducedNativeLift b ω hF w A
  let r := F.realReducedNativeLift b ω hF w R
  let p := a⁻¹ * g * r⁻¹
  have hapr : a * p * r = g := by simp [p, mul_assoc]
  have ha : F.adaptedReducedRealSymbolHom w a = A := F.adaptedReducedRealSymbolHom_lift b ω hF w A
  have hr : F.adaptedReducedRealSymbolHom w r = R := F.adaptedReducedRealSymbolHom_lift b ω hF w R
  have hp : F.adaptedReducedRealSymbolHom w p = P := by
    change F.adaptedReducedRealSymbolHom w (a⁻¹ * g * r⁻¹) = P
    rw [map_mul, map_mul, map_inv, map_inv, ha, hr, ← hprod]
    simp [mul_assoc]
  have ha0 := F.realReducedNativeLift_constant b ω hF w A
  have hr0 := F.realReducedNativeLift_constant b ω hF w R
  refine ⟨a, p, r, hapr, ha, hp, hr, F.realReducedNativeLift_slow b ω hF w T hT hM A hA,
    F.realReducedNativeLift_grid b ω hF w l R hR, ha0, hr0, ?_⟩
  have hpoly : F.realAdaptedPolynomialGroupHom w a * F.realAdaptedPolynomialGroupHom w p *
      F.realAdaptedPolynomialGroupHom w r = F.realAdaptedPolynomialGroupHom w g := by
    rw [← map_mul, ← map_mul, hapr]
  exact F.realification.polynomial_factor_middle_constant w
    (F.realAdaptedPolynomialGroupHom w g) (F.realAdaptedPolynomialGroupHom w a)
    (F.realAdaptedPolynomialGroupHom w p) (F.realAdaptedPolynomialGroupHom w r) hpoly ha0 hr0

end Erdos3.NilpotentLieFiltration

end

end OAI
