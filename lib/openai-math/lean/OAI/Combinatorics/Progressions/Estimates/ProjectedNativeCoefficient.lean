/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.BoundedRealifiedSquareOrbit
import OAI.Combinatorics.Progressions.Estimates.RealProjectedCoefficientLift
import OAI.Combinatorics.Progressions.Linear.RealRankHorizontalSymbol
import OAI.Combinatorics.Progressions.Nilpotent.RealifiedBCHProductEquiv

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def adaptedTranslateLinear (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h : σ → ℚ) :
    F.adaptedLieSubalgebra w →ₗ[ℚ] F.adaptedLieSubalgebra w :=
  ((VectorPolynomial.translate h).comp (F.adaptedLieSubalgebra w).incl.toLinearMap).codRestrict
    (F.adaptedLieSubalgebra w).toSubmodule (by
      intro p
      exact (F.mem_adaptedSubmodule w _).mpr
        (F.adapted_translate w hw h ((F.mem_adaptedSubmodule w _).mp p.property)))

@[simp] theorem adaptedTranslateLinear_coe (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h : σ → ℚ)
    (p : F.adaptedLieSubalgebra w) :
    (F.adaptedTranslateLinear w hw h p : VectorPolynomial σ ℚ L) = translate h p.val := rfl

theorem polynomialSymbolMap_adaptedTranslateLinear (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h : σ → ℚ)
    (p : F.adaptedLieSubalgebra w) :
    F.polynomialSymbolMap w (F.adaptedTranslateLinear w hw h p) = F.polynomialSymbolMap w p := by
  exact F.polynomialSymbolMap_translate w hw h p

theorem realPolynomialSymbolMap_translate (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h : σ → ℚ)
    (p : F.realification.adaptedLieSubalgebra w) :
    F.realPolynomialSymbolMap b ω hF w (F.realification.adaptedTranslateLinear w hw h p) =
      F.realPolynomialSymbolMap b ω hF w p := by
  apply sub_eq_zero.mp
  rw [← map_sub, F.realPolynomialSymbolMap_eq_zero_iff, map_sub, sub_eq_zero]
  exact F.realification.polynomialSymbolMap_adaptedTranslateLinear w hw h p

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem realFilteredPolynomialSymbolMap_extended (w : σ → ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ (F.realExtendedSymbolMap w x) =
      G.realExtendedSymbolMap w ((F.filteredPolynomialMap G φ hφ w).toLinearMap.baseChange ℝ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a p => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realFilteredPolynomialSymbolMap_polynomial
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (p : F.realification.adaptedLieSubalgebra w) :
    (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ
        (F.realPolynomialSymbolMap b ω hF w p) =
      G.realSymbolOfPolynomial c τ hG w
        (VectorPolynomial.map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) p.val) := by
  obtain ⟨x, rfl⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hF p
  change (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ
    (F.realSymbolOfPolynomial b ω hF w (F.realAdaptedPolynomialMap w x)) = _
  rw [F.realSymbolOfPolynomial_realAdaptedPolynomialMap,
    F.realFilteredPolynomialSymbolMap_extended,
    ← G.realSymbolOfPolynomial_realAdaptedPolynomialMap c τ hG,
    F.realFilteredPolynomialMap_polynomial]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {F : NilpotentLieFiltration L s} {w : σ → ℕ}

noncomputable def PolynomialOrbit.translate (g : F.PolynomialOrbit w)
    (hw : ∀ i, 0 < w i) (h : σ → ℤ) : F.PolynomialOrbit w :=
  polynomialOrbitOfLog (VectorPolynomial.translate (fun i => (h i : ℚ)) g.log)
    (F.adapted_translate w hw _ g.adapted)

@[simp] theorem polynomialOrbitEval_translate (g : F.PolynomialOrbit w)
    (hw : ∀ i, 0 < w i) (h x : σ → ℤ) :
    F.polynomialOrbitEval w x (g.translate hw h) = F.polynomialOrbitEval w (x + h) g := by
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.eval (fun i => (x i : ℚ))
      (VectorPolynomial.translate (fun i => (h i : ℚ)) g.log) =
    VectorPolynomial.eval (fun i => ((x + h) i : ℚ)) g.log
  rw [VectorPolynomial.eval_translate]
  simp only [Pi.add_apply, Int.cast_add]

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

noncomputable def integerOrbitPoint
    (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)) (n : ℤ) : D.Space :=
  QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
    (fun _ : Unit => 1) (fun _ => n) g)

@[simp] theorem cyclicOrbitPoint_translate
    (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (h : ℤ) (N : ℕ) [NeZero N] (x : ZMod N) :
    D.cyclicOrbitPoint (g.translate (fun _ => Nat.zero_lt_one) (fun _ => h)) N
      (fun _ : Unit => x) = D.integerOrbitPoint g ((x.val : ℤ) + h) := by
  unfold cyclicOrbitPoint integerOrbitPoint
  rw [NilpotentLieFiltration.polynomialOrbitEval_translate]
  rfl

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

noncomputable def nativeHorizontalCoefficientHom (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.associatedDegree.realification.PolynomialOrbit w →*
      Multiplicative (ℝ ⊗[ℚ] F.HigherHorizontal (Finsupp.weight w α)) :=
  (F.realHorizontalPolynomialHom hs b ω hF w α).comp
    (F.associatedDegree.realification.polynomialOrbitCoordinates w).toMonoidHom

@[simp] theorem nativeHorizontalCoefficientHom_apply (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ)
    (g : F.associatedDegree.realification.PolynomialOrbit w) :
    Multiplicative.toAdd (F.nativeHorizontalCoefficientHom hs b ω hF w α g) =
      (F.higherHorizontalSymbolCoefficient w α).baseChange ℝ
        (F.associatedDegree.realSymbolOfPolynomial b ω hF w g.log) := rfl

theorem nativeHorizontalCoefficientHom_tensor (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ)
    (g : F.associatedDegree.realification.PolynomialOrbit w)
    (x : ℝ ⊗[ℚ] F.associatedDegree.adaptedLieSubalgebra w)
    (hx : g.log = F.associatedDegree.realAdaptedPolynomialMap w x) :
    Multiplicative.toAdd (F.nativeHorizontalCoefficientHom hs b ω hF w α g) =
      (F.higherHorizontalCoefficient w α).baseChange ℝ x := by
  rw [F.nativeHorizontalCoefficientHom_apply, hx,
    F.associatedDegree.realSymbolOfPolynomial_realAdaptedPolynomialMap]
  exact F.realHorizontalSymbolCoefficient_extended w α x

theorem nativeHorizontalCoefficientHom_translate (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (α : σ →₀ ℕ)
    (g : F.associatedDegree.realification.PolynomialOrbit w) (h : σ → ℤ) :
    F.nativeHorizontalCoefficientHom hs b ω hF w α (g.translate hw h) =
      F.nativeHorizontalCoefficientHom hs b ω hF w α g := by
  change Multiplicative.ofAdd ((F.higherHorizontalSymbolCoefficient w α).baseChange ℝ
    (F.associatedDegree.realPolynomialSymbolMap b ω hF w
      (F.associatedDegree.realification.adaptedTranslateLinear w hw (fun i => (h i : ℚ))
        ⟨g.log, g.property⟩))) = _
  rw [F.associatedDegree.realPolynomialSymbolMap_translate]
  rfl

theorem nativeHorizontalCoefficientHom_basis_independent (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ L) (τ : κ → ℕ)
    (hG : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.nativeHorizontalCoefficientHom hs b ω hF w α =
      F.nativeHorizontalCoefficientHom hs c τ hG w α := by
  apply MonoidHom.ext
  intro g
  obtain ⟨x, hx⟩ := F.associatedDegree.realAdaptedPolynomialTensor_surjective w b ω hF
    (⟨g.log, g.property⟩ : F.associatedDegree.realification.adaptedLieSubalgebra w)
  have hlog : g.log = F.associatedDegree.realAdaptedPolynomialMap w x :=
    (congrArg Subtype.val hx).symm
  change Multiplicative.toAdd (F.nativeHorizontalCoefficientHom hs b ω hF w α g) =
    Multiplicative.toAdd (F.nativeHorizontalCoefficientHom hs c τ hG w α g)
  rw [F.nativeHorizontalCoefficientHom_tensor hs b ω hF w α g x hlog,
    F.nativeHorizontalCoefficientHom_tensor hs c τ hG w α g x hlog]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def realSquarePairHom :
    F.squareFiltration.realification.Group →* (pi (fun _ : Bool => F)).realification.Group :=
  realificationMap (hnil := F.squareFiltration.lowerCentralSeries_eq_bot)
    (hM := (pi (fun _ : Bool => F)).lowerCentralSeries_eq_bot) F.squarePairMap

theorem realSquarePairHom_component (z : F.squareFiltration.realification.Group) (b : Bool) :
    realBCHPiEquiv (fun _ : Bool => F) (F.realSquarePairHom z) b =
      cond b (F.realSquareFstHom z) (F.realSquareSndHom z) := by
  cases b
  · apply NilpotentLieBCHGroup.ext
    change realificationLieHom (liePiEval false) (realificationLieHom F.squarePairMap z.coord) =
      realificationLieHom F.squareSnd z.coord
    induction z.coord using TensorProduct.inductionOn with
    | tmul r x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  · apply NilpotentLieBCHGroup.ext
    change realificationLieHom (liePiEval true) (realificationLieHom F.squarePairMap z.coord) =
      realificationLieHom F.squareFst z.coord
    induction z.coord using TensorProduct.inductionOn with
    | tmul r x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]

theorem realSquarePairHom_normalization (ε γ a b : F.realification.Group)
    (z : F.squareFiltration.realification.Group)
    (hf : F.realSquareFstHom z = ε⁻¹ * a * γ⁻¹)
    (hs : F.realSquareSndHom z = b) :
    (realBCHPiEquiv (fun _ : Bool => F)).symm (fun flag => cond flag ε⁻¹ 1) *
      (realBCHPiEquiv (fun _ : Bool => F)).symm (fun flag => cond flag a b) *
      ((realBCHPiEquiv (fun _ : Bool => F)).symm (fun flag => cond flag γ 1))⁻¹ =
        F.realSquarePairHom z := by
  apply (realBCHPiEquiv (fun _ : Bool => F)).injective
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  funext flag
  rw [F.realSquarePairHom_component]
  cases flag <;> simp only [Pi.mul_apply, Pi.inv_apply, Bool.cond_false, Bool.cond_true,
    inv_one, one_mul, mul_one, hf, hs]

end Erdos3.NilpotentLieFiltration

namespace Erdos3

open scoped TensorProduct

theorem exists_native_two_shift_normalization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (a b : σ → ℤ) (g : D.filtration.realification.PolynomialOrbit w),
      ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
        (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 1 + C) ^ C)) ∧
        ∃ q : D.filtration.squareFiltration.realification.PolynomialOrbit w,
          ∀ x : σ → ℤ,
            D.filtration.realSquareFstHom
              (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q) =
                ε⁻¹ * D.filtration.realification.polynomialOrbitEval w (x + a) g * γ⁻¹ ∧
            D.filtration.realSquareSndHom
              (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q) =
                D.filtration.realification.polynomialOrbitEval w (x + b) g := by
  obtain ⟨C, hC, hnorm⟩ := exists_bounded_realified_square_orbit s
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ D p hp hD w hw a b g
  obtain ⟨ε, γ, hγ, hε, q, hq⟩ := hnorm D p hp hD w hw (a - b) g
  refine ⟨ε, γ, hγ, hε, q.translate hw b, ?_⟩
  intro x
  rw [NilpotentLieFiltration.polynomialOrbitEval_translate]
  have hx : (fun i => (x + b) i + (a - b) i) = x + a := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    abel
  simpa only [hx] using hq (x + b)

end Erdos3

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r) (F : NilpotentLieFiltration M t)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ k, φ x k ∈ G.layer d 1)

theorem projectedHorizontalSymbolCoefficient_native (hs : 1 ≤ s)
    (b : Basis ι ℚ M) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ L) (τ : κ → ℕ)
    (hG : ∀ j, G.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) (p : F.realification.adaptedLieSubalgebra w)
    (g : G.associatedDegree.realification.PolynomialOrbit w) (k : Fin 4)
    (hg : VectorPolynomial.map
      ((realificationLieHom ((liePiEval k).comp φ)).toLinearMap.restrictScalars ℚ) p.val = g.log) :
    (LinearMap.proj k).baseChange ℝ
        ((G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ
          (F.realPolynomialSymbolMap b ω hF w p)) =
      Multiplicative.toAdd (G.nativeHorizontalCoefficientHom hs c τ hG w α g) := by
  rw [G.real_projectedHorizontalSymbolCoefficient_component,
    G.nativeHorizontalCoefficientHom_apply]
  change (G.higherHorizontalSymbolCoefficient w α).baseChange ℝ
    ((F.filteredPolynomialSymbolMap G.associatedDegree ((liePiEval k).comp φ)
      (G.projectedComponent_mem_layer F φ hφ k) w).toLinearMap.baseChange ℝ
        (F.realPolynomialSymbolMap b ω hF w p)) = _
  rw [F.realFilteredPolynomialSymbolMap_polynomial G.associatedDegree ((liePiEval k).comp φ)
    (G.projectedComponent_mem_layer F φ hφ k) b ω hF c τ hG w p, hg]

end Erdos3.DegreeRankLieFiltration

end

end OAI
