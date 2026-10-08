/-
Modified for ProveIt: give common_coefficient_derivative_system a local
400000-heartbeat budget for dependent quotient reduction on Lean 4.32.
The upstream theorem statements and proof text are unchanged.
-/
/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Dynamics.CommonInitialBudget
import OAI.Combinatorics.Progressions.Dynamics.CommonTerminalBudget
import OAI.Combinatorics.Progressions.Dynamics.TerminalCompositionBudget
import OAI.Combinatorics.Progressions.Estimates.TerminalControlledFactorization
import OAI.Combinatorics.Progressions.Geometry.FullFastCoefficientCoordinates

namespace OAI

section

namespace Erdos3

theorem exists_derivative_difference_inputs
    {σ κ : Type*} [Fintype σ] [Fintype κ]
    (T : σ → ℝ) (scale : κ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ))
    (A : Matrix κ κ ℝ) (l : ℕ) (H : Finset (σ → ℤ)) (h₀ : σ → ℤ) (R : ℝ)
    (hinputs : ∀ h ∈ H, ∃ r : κ → ℝ, r ∈ realDenominatorGrid l ∧
      ‖derivativeGridPoint T scale Y A (h - h₀) r‖ ≤ R) :
    ∃ D : Finset (σ → ℤ), D.card = H.card ∧
      ∃ q : (σ → ℤ) → κ → ℝ, ∀ h ∈ D,
        q h ∈ realDenominatorGrid l ∧ ‖derivativeGridPoint T scale Y A h (q h)‖ ≤ R := by
  classical
  let D := H.image (fun h => h - h₀)
  let q : (σ → ℤ) → κ → ℝ := fun h =>
    if hh : h + h₀ ∈ H then (hinputs (h + h₀) hh).choose else 0
  refine ⟨D, ?_, q, ?_⟩
  · apply Finset.card_image_iff.mpr
    intro h _ k _ he
    simpa only [sub_add_cancel] using congrArg (fun x => x + h₀) he
  · intro h hh
    have hh' : h + h₀ ∈ H := by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hh
      simpa only [sub_add_cancel] using hk
    simpa only [q, dite_eq_left hh', add_sub_cancel_right] using
      (hinputs (h + h₀) hh').choose_spec

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realPolynomialSymbolHom_groupHom_coord (g : F.RealAdaptedPolynomialGroup w) :
    (F.realPolynomialSymbolHom b ω hF w (F.realAdaptedPolynomialGroupHom w g)).coord =
      F.realExtendedSymbolMap w g.coord :=
  F.realSymbolOfPolynomial_realAdaptedPolynomialMap b ω hF w g.coord

noncomputable def nativeSymbolNormalize (g : F.RealAdaptedPolynomialGroup w) :
    F.RealAdaptedPolynomialGroup w :=
  F.realAdaptedPolynomialGroupLift w b ω hF
    (F.realPolynomialSymbolLift b ω hF w
      (F.realPolynomialSymbolHom b ω hF w (F.realAdaptedPolynomialGroupHom w g)))

theorem nativeSymbolNormalize_symbol (g : F.RealAdaptedPolynomialGroup w) :
    F.realExtendedSymbolMap w (F.nativeSymbolNormalize b ω hF w g).coord =
      F.realExtendedSymbolMap w g.coord := by
  have he : F.realPolynomialSymbolHom b ω hF w
      (F.realAdaptedPolynomialGroupHom w (F.nativeSymbolNormalize b ω hF w g)) =
      F.realPolynomialSymbolHom b ω hF w (F.realAdaptedPolynomialGroupHom w g) := by
    unfold nativeSymbolNormalize
    rw [F.realAdaptedPolynomialGroupHom_lift, F.realPolynomialSymbolHom_lift]
  have hc := congrArg NilpotentLieBCHGroup.coord he
  simpa only [F.realPolynomialSymbolHom_groupHom_coord] using hc

theorem nativeSymbolNormalize_constant (g : F.RealAdaptedPolynomialGroup w) :
    coefficients (F.realAdaptedPolynomialMap w (F.nativeSymbolNormalize b ω hF w g).coord) 0 = 0 := by
  let X : F.RealPolynomialSymbolGroup w :=
    F.realPolynomialSymbolHom b ω hF w (F.realAdaptedPolynomialGroupHom w g)
  have hX : coefficients (F.realSymbolRepresentative b ω hF w X.coord) 0 = 0 :=
    F.realSymbolRepresentative_constant b ω hF w X.coord
  change coefficients (F.realAdaptedPolynomialGroupHom w
    (F.realAdaptedPolynomialGroupLift w b ω hF (F.realPolynomialSymbolLift b ω hF w X))).coord.val 0 = 0
  rw [F.realAdaptedPolynomialGroupHom_lift, F.realPolynomialSymbolLift_log, hX]

theorem realAdaptedGradedPolynomialHom_eq_of_symbol_eq
    (g h : F.RealAdaptedPolynomialGroup w)
    (he : F.realExtendedSymbolMap w g.coord = F.realExtendedSymbolMap w h.coord) :
    F.realAdaptedGradedPolynomialHom b ω hF w g = F.realAdaptedGradedPolynomialHom b ω hF w h := by
  apply NilpotentLieBCHGroup.ext
  change F.realAdaptedGradedPolynomialLie b ω hF w g.coord =
    F.realAdaptedGradedPolynomialLie b ω hF w h.coord
  rw [F.realAdaptedGradedPolynomialLie_symbol, F.realAdaptedGradedPolynomialLie_symbol]
  change F.realGradedSymbolPolynomial b ω hF w (F.realExtendedSymbolMap w g.coord) =
    F.realGradedSymbolPolynomial b ω hF w (F.realExtendedSymbolMap w h.coord)
  rw [he]

include b ω hF in
theorem realFirstCoefficientDirectionMap_eq_of_symbol_eq [Fintype σ]
    (g h : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (he : F.realExtendedSymbolMap (fun _ => 1) g.coord = F.realExtendedSymbolMap (fun _ => 1) h.coord) :
    F.realFirstCoefficientDirectionMap g.coord = F.realFirstCoefficientDirectionMap h.coord := by
  classical
  apply (Pi.basisFun ℝ σ).ext
  intro i
  apply F.realFirstCoefficientGradedPolynomial_injective b ω hF (fun _ => 1)
  change F.realFirstCoefficientGradedPolynomial b ω hF (fun _ => 1)
      (F.realFirstCoefficientDirectionMap g.coord (Pi.single i 1)) =
    F.realFirstCoefficientGradedPolynomial b ω hF (fun _ => 1)
      (F.realFirstCoefficientDirectionMap h.coord (Pi.single i 1))
  rw [F.realFirstCoefficientGradedPolynomial_direction, F.realFirstCoefficientGradedPolynomial_direction,
    F.realAdaptedGradedPolynomialHom_eq_of_symbol_eq b ω hF (fun _ => 1) g h he]

include b ω hF in
theorem realFirstCoefficientAdjoint_eq_of_symbol_eq
    (g h : F.RealAdaptedPolynomialGroup w)
    (he : F.realExtendedSymbolMap w g.coord = F.realExtendedSymbolMap w h.coord)
    (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientAdjoint w g x = F.realFirstCoefficientAdjoint w h x := by
  apply F.realFirstCoefficientGradedPolynomial_injective b ω hF w
  rw [F.realFirstCoefficientGradedPolynomial_adjoint, F.realFirstCoefficientGradedPolynomial_adjoint,
    F.realAdaptedGradedPolynomialHom_eq_of_symbol_eq b ω hF w g h he]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

theorem bounded_coefficient_derivative_point
    {σ ι κ L : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
    (b : Basis κ ℝ (F.RealFirstCoefficientModule (fun _ : σ => 1) ⧸
      F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)))
    (rows : κ → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hB : (F.adaptedReducedRealSymbolHom (fun _ => 1) B).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) U))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (C M N : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hN : 0 ≤ N) (l m : ℕ)
    (hslow : ∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (M + N) x → ∀ i,
      |b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) i| ≤
          C * (M + N) / monomialScale T (rows i).val.1)
    (hgrid : ∀ x, F.FirstCoefficientGrid e ω hF (fun _ => 1) l x →
      b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) ∈ realDenominatorGrid m)
    (h h₀ : σ → ℤ) (hhbox : ∀ i, |(h i : ℝ)| ≤ T i) (hh₀box : ∀ i, |(h₀ i : ℝ)| ≤ T i)
    (S S₀ R R₀ Z : F.RealFirstCoefficientModule (fun _ : σ => 1))
    (hh : F.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) -
      (S + F.realFirstCoefficientAdjoint (fun _ => 1) B R + Z) ∈
        F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U))
    (hh₀ : F.realFirstCoefficientDirectionMap B.coord (fun i => (h₀ i : ℝ)) -
      (S₀ + F.realFirstCoefficientAdjoint (fun _ => 1) B R₀ + Z) ∈
        F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U))
    (hS : F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T M S)
    (hS₀ : F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T N S₀)
    (hR : F.FirstCoefficientGrid e ω hF (fun _ => 1) l R)
    (hR₀ : F.FirstCoefficientGrid e ω hF (fun _ => 1) l R₀) :
    let Y := F.fastCoefficientDirectionCoordinates U b B
    let A := LinearMap.toMatrix b b (F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB).toLinearMap
    let scale := fun i => monomialScale T (rows i).val.1
    ∃ r : κ → ℝ, r ∈ realDenominatorGrid m ∧
      derivativeGridPoint T scale Y A (h - h₀) r ∈ derivativeGridPoints T scale Y A m ∧
      ‖derivativeGridPoint T scale Y A (h - h₀) r‖ ≤ max 2 (C * (M + N)) := by
  dsimp only
  let V := F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
    (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)
  let r := b.equivFun (V.mkQ (R - R₀))
  let a := b.equivFun (V.mkQ (S - S₀))
  have hdiff := F.coefficient_common_derivative_difference V B
    (fun i => (h i : ℝ)) (fun i => (h₀ i : ℝ)) S S₀ R R₀ Z hh hh₀
  have hdiff' : F.realFirstCoefficientDirectionMap B.coord (fun i => ((h - h₀) i : ℝ)) -
      ((S - S₀) + F.realFirstCoefficientAdjoint (fun _ => 1) B (R - R₀)) ∈ V := by
    have hcast : (fun i => ((h - h₀) i : ℝ)) =
        (fun i => (h i : ℝ)) - (fun i => (h₀ i : ℝ)) := by
      funext i
      simp only [Pi.sub_apply, Int.cast_sub]
    rw [hcast]
    exact hdiff
  have heq := F.fastCoefficientDerivative_coordinates U b B hB
    (fun i => ((h - h₀) i : ℝ)) (S - S₀) (R - R₀) hdiff'
  have hr : r ∈ realDenominatorGrid m := hgrid (R - R₀)
    (F.firstCoefficientGrid_sub e ω hF (fun _ => 1) l R R₀ hR hR₀)
  have ha : ∀ i, |a i| ≤ C * (M + N) / monomialScale T (rows i).val.1 :=
    hslow (S - S₀) (F.firstCoefficientSlowBound_sub e ω hF (fun _ => 1) T M N S S₀ hS hS₀)
  refine ⟨r, hr, derivativeGridPoint_mem _ _ _ _ m (h - h₀) r hr, ?_⟩
  apply derivativeGridPoint_bound T hT _ (fun i => monomialScale_pos T hT (rows i).val.1)
    _ _ (h - h₀) r a 2 (C * (M + N)) (by norm_num) (mul_nonneg hC (add_nonneg hM hN)) ?_ heq ha
  intro i
  change |((h i - h₀ i : ℤ) : ℝ)| ≤ 2 * T i
  rw [Int.cast_sub]
  exact (abs_sub _ _).trans (by linarith [hhbox i, hh₀box i])

theorem bounded_coefficient_derivative_family
    {σ ι κ L : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
    (b : Basis κ ℝ (F.RealFirstCoefficientModule (fun _ : σ => 1) ⧸
      F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)))
    (rows : κ → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hB : (F.adaptedReducedRealSymbolHom (fun _ => 1) B).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) U))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M) (l m : ℕ)
    (hslow : ∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (M + M) x → ∀ i,
      |b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) i| ≤
          C * (M + M) / monomialScale T (rows i).val.1)
    (hgrid : ∀ x, F.FirstCoefficientGrid e ω hF (fun _ => 1) l x →
      b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) ∈ realDenominatorGrid m)
    (H : Finset (σ → ℤ)) (h₀ : σ → ℤ) (hh₀ : h₀ ∈ H)
    (S R : (σ → ℤ) → F.RealFirstCoefficientModule (fun _ : σ => 1))
    (Z : F.RealFirstCoefficientModule (fun _ : σ => 1))
    (hbox : ∀ h ∈ H, ∀ i, |(h i : ℝ)| ≤ T i)
    (hcommon : ∀ h ∈ H, F.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ => 1) B (R h) + Z) ∈
        F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U))
    (hS : ∀ h ∈ H, F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T M (S h))
    (hR : ∀ h ∈ H, F.FirstCoefficientGrid e ω hF (fun _ => 1) l (R h)) :
    let Y := F.fastCoefficientDirectionCoordinates U b B
    let A := LinearMap.toMatrix b b (F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB).toLinearMap
    let scale := fun i => monomialScale T (rows i).val.1
    ∃ P : Finset ((σ → ℝ) × (κ → ℝ)), P.card = H.card ∧
      ∀ v ∈ P, v ∈ derivativeGridPoints T scale Y A m ∧ ‖v‖ ≤ max 2 (C * (M + M)) := by
  dsimp only
  apply exists_bounded_derivativeGridPoint_family T (fun i => (hT i).ne') _ _ _ m H h₀
    (max 2 (C * (M + M)))
  intro h hh
  have hp := F.bounded_coefficient_derivative_point e ω hF U b rows B hB T hT C M M hC hM hM l m
    hslow hgrid h h₀ (hbox h hh) (hbox h₀ hh₀) (S h) (S h₀) (R h) (R h₀) Z
    (hcommon h hh) (hcommon h₀ hh₀) (hS h hh) (hS h₀ hh₀) (hR h hh) (hR h₀ hh₀)
  obtain ⟨r, hr, _, hbound⟩ := hp
  exact ⟨r, hr, hbound⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

theorem bounded_coefficient_difference_inputs
    {σ ι κ L : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
    (b : Basis κ ℝ (F.RealFirstCoefficientModule (fun _ : σ => 1) ⧸
      F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)))
    (rows : κ → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hB : (F.adaptedReducedRealSymbolHom (fun _ => 1) B).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) U))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M) (l m : ℕ)
    (hslow : ∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (M + M) x → ∀ i,
      |b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) i| ≤
          C * (M + M) / monomialScale T (rows i).val.1)
    (hgrid : ∀ x, F.FirstCoefficientGrid e ω hF (fun _ => 1) l x →
      b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) ∈ realDenominatorGrid m)
    (H : Finset (σ → ℤ)) (h₀ : σ → ℤ) (hh₀ : h₀ ∈ H)
    (S R : (σ → ℤ) → F.RealFirstCoefficientModule (fun _ : σ => 1))
    (Z : F.RealFirstCoefficientModule (fun _ : σ => 1))
    (hbox : ∀ h ∈ H, ∀ i, |(h i : ℝ)| ≤ T i)
    (hcommon : ∀ h ∈ H, F.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ => 1) B (R h) + Z) ∈
        F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U))
    (hS : ∀ h ∈ H, F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T M (S h))
    (hR : ∀ h ∈ H, F.FirstCoefficientGrid e ω hF (fun _ => 1) l (R h)) :
    let Y := F.fastCoefficientDirectionCoordinates U b B
    let A := LinearMap.toMatrix b b (F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB).toLinearMap
    let scale := fun i => monomialScale T (rows i).val.1
    ∃ D : Finset (σ → ℤ), D.card = H.card ∧
      ∃ q : (σ → ℤ) → κ → ℝ, ∀ h ∈ D,
        q h ∈ realDenominatorGrid m ∧
        ‖derivativeGridPoint T scale Y A h (q h)‖ ≤ max 2 (C * (M + M)) := by
  dsimp only
  apply exists_derivative_difference_inputs T _ _ _ m H h₀ (max 2 (C * (M + M)))
  intro h hh
  obtain ⟨r, hr, _, hnorm⟩ := F.bounded_coefficient_derivative_point
    e ω hF U b rows B hB T hT C M M hC hM hM l m hslow hgrid
    h h₀ (hbox h hh) (hbox h₀ hh₀) (S h) (S h₀) (R h) (R h₀) Z
    (hcommon h hh) (hcommon h₀ hh₀) (hS h hh) (hS h₀ hh₀) (hR h hh) (hR h₀ hh₀)
  exact ⟨r, hr, hnorm⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix TensorProduct

set_option maxHeartbeats 400000 in
theorem common_coefficient_derivative_system
    {σ ι L : Type*} [Fintype σ] [DecidableEq σ] {d : ℕ}
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
    (b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule (fun _ : σ => 1) ⧸
      F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)))
    (rows : Fin d → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (hblock : ∀ i j, (rows j).val.1 ≠ i.val.1 →
      b.repr ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ
          (F.realFirstCoefficientBasis e ω hF (fun _ => 1) i)) j = 0)
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hB : (F.adaptedReducedRealSymbolHom (fun _ => 1) B).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) U))
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i) (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M) (l m : ℕ)
    (hslow : ∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (M + M) x → ∀ i,
      |b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) i| ≤
          C * (M + M) / monomialScale T (rows i).val.1)
    (hgrid : ∀ x, F.FirstCoefficientGrid e ω hF (fun _ => 1) l x →
      b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) ∈ realDenominatorGrid m)
    (H : Finset (σ → ℤ)) (h₀ : σ → ℤ) (hh₀ : h₀ ∈ H)
    (S R : (σ → ℤ) → F.RealFirstCoefficientModule (fun _ : σ => 1))
    (Z : F.RealFirstCoefficientModule (fun _ : σ => 1))
    (hbox : ∀ h ∈ H, ∀ i, |(h i : ℝ)| ≤ T i)
    (hcommon : ∀ h ∈ H, F.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ => 1) B (R h) + Z) ∈
        F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U))
    (hS : ∀ h ∈ H, F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T M (S h))
    (hR : ∀ h ∈ H, F.FirstCoefficientGrid e ω hF (fun _ => 1) l (R h))
    (haction : ∀ i j, ω (rows i).val.2 ≤ ω (rows j).val.2 →
      LinearMap.toMatrix b b
        (F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB).toLinearMap i j =
          (1 : Matrix (Fin d) (Fin d) ℝ) i j)
    (hm : 0 < m) (δ p : ℝ) (hδ : 0 < δ) (hp : 0 ≤ p)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (hdim : ((Fintype.card σ + Fintype.card (Fin d) : ℕ) : ℝ) ≤ p)
    (hmcap : (m : ℝ) ≤ Real.exp p) (hRcap : max 2 (C * (M + M)) ≤ Real.exp p)
    (hδcap : δ⁻¹ ≤ Real.exp p) (Tmin : ℝ)
    (hmin : Real.exp ((p + 2) ^ 3) < Tmin) (hside : ∀ i, Tmin ≤ T i) :
    ∃ (perm : Equiv.Perm (Fin d)) (a : ℕ) (ha : a ≤ d),
      (∀ i, i.val < a ↔ (rows (perm i)).val.1 = 0) ∧
      let b' := b.reindex perm.symm
      let f := F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB
      let A' := b'.equivFun.symm.trans (f.trans b'.equivFun)
      ∃ η : (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)),
      (∀ x, η (fun i => b'.equivFun x (Fin.castLE ha i)) =
        F.realFastCoefficientHorizontal (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U) x) ∧
      Nonempty (CoordinateDerivativeSystem ha T (F.fastCoefficientDirectionCoordinates U b' B) A'
        (fun i => monomialScale T (rows (perm i)).val.1) (Real.exp ((p + 2) ^ 3))) := by
  have hTpos : ∀ i, 0 < T i := fun i => lt_of_lt_of_le zero_lt_one (hT i)
  obtain ⟨D, hDcard, q, hq⟩ := F.bounded_coefficient_difference_inputs e ω hF U b rows
    B hB T hTpos C M hC hM l m hslow hgrid H h₀ hh₀ S R Z hbox hcommon hS hR
  let V := F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
    (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)
  let Y := V.mkQ.comp (F.realFirstCoefficientDirectionMap B.coord)
  let f := F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB
  have hDdense : δ * ∏ i, T i ≤ (D.card : ℝ) := by rw [hDcard]; exact hdense
  obtain ⟨perm, a, ha, hzero, hsystem⟩ :=
    firstCoefficient_coordinate_system ω rows b Y f haction T hT m hm
    (max 2 (C * (M + M))) δ
    ((by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)) hδ D q
    (fun h hh => (hq h hh).1) (fun h hh => (hq h hh).2) hDdense
    p hp hdim hmcap hRcap hδcap Tmin hmin hside
  have hblock' : ∀ i j, (rows (perm j)).val.1 ≠ i.val.1 →
      (b.reindex perm.symm).repr (V.mkQ
        (F.realFirstCoefficientBasis e ω hF (fun _ => 1) i)) j = 0 := by
    intro i j hij
    simpa only [Basis.repr_reindex_apply, Equiv.symm_symm] using hblock i (perm j) hij
  let η := F.realFastCoefficientHorizontalEquiv e ω hF (fun _ : σ => 1) (by simp)
    (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)
    (b.reindex perm.symm) (fun i => rows (perm i)) hblock' ha hzero
  refine ⟨perm, a, ha, hzero, η, ?_, hsystem⟩
  exact F.realFastCoefficientHorizontalEquiv_projection e ω hF (fun _ : σ => 1) (by simp)
    (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)
    (b.reindex perm.symm) (fun i => rows (perm i)) hblock' ha hzero

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped Matrix TensorProduct

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "Q" => (E ⧸ J)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf

def BoundedInitialStateFactorization (g₀ : G) (T : σ → ℝ) (rankBound : ℕ) (p : ℝ) : Prop :=
  ∃ k : ℕ, k ≤ rankBound ∧
    ∃ (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis (Fin k) ℚ K),
    ∃ Hk : ℕ, 1 ≤ Hk ∧ (Hk : ℝ) ≤ Real.exp p ∧
      (∀ i j, RationalHeightLE ((F.layerOneBasis e ω hF).repr (bK j).val i) Hk) ∧
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp p ∧
        ∃ x g z : G, x * g * z = g₀ ∧
          F.RealAdaptedCoefficientBound e ω hF (fun _ : σ => 1) T (Real.exp p) x.val.coord ∧
          F.RealAdaptedCoefficientGrid e ω hF (fun _ : σ => 1) m z.val.coord ∧
          ∃ X : F.associatedGradedFiltration.FormalInductionState (F.associatedGradedBasis e ω hF) ω
            (realificationLieSubalgebra (F.fullFastGradedDiagonal W))
            (F.fullFastGradedRelative e ω hF W) (F.gradedHorizontalKernel e ω hF K)
            (F.gradedHorizontalKernelBasis e ω hF K bK) T 2 p,
            X.P = F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val

def CommonInitialStateSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hd : (d : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (g₀ : G) (_hzero : coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g₀.val.coord) 0 = 0)
    (b : Basis (Fin d) ℝ Q) (rows : Fin d → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (sectionMap : (Fin d → ℝ) →ₗ[ℝ] E)
    (_hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y)
    (Cscale : ℝ) (_hC : 0 ≤ Cscale) (_hCp : Cscale ≤ Real.exp p)
    (_hweighted : ∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
      (∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M x → ∀ i,
        |b.equivFun ((J).mkQ x) i| ≤ Cscale * M / monomialScale T (rows i).val.1) ∧
      (∀ y, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T (Cscale * M) (sectionMap y)))
    (δ : ℕ) (_hδ : 0 < δ) (_hδp : (δ : ℝ) ≤ Real.exp p)
    (_hprojectionGrid : ∀ m x, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) m x →
      b.equivFun ((J).mkQ x) ∈ realDenominatorGrid (δ * m))
    (_hsectionGrid : ∀ m (y : Fin d → ℝ), y ∈ realDenominatorGrid m →
      F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) (δ * m) (sectionMap y))
    (_hblock : ∀ i j, (rows j).val.1 ≠ i.val.1 →
      b.repr ((J).mkQ (F.realFirstCoefficientBasis e ω hF (fun _ : σ => 1) i)) j = 0)
    (_haction : ∀ i j, ω (rows i).val.2 ≤ ω (rows j).val.2 →
      LinearMap.toMatrix b b (ρ g₀).toLinearMap i j = (1 : Matrix (Fin d) (Fin d) ℝ) i j)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (M : ℝ) (_hM : 0 ≤ M) (_hMp : M ≤ Real.exp p)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p)
    (Hshifts : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ Hshifts)
    (S R : (σ → ℤ) → E) (Z : E)
    (_hbox : ∀ h ∈ Hshifts, ∀ i, |(h i : ℝ)| ≤ T i)
    (_hcommon : ∀ h ∈ Hshifts, F.realFirstCoefficientDirectionMap g₀.val.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g₀.val (R h) + Z) ∈ J)
    (_hS : ∀ h ∈ Hshifts, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M (S h))
    (_hR : ∀ h ∈ Hshifts, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) l (R h))
    (density : ℝ) (_hdensity : 0 < density) (_hdensityp : density⁻¹ ≤ Real.exp p)
    (_hdense : density * ∏ i, T i ≤ (Hshifts.card : ℝ)),
    F.BoundedInitialStateFactorization e ω hF W g₀ T d ((p + C) ^ C)

theorem exists_initialFormalState_from_common (C D : ℕ)
    (hbudget : ∀ p : ℝ, 0 ≤ p →
      commonInitialParameter p + 1 ≤ (p + D) ^ D ∧
      (commonInitialParameter p + 2) ^ 3 ≤ (p + D) ^ D ∧
      (commonInitialParameter p + C) ^ C ≤ (p + D) ^ D)
    (hinit : ∀ a : ℕ, F.ExtractedInitialStateSpec (σ := σ) (τ := τ) (a := a) (d := d) e ω hF W C) :
    F.CommonInitialStateSpec (σ := σ) (τ := τ) (d := d) e ω hF W D := by
  intro H p hH hp hι hσ hτ hd hHp hstructure hW v hv hheight g₀ hzero
    b rows sectionMap hsection Cscale hC hCp hweighted δ hδ hδp hprojectionGrid hsectionGrid
    hblock haction T hT M hM hMp l hl hlp Hshifts h₀ hh₀ S R Z hbox hcommon hS hR
    density hdensity hdensityp hdense
  let q := commonExtractionParameter p
  let r := commonInitialParameter p
  have hcontrol := commonExtractionParameter_controls hp
  have hpq : p ≤ q := hcontrol.1
  have hqr : q ≤ r := hcontrol.2.2.2
  have hpr : p ≤ r := hpq.trans hqr
  have hq : 0 ≤ q := hp.trans hpq
  have hr : 0 ≤ r := hp.trans hpr
  have hepq := Real.exp_le_exp.mpr hpq
  have hepr := Real.exp_le_exp.mpr hpr
  have hb := hbudget p hp
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hTlarge (i : σ) : Real.exp (r + 1) ≤ T i :=
    (Real.exp_le_exp.mpr hb.1).trans (hT i)
  have hTone (i : σ) : 1 ≤ T i := (Real.one_le_exp (by linarith : 0 ≤ r + 1)).trans (hTlarge i)
  have hproducts := commonExtractionParameter_products hp hC hCp hM hMp δ l hδp hlp
  have hdim : ((Fintype.card σ + Fintype.card (Fin d) : ℕ) : ℝ) ≤ q := by
    rw [Nat.cast_add, Fintype.card_fin]
    calc
      _ ≤ p + p := add_le_add hσ hd
      _ ≤ q := by linarith [hcontrol.2.1]
  have hmin : Real.exp ((q + 2) ^ 3) < Real.exp (r + 1) :=
    Real.exp_lt_exp.mpr (by change r < r + 1; linarith)
  have hextract := F.common_coefficient_derivative_system e ω hF Wf b rows hblock
    g₀.val g₀.property T hTone Cscale M hC hM l (δ * l)
    ((hweighted T hTpos (M + M) (add_nonneg hM hM)).1)
    (hprojectionGrid l) Hshifts h₀ hh₀ S R Z hbox hcommon hS hR haction
    (Nat.mul_pos hδ hl) density q hdensity hq hdense hdim hproducts.2 hproducts.1
    (hdensityp.trans hepq) (Real.exp (r + 1)) hmin hTlarge
  obtain ⟨perm, a, ha, _, η, hη, ⟨sys⟩⟩ := hextract
  have hsection' := F.exists_reindexed_fast_coefficient_section e ω hF
    (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf b rows sectionMap hsection δ Cscale
    hprojectionGrid hsectionGrid hweighted perm
  obtain ⟨sectionMap', hright', hproj', hgrid', hweighted'⟩ := hsection'
  have har : (a : ℝ) ≤ r := (Nat.cast_le.mpr ha).trans (hd.trans hpr)
  have hTr (i : σ) : Real.exp ((r + C) ^ C) ≤ T i :=
    (Real.exp_le_exp.mpr hb.2.2).trans (hT i)
  have hout := hinit a H r hH hr (hι.trans hpr) (hσ.trans hpr) (hτ.trans hpr) har
    (hHp.trans hepr) hstructure hW v hv hheight g₀ hzero (b.reindex perm.symm)
    (fun i => rows (perm i)) ha η hη sectionMap' hright' Cscale hC (hCp.trans hepr)
    hweighted' δ hδ (hδp.trans hepr) hproj' hgrid' T hTr
    (Real.exp r) (Real.exp_nonneg _) le_rfl sys
  obtain ⟨hk, K, bK, Hk, hHk, hHkp, hKheight, m, hm, hmp, x, g, z, hfactor, hx, hz, X, hX⟩ := hout
  refine ⟨sys.k, hk.trans ha, K, bK, Hk, hHk,
    hHkp.trans (Real.exp_le_exp.mpr hb.2.1), hKheight, m, hm,
    hmp.trans (Real.exp_le_exp.mpr hb.2.2), x, g, z, hfactor, ?_, hz,
    X.enlarge hb.2.2 hTpos, hX⟩
  exact F.realAdaptedCoefficientBound_mono e ω hF (fun _ => 1) T hTpos
    (Real.exp_le_exp.mpr hb.2.2) x.val.coord hx

theorem exists_common_initialState_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
        [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) (d : ℕ),
        F.CommonInitialStateSpec (σ := σ) (τ := τ) (d := d) e ω hF W C := by
  have h := exists_extracted_initialState_bound.{uσ, uι, uτ, uL} s
  obtain ⟨C, _, hinit⟩ := h
  obtain ⟨D, hD, hbudget⟩ := exists_commonInitialParameter_budget C
  refine ⟨D, hD, ?_⟩
  intro σ ι τ L _ _ _ _ _ _ F e ω hF W d
  exact F.exists_initialFormalState_from_common e ω hF W C D hbudget
    (fun a => hinit F e ω hF W a d)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf

omit [Fintype σ] [DecidableEq σ] [Fintype ι] in
theorem BoundedInitialStateFactorization.mono
    {g₀ : G} {T : σ → ℝ} {d d' : ℕ} {p q : ℝ}
    (h : F.BoundedInitialStateFactorization e ω hF W g₀ T d p)
    (hd : d ≤ d') (hpq : p ≤ q) (hT : ∀ i, 0 < T i) :
    F.BoundedInitialStateFactorization e ω hF W g₀ T d' q := by
  obtain ⟨k, hk, K, bK, Hk, hHk, hHkp, hKb, m, hm, hmp, x, g, z, hfactor, hx, hz, X, hX⟩ := h
  have hepq := Real.exp_le_exp.mpr hpq
  refine ⟨k, hk.trans hd, K, bK, Hk, hHk, hHkp.trans hepq, hKb, m, hm, hmp.trans hepq,
    x, g, z, hfactor, ?_, hz, X.enlarge hpq hT, hX⟩
  exact F.realAdaptedCoefficientBound_mono e ω hF (fun _ => 1) T hT hepq x.val.coord hx

def FullInitialStateSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (g₀ : G) (_hzero : coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g₀.val.coord) 0 = 0)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (M : ℝ) (_hM : 0 ≤ M) (_hMp : M ≤ Real.exp p)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p)
    (Hshifts : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ Hshifts)
    (S R : (σ → ℤ) → E) (Z : E)
    (_hbox : ∀ h ∈ Hshifts, ∀ i, |(h i : ℝ)| ≤ T i)
    (_hcommon : ∀ h ∈ Hshifts, F.realFirstCoefficientDirectionMap g₀.val.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g₀.val (R h) + Z) ∈ J)
    (_hS : ∀ h ∈ Hshifts, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M (S h))
    (_hR : ∀ h ∈ Hshifts, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) l (R h))
    (density : ℝ) (_hdensity : 0 < density) (_hdensityp : density⁻¹ ≤ Real.exp p)
    (_hdense : density * ∏ i, T i ≤ (Hshifts.card : ℝ)),
    F.BoundedInitialStateFactorization e ω hF W g₀ T
      (Fintype.card ι * (s + 2) * (Fintype.card σ + 1) ^ (s + 1)) ((p + C) ^ C)

omit [DecidableEq σ] in
theorem exists_initialFormalState_from_common_family (c C D : ℕ)
    (hcoords : FullFastCoefficientCoordinateSpec.{uσ, uι, uτ, uL} s c)
    (hcommonState : ∀ d : ℕ,
      F.CommonInitialStateSpec (σ := σ) (τ := τ) (d := d) e ω hF W C)
    (hbudget : ∀ p : ℝ, 0 ≤ p → (fullInitialParameter s c p + C) ^ C ≤ (p + D) ^ D) :
    F.FullInitialStateSpec (σ := σ) (τ := τ) e ω hF W D := by
  intro H p hH hp hι hσ hτ hHp hstructure hW v hv hheight g₀ hzero T hT
    M hM hMp l hl hlp Hshifts h₀ hh₀ S R Z hbox hcommon hS hR density hdensity hdensityp hdense
  have hcoordinateData := hcoords F e ω hF (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    W hW v hv hH hheight hp hι hσ hτ hHp
  obtain ⟨d, hd, rows, _, b, sectionMap, δ, hδ, hδp, hproj, hgrid, hright,
    hweighted, hblock, haction⟩ := hcoordinateData
  let q := fullInitialParameter s c p
  have hcontrol := fullInitialParameter_controls s c hp
  have hpq : p ≤ q := hcontrol.1
  have hq : 0 ≤ q := hp.trans hpq
  have hepq := Real.exp_le_exp.mpr hpq
  have hcoordinateBound : Real.exp ((p + c) ^ c) ≤ Real.exp q :=
    Real.exp_le_exp.mpr hcontrol.2.2
  have hdim : (d : ℝ) ≤ q := by
    have hd' : (d : ℝ) ≤
        (Fintype.card ι : ℝ) * (s + 2) * ((Fintype.card σ : ℝ) + 1) ^ (s + 1) := by
      exact_mod_cast hd
    apply hd'.trans
    apply le_trans _ hcontrol.2.1
    gcongr
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hTq (i : σ) : Real.exp ((q + C) ^ C) ≤ T i :=
    (Real.exp_le_exp.mpr (hbudget p hp)).trans (hT i)
  have hout := hcommonState d H q hH hq (hι.trans hpq) (hσ.trans hpq) (hτ.trans hpq) hdim
    (hHp.trans hepq) hstructure hW v hv hheight g₀ hzero b rows sectionMap hright
    (Real.exp ((p + c) ^ c)) (Real.exp_nonneg _) hcoordinateBound hweighted
    δ hδ (hδp.trans hcoordinateBound) hproj hgrid hblock (haction g₀.val g₀.property)
    T hTq M hM (hMp.trans hepq) l hl (hlp.trans hepq) Hshifts h₀ hh₀ S R Z
    hbox hcommon hS hR density hdensity (hdensityp.trans hepq) hdense
  exact hout.mono F e ω hF W hd (hbudget p hp) hTpos

theorem exists_full_initialState_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
        [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded),
        F.FullInitialStateSpec (σ := σ) (τ := τ) e ω hF W C := by
  have h₁ := exists_fullFast_coefficient_coordinate_bound.{uσ, uι, uτ, uL} s
  obtain ⟨c, _, hcoords⟩ := h₁
  have h₂ := exists_common_initialState_bound.{uσ, uι, uτ, uL} s
  obtain ⟨C, _, hcommonState⟩ := h₂
  obtain ⟨D, hD, hbudget⟩ := exists_fullInitialParameter_budget s c C
  refine ⟨D, hD, ?_⟩
  intro σ ι τ L _ _ _ _ _ _ F e ω hF W
  exact F.exists_initialFormalState_from_common_family e ω hF W c C D hcoords
    (hcommonState F e ω hF W) hbudget

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) (F.fastPointwiseSquare e ω hF (fun _ => 1) W)

def NormalizedTerminalFactorization (g₀ : G) (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (T : σ → ℝ) (p : ℝ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp p ∧
    ∃ x g z : G, x * g * z = g₀ ∧
      F.RealAdaptedCoefficientBound e ω hF (fun _ : σ => 1) T (Real.exp p) x.val.coord ∧
      F.RealAdaptedCoefficientGrid e ω hF (fun _ : σ => 1) m z.val.coord ∧
      F.FastTerminalFactorization e ω hF W η T
        (F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val) p

omit [Fintype σ] [Fintype ι] in
theorem NormalizedTerminalFactorization.mono
    {g₀ : G} {η : F.AssociatedGraded →ₗ[ℚ] ℚ} {T : σ → ℝ} {p q : ℝ}
    (h : F.NormalizedTerminalFactorization e ω hF W g₀ η T p)
    (hpq : p ≤ q) (hT : ∀ i, 0 < T i) :
    F.NormalizedTerminalFactorization e ω hF W g₀ η T q := by
  obtain ⟨m, hm, hmp, x, g, z, hfactor, hx, hz, hterminal⟩ := h
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hpq), x, g, z, hfactor, ?_, hz,
    hterminal.mono F e ω hF W hpq hT⟩
  exact F.realAdaptedCoefficientBound_mono e ω hF (fun _ => 1) T hT
    (Real.exp_le_exp.mpr hpq) x.val.coord hx

def NormalizedTerminalStateSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p) (_hs : 1 ≤ s)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hsp : (s + 1 : ℕ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (_hη : ∀ x ∈ F.fullFastGradedRelative e ω hF W,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω (s + 1) x = x → η x = 0)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (g₀ : G) (d : ℕ) (_hd : (d : ℝ) ≤ p)
    (_hinitial : F.BoundedInitialStateFactorization e ω hF W g₀ T d p),
    F.NormalizedTerminalFactorization e ω hF W g₀ η T ((p + C) ^ C)

theorem exists_normalized_terminalState_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
        [Fintype σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded),
        F.NormalizedTerminalStateSpec (σ := σ) (τ := τ) e ω hF W C := by
  have h := exists_fast_terminalState_bound.{uσ, uι, uτ, uL} s
  obtain ⟨C, hC, hterminal⟩ := h
  refine ⟨C, hC, ?_⟩
  intro σ ι τ L _ _ _ _ _ F e ω hF W H p hH hp hs hι hσ hτ hsp hHp hstructure
    hW v hv hheight η hη T hT g₀ d hd hinitial
  obtain ⟨k, hk, K, bK, Hk, _, hHkp, hKb, m, hm, hmp, x, g, z, hfactor, hx, hz, X, hX⟩ := hinitial
  have hcommon : ((max H Hk : ℕ) : ℝ) ≤ Real.exp p := by
    rw [Nat.cast_max]
    exact max_le hHp hHkp
  have hkr : (k : ℝ) ≤ p := (Nat.cast_le.mpr hk).trans hd
  have hout := hterminal F e ω hF W (max H Hk) p (hH.trans (le_max_left _ _)) hp hs
    hι hσ hτ hsp hcommon (fun i j k => (hstructure i j k).mono (le_max_left _ _))
    hW v hv (fun j i => (hheight j i).mono (le_max_left _ _)) k hkr K bK
    (fun i j => (hKb i j).mono (le_max_right _ _)) η hη T hT X
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hpC : p ≤ (p + C) ^ C := by
    have hCr : (2 : ℝ) ≤ C := Nat.cast_le.mpr hC
    calc
      p ≤ p + C := le_add_of_nonneg_right (Nat.cast_nonneg C)
      _ ≤ (p + C) ^ C := by
        simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + C)
          (show 1 ≤ C by omega)
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hpC), x, g, z, hfactor, ?_, hz, ?_⟩
  · exact F.realAdaptedCoefficientBound_mono e ω hF (fun _ => 1) T hTpos
      (Real.exp_le_exp.mpr hpC) x.val.coord hx
  · exact (congrArg (fun P => F.FastTerminalFactorization e ω hF W η T P ((p + C) ^ C)) hX).mp hout

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf

def CommonTerminalStateSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p) (_hs : 1 ≤ s)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (_hη : ∀ x ∈ F.fullFastGradedRelative e ω hF W,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω (s + 1) x = x → η x = 0)
    (g₀ : G) (_hzero : coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g₀.val.coord) 0 = 0)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (M : ℝ) (_hM : 0 ≤ M) (_hMp : M ≤ Real.exp p)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p)
    (Hshifts : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ Hshifts)
    (S R : (σ → ℤ) → E) (Z : E)
    (_hbox : ∀ h ∈ Hshifts, ∀ i, |(h i : ℝ)| ≤ T i)
    (_hcommon : ∀ h ∈ Hshifts, F.realFirstCoefficientDirectionMap g₀.val.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g₀.val (R h) + Z) ∈ J)
    (_hS : ∀ h ∈ Hshifts, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M (S h))
    (_hR : ∀ h ∈ Hshifts, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) l (R h))
    (density : ℝ) (_hdensity : 0 < density) (_hdensityp : density⁻¹ ≤ Real.exp p)
    (_hdense : density * ∏ i, T i ≤ (Hshifts.card : ℝ)),
    F.NormalizedTerminalFactorization e ω hF W g₀ η T ((p + C) ^ C)

theorem exists_common_terminalState_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
        [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded),
        F.CommonTerminalStateSpec (σ := σ) (τ := τ) e ω hF W C := by
  have h₁ := exists_full_initialState_bound.{uσ, uι, uτ, uL} s
  obtain ⟨c, _, hinit⟩ := h₁
  have h₂ := exists_normalized_terminalState_bound.{uσ, uι, uτ, uL} s
  obtain ⟨C, _, hterminal⟩ := h₂
  obtain ⟨D, hD, hbudget⟩ := exists_commonTerminalParameter_budget s c C
  refine ⟨D, hD, ?_⟩
  intro σ ι τ L _ _ _ _ _ _ F e ω hF W H p hH hp hs hι hσ hτ hHp hstructure
    hW v hv hheight η hη g₀ hzero T hT
    M hM hMp l hl hlp Hshifts h₀ hh₀ S R Z hbox hcommon hS hR density hdensity hdensityp hdense
  let q := commonTerminalParameter s c p
  have hcontrol := commonTerminalParameter_controls s c hp
  have hpq : p ≤ q := hcontrol.1
  have hq : 0 ≤ q := hp.trans hpq
  have hp₀q : (p + c) ^ c ≤ q := hcontrol.2.2.1
  have hqfinal : q ≤ (p + D) ^ D := (hbudget p hp).1
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hTinitial (i : σ) : Real.exp ((p + c) ^ c) ≤ T i :=
    (Real.exp_le_exp.mpr (hp₀q.trans hqfinal)).trans (hT i)
  have hi := hinit F e ω hF W H p hH hp hι hσ hτ hHp hstructure hW v hv hheight g₀ hzero
    T hTinitial M hM hMp l hl hlp Hshifts h₀ hh₀ S R Z hbox hcommon hS hR density hdensity hdensityp hdense
  have hiq := hi.mono F e ω hF W le_rfl hp₀q hTpos
  have hd : ((Fintype.card ι * (s + 2) * (Fintype.card σ + 1) ^ (s + 1) : ℕ) : ℝ) ≤ q := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    apply le_trans _ hcontrol.2.1
    gcongr
  have hTterminal (i : σ) : Real.exp ((q + C) ^ C) ≤ T i :=
    (Real.exp_le_exp.mpr (hbudget p hp).2).trans (hT i)
  have hout := hterminal F e ω hF W H q hH hq hs (hι.trans hpq) (hσ.trans hpq) (hτ.trans hpq)
    hcontrol.2.2.2 (hHp.trans (Real.exp_le_exp.mpr hpq)) hstructure hW v hv hheight
    η hη T hTterminal g₀ _ hd hiq
  exact hout.mono F e ω hF W (hbudget p hp).2 hTpos

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup

universe uσ uι uL

variable {σ : Type uσ} {ι : Type uι} {L : Type uL}
  [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) (F.fastPointwiseSquare e ω hF (fun _ => 1) W)

def TerminalCompositionSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ) (T : σ → ℝ) (_hT : ∀ i, 0 < T i) (g₀ : G),
    F.NormalizedTerminalFactorization e ω hF W g₀ η T p →
    F.FastTerminalFactorization e ω hF W η T
      (F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g₀.val) ((p + C) ^ C)

theorem exists_terminalComposition_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {L : Type uL}
        [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded),
        F.TerminalCompositionSpec (σ := σ) e ω hF W C := by
  have hs := exists_formal_polynomial_product_bound.{uσ, uι, uL} (s + 1) 1 2
  obtain ⟨a, _, hslow⟩ := hs
  have hr := exists_formal_polynomial_product_grid.{uσ, uι, uL} (s + 1) 2
  obtain ⟨b, _, hgrid⟩ := hr
  obtain ⟨C, hC, hbudget⟩ := exists_terminalComposition_budget a b
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F e ω hF W H p hH hp hι hσ hHp hstructure hW η T hT g₀ hn
  obtain ⟨l, hl, hlp, x, g, z, hnative, hx, hz, hterminal⟩ := hn
  obtain ⟨Z, hZ, hZη, bZ, hbZ, A, P, B, hformal, hA, hB, hzero, hdegree, hcoeff,
    hAbound, m, hm, hmp, hBgrid⟩ := hterminal
  let φ := F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1)
  let bG := F.associatedGradedBasis e ω hF
  let FG := F.associatedGradedFiltration
  have hgraded := F.associatedGradedBasis_homogeneous_brackets e ω hF
  have hlayers := F.associatedGradedFiltration_layer e ω hF
  have hstructureG (i j k : ι) : RationalHeightLE (bG.repr ⁅bG i, bG j⁆ k) H := by
    rw [F.associatedGradedBasis_bracket e ω hF]
    split_ifs
    · exact hstructure i j k
    · exact rationalHeightLE_zero hH
  have h2p : 0 ≤ 2 * p := by positivity
  have hp2 : p ≤ 2 * p := by linarith
  have hι2 := hι.trans hp2
  have hσ2 := hσ.trans hp2
  have hH2 := hHp.trans (Real.exp_le_exp.mpr hp2)
  have hxb := F.realAdaptedGradedPolynomialHom_bound e ω hF (fun _ : σ => 1) T hT
    (Real.exp_nonneg p) x.val hx
  have hzg := F.realAdaptedGradedPolynomialHom_grid e ω hF (fun _ : σ => 1) l z.val hz
  have hxc := F.realAdaptedGradedPolynomialHom_correction e ω hF W hW x
  have hzc := F.realAdaptedGradedPolynomialHom_correction e ω hF W hW z
  have hinput : Real.exp p ≤ Real.exp ((2 * p + 2) ^ 1) :=
    Real.exp_le_exp.mpr (by rw [pow_one]; linarith)
  have hleft := hslow FG bG ω hlayers H (2 * p) hH h2p hι2 hσ2 hH2 hstructureG T hT
    [φ x.val, A] (by simp) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact FG.gradedPolynomial_mem_adapted bG ω hlayers (fun _ => 1) _ hxc.2.1
      · exact FG.gradedPolynomial_mem_adapted bG ω hlayers (fun _ => 1) _ hA.2.1) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hxb.mono _ T hT hinput
      · exact hAbound.mono _ T hT hinput)
  have hleftBound : CoefficientBound (bG.baseChange ℝ) T (Real.exp ((2 * p + a) ^ a))
      (φ x.val * A).coord := by
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hleft
  have hdenom : ((l * m : ℕ) : ℝ) ≤ Real.exp (2 * p) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hlp hmp (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
  have hcommonB : CoefficientGrid (bG.baseChange ℝ) (l * m) B.coord :=
    fun α => realDenominatorGrid_subset_of_dvd hm (dvd_mul_left m l) (hBgrid α)
  have hcommonz : CoefficientGrid (bG.baseChange ℝ) (l * m) (φ z.val).coord :=
    fun α => realDenominatorGrid_subset_of_dvd hl (dvd_mul_right l m) (hzg α)
  have hg := hgrid FG bG ω hlayers H (2 * p) hH h2p hι2 hσ2 hH2 hstructureG
    (l * m) (Nat.mul_pos hl hm) hdenom
  obtain ⟨n, hn, hnp, _, hproducts⟩ := hg
  have hright := hproducts [B, φ z.val] (by simp) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact FG.gradedPolynomial_mem_adapted bG ω hlayers (fun _ => 1) _ hB.2.1
    · exact FG.gradedPolynomial_mem_adapted bG ω hlayers (fun _ => 1) _ hzc.2.1) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hcommonB
    · exact hcommonz)
  have hrightGrid : CoefficientGrid (bG.baseChange ℝ) n (B * φ z.val).coord := by
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hright
  have hnative' : φ x.val * φ g.val * φ z.val = φ g₀.val := by
    calc
      _ = φ (x.val * g.val * z.val) := by simp only [map_mul]
      _ = φ g₀.val := congrArg φ (congrArg Subtype.val hnative)
  have hfactor : (φ x.val * A) * P * (B * φ z.val) = φ g₀.val := by
    calc
      _ = φ x.val * (A * P * B) * φ z.val := by group
      _ = φ x.val * φ g.val * φ z.val := congrArg (fun t => φ x.val * t * φ z.val) hformal
      _ = _ := hnative'
  have hb := hbudget p hp
  have hep := Real.exp_le_exp.mpr hb.1
  exact ⟨Z, hZ, hZη, bZ, fun i j => ⟨(hbZ i j).1.trans hep, (hbZ i j).2.trans hep⟩,
    φ x.val * A, P, B * φ z.val, hfactor, hxc.mul hgraded hA, hB.mul hgraded hzc,
    hzero, hdegree, hcoeff, hleftBound.mono _ T hT (Real.exp_le_exp.mpr hb.2.1),
    n, hn, hnp.trans (Real.exp_le_exp.mpr hb.2.2), hrightGrid⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf

def CommonFactorizationSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p) (_hs : 1 ≤ s)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (_hη : ∀ x ∈ F.fullFastGradedRelative e ω hF W,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω (s + 1) x = x → η x = 0)
    (g₀ : G) (_hzero : coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g₀.val.coord) 0 = 0)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (M : ℝ) (_hM : 0 ≤ M) (_hMp : M ≤ Real.exp p)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p)
    (Hshifts : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ Hshifts)
    (S R : (σ → ℤ) → E) (Z : E)
    (_hbox : ∀ h ∈ Hshifts, ∀ i, |(h i : ℝ)| ≤ T i)
    (_hcommon : ∀ h ∈ Hshifts, F.realFirstCoefficientDirectionMap g₀.val.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g₀.val (R h) + Z) ∈ J)
    (_hS : ∀ h ∈ Hshifts, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M (S h))
    (_hR : ∀ h ∈ Hshifts, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) l (R h))
    (density : ℝ) (_hdensity : 0 < density) (_hdensityp : density⁻¹ ≤ Real.exp p)
    (_hdense : density * ∏ i, T i ≤ (Hshifts.card : ℝ)),
    F.FastTerminalFactorization e ω hF W η T
      (F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g₀.val) ((p + C) ^ C)

theorem exists_commonFactorization_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
        [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded),
        F.CommonFactorizationSpec (σ := σ) (τ := τ) e ω hF W C := by
  have h₁ := exists_common_terminalState_bound.{uσ, uι, uτ, uL} s
  obtain ⟨c, _, hcommon⟩ := h₁
  have h₂ := exists_terminalComposition_bound.{uσ, uι, uL} s
  obtain ⟨C, _, hcompose⟩ := h₂
  obtain ⟨D, hD, hbudget⟩ := exists_commonTerminalParameter_budget s c C
  refine ⟨D, hD, ?_⟩
  intro σ ι τ L _ _ _ _ _ _ F e ω hF W H p hH hp hs hι hσ hτ hHp hstructure
    hW v hv hheight η hη g₀ hzero T hT M hM hMp l hl hlp Hshifts h₀ hh₀ S R Z
    hbox hcommonIdentity hS hR density hdensity hdensityp hdense
  let q := commonTerminalParameter s c p
  have hcontrol := commonTerminalParameter_controls s c hp
  have hpq : p ≤ q := hcontrol.1
  have hq : 0 ≤ q := hp.trans hpq
  have hp₀q : (p + c) ^ c ≤ q := hcontrol.2.2.1
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hTcommon (i : σ) : Real.exp ((p + c) ^ c) ≤ T i :=
    (Real.exp_le_exp.mpr (hp₀q.trans (hbudget p hp).1)).trans (hT i)
  have hn := hcommon F e ω hF W H p hH hp hs hι hσ hτ hHp hstructure hW v hv hheight
    η hη g₀ hzero T hTcommon M hM hMp l hl hlp Hshifts h₀ hh₀ S R Z hbox hcommonIdentity
    hS hR density hdensity hdensityp hdense
  have hnq := hn.mono F e ω hF W hp₀q hTpos
  have hout := hcompose F e ω hF W H q hH hq (hι.trans hpq) (hσ.trans hpq)
    (hHp.trans (Real.exp_le_exp.mpr hpq)) hstructure hW η T hTpos g₀ hnq
  exact hout.mono F e ω hF W (hbudget p hp).2 hTpos

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf

def CommonSymbolFactorizationSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p) (_hs : 1 ≤ s)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (_hη : ∀ x ∈ F.fullFastGradedRelative e ω hF W,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω (s + 1) x = x → η x = 0)
    (g₀ : G) (_hzero : coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g₀.val.coord) 0 = 0)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (M : ℝ) (_hM : 0 ≤ M) (_hMp : M ≤ Real.exp p)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p)
    (Hshifts : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ Hshifts)
    (S R : (σ → ℤ) → E) (Z : E)
    (_hbox : ∀ h ∈ Hshifts, ∀ i, |(h i : ℝ)| ≤ T i)
    (_hcommon : ∀ h ∈ Hshifts, F.realFirstCoefficientDirectionMap g₀.val.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g₀.val (R h) + Z) ∈ J)
    (_hS : ∀ h ∈ Hshifts, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M (S h))
    (_hR : ∀ h ∈ Hshifts, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) l (R h))
    (density : ℝ) (_hdensity : 0 < density) (_hdensityp : density⁻¹ ≤ Real.exp p)
    (_hdense : density * ∏ i, T i ≤ (Hshifts.card : ℝ)),
    F.SymbolTerminalFactorization e ω hF W η T
      (F.realPolynomialSymbolHom e ω hF (fun _ : σ => 1)
        (F.realAdaptedPolynomialGroupHom (fun _ : σ => 1) g₀.val)) ((p + C) ^ C)

theorem exists_common_symbolFactorization_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
        [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded),
        F.CommonSymbolFactorizationSpec (σ := σ) (τ := τ) e ω hF W C := by
  have h := exists_commonFactorization_bound.{uσ, uι, uτ, uL} s
  obtain ⟨C, hC, hfactor⟩ := h
  refine ⟨C, hC, ?_⟩
  intro σ ι τ L _ _ _ _ _ _ F e ω hF W H p hH hp hs hι hσ hτ hHp hstructure
    hW v hv hheight η hη g₀ hzero T hT M hM hMp l hl hlp Hshifts h₀ hh₀ S R Z
    hbox hcommon hS hR density hdensity hdensityp hdense
  apply F.symbolTerminalFactorization_of_native e ω hF W η T g₀.val ((p + C) ^ C)
  exact hfactor F e ω hF W H p hH hp hs hι hσ hτ hHp hstructure hW v hv hheight η hη g₀ hzero
    T hT M hM hMp l hl hlp Hshifts h₀ hh₀ S R Z hbox hcommon hS hR density hdensity hdensityp hdense

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf

def UnnormalizedCommonSymbolFactorizationSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p) (_hs : 1 ≤ s)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (_hη : ∀ x ∈ F.fullFastGradedRelative e ω hF W,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω (s + 1) x = x → η x = 0)
    (g₀ : G)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (M : ℝ) (_hM : 0 ≤ M) (_hMp : M ≤ Real.exp p)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p)
    (Hshifts : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ Hshifts)
    (S R : (σ → ℤ) → E) (Z : E)
    (_hbox : ∀ h ∈ Hshifts, ∀ i, |(h i : ℝ)| ≤ T i)
    (_hcommon : ∀ h ∈ Hshifts, F.realFirstCoefficientDirectionMap g₀.val.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g₀.val (R h) + Z) ∈ J)
    (_hS : ∀ h ∈ Hshifts, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M (S h))
    (_hR : ∀ h ∈ Hshifts, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) l (R h))
    (density : ℝ) (_hdensity : 0 < density) (_hdensityp : density⁻¹ ≤ Real.exp p)
    (_hdense : density * ∏ i, T i ≤ (Hshifts.card : ℝ)),
    F.SymbolTerminalFactorization e ω hF W η T
      (F.realPolynomialSymbolHom e ω hF (fun _ : σ => 1)
        (F.realAdaptedPolynomialGroupHom (fun _ : σ => 1) g₀.val)) ((p + C) ^ C)

theorem exists_unnormalized_common_symbolFactorization_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
        [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded),
        F.UnnormalizedCommonSymbolFactorizationSpec (σ := σ) (τ := τ) e ω hF W C := by
  obtain ⟨C, hC, hfactor⟩ := exists_common_symbolFactorization_bound.{uσ, uι, uτ, uL} s
  refine ⟨C, hC, ?_⟩
  intro σ ι τ L _ _ _ _ _ _ F e ω hF W H p hH hp hs hι hσ hτ hHp hstructure
    hW v hv hheight η hη g₀ T hT M hM hMp l hl hlp Hshifts h₀ hh₀ S R Z
    hbox hcommon hS hR density hdensity hdensityp hdense
  let g := F.nativeSymbolNormalize e ω hF (fun _ : σ => 1) g₀.val
  have hsymbol : F.realExtendedSymbolMap (fun _ => 1) g.coord =
      F.realExtendedSymbolMap (fun _ => 1) g₀.val.coord :=
    F.nativeSymbolNormalize_symbol e ω hF (fun _ => 1) g₀.val
  have hprojection : F.adaptedReducedRealSymbolHom (fun _ => 1) g =
      F.adaptedReducedRealSymbolHom (fun _ => 1) g₀.val := by
    apply NilpotentLieBCHGroup.ext
    rw [F.adaptedReducedRealSymbolHom_coord, F.adaptedReducedRealSymbolHom_coord, hsymbol]
  have hfast : g ∈ F.realFastDiagonalSubgroup (fun _ => 1)
      (F.fastPointwiseSquare e ω hF (fun _ => 1) W) := by
    rw [F.mem_realFastDiagonalSubgroup, hprojection]
    exact g₀.property
  let g' : F.realFastDiagonalSubgroup (fun _ : σ => 1)
      (F.fastPointwiseSquare e ω hF (fun _ => 1) W) := ⟨g, hfast⟩
  have hzero : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) g'.val.coord) 0 = 0 :=
    F.nativeSymbolNormalize_constant e ω hF (fun _ => 1) g₀.val
  have hdir := F.realFirstCoefficientDirectionMap_eq_of_symbol_eq e ω hF g g₀.val hsymbol
  have hadj := F.realFirstCoefficientAdjoint_eq_of_symbol_eq e ω hF (fun _ => 1) g g₀.val hsymbol
  have hcommon' : ∀ h ∈ Hshifts,
      F.realFirstCoefficientDirectionMap g'.val.coord (fun i => (h i : ℝ)) -
        (S h + F.realFirstCoefficientAdjoint (fun _ => 1) g'.val (R h) + Z) ∈
      F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1)
          (F.fastPointwiseSquare e ω hF (fun _ => 1) W)) := by
    intro h hh
    change F.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ => 1) g (R h) + Z) ∈ _
    rw [hdir, hadj]
    exact hcommon h hh
  have hout := hfactor F e ω hF W H p hH hp hs hι hσ hτ hHp hstructure
    hW v hv hheight η hη g' hzero T hT M hM hMp l hl hlp Hshifts h₀ hh₀ S R Z
    hbox hcommon' hS hR density hdensity hdensityp hdense
  have heq : F.realPolynomialSymbolHom e ω hF (fun _ => 1)
      (F.realAdaptedPolynomialGroupHom (fun _ => 1) g'.val) =
      F.realPolynomialSymbolHom e ω hF (fun _ => 1)
        (F.realAdaptedPolynomialGroupHom (fun _ => 1) g₀.val) := by
    apply NilpotentLieBCHGroup.ext
    rw [F.realPolynomialSymbolHom_groupHom_coord, F.realPolynomialSymbolHom_groupHom_coord]
    exact hsymbol
  rw [heq] at hout
  exact hout

end Erdos3.NilpotentLieFiltration

end

end OAI
