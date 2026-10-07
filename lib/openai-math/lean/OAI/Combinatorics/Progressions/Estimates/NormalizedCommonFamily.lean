import OAI.Combinatorics.Progressions.Dynamics.SynchronizedCorrectionBudget
import OAI.Combinatorics.Progressions.Polynomial.RealReducedSquarePolynomial

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

universe uσ uι uL

def CoefficientCorrectionSpec (s C : ℕ) : Prop :=
  ∀ {σ : Type uσ} {ι : Type uι} {L : Type uL}
    [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p),
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
      ∀ (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
        (A D : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
        (_hA : F.RealAdaptedCoefficientBound e ω hF (fun _ => 1) T (Real.exp p) A.coord)
        (_hD : F.RealAdaptedCoefficientGrid e ω hF (fun _ => 1) l D.coord)
        (h : σ → ℤ) (_hh : ∀ i, |(h i : ℝ)| ≤ T i)
        (ε u μ v : F.RealFirstCoefficientModule (fun _ : σ => 1))
        (_hε : F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (Real.exp p) ε)
        (_hu : F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (Real.exp p) u)
        (_hμ : F.FirstCoefficientGrid e ω hF (fun _ => 1) l μ)
        (_hv : F.FirstCoefficientGrid e ω hF (fun _ => 1) l v),
        F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (Real.exp ((p + C) ^ C))
          (F.coefficientSlowCorrection A (fun i => (h i : ℝ)) ε u) ∧
        F.FirstCoefficientGrid e ω hF (fun _ => 1) m
          (F.coefficientGridCorrection D (fun i => (h i : ℝ)) μ v)

theorem exists_coefficient_correction_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CoefficientCorrectionSpec.{uσ, uι, uL} s C := by
  obtain ⟨a, _, hadjoint⟩ := exists_firstCoefficient_adjoint_bound.{uσ, uι, uL} (s + 1) 1
  obtain ⟨d, _, hderivative⟩ := exists_firstCoefficient_direction_bound.{uσ, uι, uL} (s + 1) 1
  obtain ⟨r, _, hgrid⟩ := exists_firstCoefficient_operation_grid.{uσ, uι, uL} (s + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_synchronizedCorrection_budget a d r
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F e ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  have hgrids := hgrid F e ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  obtain ⟨m, hm, hmp, hlm, hAdjointGrid, hDerivativeGrid⟩ := hgrids
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr (hbudget p hp).2), hlm, ?_⟩
  intro T hT A D hA hD h hh ε u μ v hε hu hμ hv
  have hinput : Real.exp p ≤ Real.exp ((p + 2) ^ 1) :=
    Real.exp_le_exp.mpr (by rw [pow_one]; linarith)
  have hA' := F.realAdaptedCoefficientBound_mono e ω hF (fun _ => 1) T hT hinput A.coord hA
  have hAi : F.RealAdaptedCoefficientBound e ω hF (fun _ : σ => 1) T (Real.exp ((p + 2) ^ 1)) A⁻¹.coord := by
    intro i
    simpa only [coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hA' i
  have hdir := hderivative F e ω hF H p hH hp hι hσ hHp hstructure T hT A hA' h hh
  have hsum := F.firstCoefficientSlowBound_add e ω hF (fun _ => 1) T (Real.exp p) (Real.exp p) ε u hε hu
  have hdiff := F.firstCoefficientSlowBound_sub e ω hF (fun _ => 1) T
    (Real.exp p + Real.exp p) (Real.exp ((p + d) ^ d)) _ _ hsum hdir
  have hslow := hadjoint F e ω hF (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    H p hH hp hι hσ hHp hstructure T hT A⁻¹ hAi
    (Real.exp p + Real.exp p + Real.exp ((p + d) ^ d)) (by positivity) _ hdiff
  have hsize : Real.exp ((p + a) ^ a) * (Real.exp p + Real.exp p + Real.exp ((p + d) ^ d)) ≤
      Real.exp ((p + C) ^ C) := by
    calc
      _ ≤ Real.exp ((p + a) ^ a) * Real.exp (p + (p + d) ^ d + 2) :=
        mul_le_mul_of_nonneg_left (exp_repeated_add_le hp (by positivity)) (Real.exp_nonneg _)
      _ = Real.exp ((p + a) ^ a + p + (p + d) ^ d + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (hbudget p hp).1
  constructor
  · exact F.firstCoefficientSlowBound_mono e ω hF (fun _ => 1) T hT hsize _ hslow
  · have hv' := F.firstCoefficientGrid_mono e ω hF (fun _ => 1) hl hlm v hv
    have hsumGrid := F.firstCoefficientGrid_add e ω hF (fun _ => 1) m _ _ hv'
      (hAdjointGrid D μ hD hμ)
    exact F.firstCoefficientGrid_sub e ω hF (fun _ => 1) m _ _ hsumGrid (hDerivativeGrid D.coord hD h)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

universe uσ uι uL

def NativeNormalizedSquareSpec (s C : ℕ) : Prop :=
  ∀ {σ : Type uσ} {ι : Type uι} {L : Type uL}
    [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (_hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (p : ℝ) (_hp : 0 ≤ p) (_hD : D.GeometryComplexityLE p)
    (h : σ → ℚ) (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
    ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
      (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 1 + C) ^ C)) ∧
      ∃ r : D.filtration.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1),
        D.filtration.realAdaptedPolynomialMap (fun _ => 1)
            (D.filtration.realSquareFstPolynomialHom (fun _ => 1) r).coord =
          normalizedShiftLog (s + 1) h (-ε.coord) (-γ.coord)
            (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) ∧
        D.filtration.realSquareSndPolynomialHom (fun _ => 1) r = g ∧
        D.filtration.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
            D.filtration.realFirstCoefficientConstant (fun _ => 1) ε.coord -
            D.filtration.realFirstCoefficientAdjoint (fun _ => 1) g
              (D.filtration.realFirstCoefficientConstant (fun _ => 1) γ.coord) =
          D.filtration.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one)
            (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r)

theorem exists_native_normalized_square (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeNormalizedSquareSpec.{uσ, uι, uL} s C := by
  obtain ⟨C, hC, hnorm⟩ := exists_bounded_realified_square_polynomial.{uσ, uL} (s + 1)
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ d _ _ _ D b ω hF p hp hD h g
  let f : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1) :=
    polynomialOrbitOfLog (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord)
      (D.filtration.realAdaptedPolynomialMap_adapted (fun _ => 1) g.coord)
  obtain ⟨ε, γ, hγ, hε, q, hq, hfst, hsnd⟩ := hnorm D p hp hD (fun _ : σ => 1)
    (fun _ => Nat.zero_lt_one) h f
  let q' : D.filtration.squareFiltration.realification.adaptedLieSubalgebra (fun _ : σ => 1) :=
    ⟨q, (D.filtration.squareFiltration.realification.mem_adaptedSubmodule (fun _ => 1) q).mpr hq⟩
  obtain ⟨r, _, hrf, hrs⟩ := D.filtration.exists_realSquarePolynomial_lift (fun _ => 1) b ω hF q'
  have hf : D.filtration.realAdaptedPolynomialMap (fun _ => 1)
        (D.filtration.realSquareFstPolynomialHom (fun _ => 1) r).coord =
      normalizedShiftLog (s + 1) h (-ε.coord) (-γ.coord)
        (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) := hrf.trans hfst
  have hs : D.filtration.realAdaptedPolynomialMap (fun _ => 1)
        (D.filtration.realSquareSndPolynomialHom (fun _ => 1) r).coord =
      D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord := hrs.trans hsnd
  refine ⟨ε, γ, hγ, hε, r, hf, ?_, ?_⟩
  · apply D.filtration.realAdaptedPolynomialGroupHom_injective (fun _ => 1) b ω hF
    apply NilpotentLieBCHGroup.ext
    exact Subtype.ext hs
  · exact D.filtration.normalized_real_square_derivative_identity b ω hF h ε.coord γ.coord g r hf hs

end Erdos3

end

section

namespace Erdos3

theorem exists_synchronizedSquare_budget (r a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + (p + r) ^ r + a) ^ a ≤ (p + C) ^ C := by
  let P : Polynomial ℕ :=
    (Polynomial.X + (Polynomial.X + Polynomial.C r) ^ r + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [P, Polynomial.eval₂_pow] using hbudget p hp

namespace NilpotentLieFiltration

open Module

universe uσ uι uL

def SynchronizedSquareBoundSpec (s C : ℕ) : Prop :=
  ∀ {σ : Type uσ} {ι : Type uι} {L : Type uL}
    [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p),
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
      ∀ (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
        (A D : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
        (_hA : F.RealAdaptedCoefficientBound e ω hF (fun _ => 1) T (Real.exp p) A.coord)
        (_hD : F.RealAdaptedCoefficientGrid e ω hF (fun _ => 1) l D.coord)
        (h : σ → ℤ) (_hh : ∀ i, |(h i : ℝ)| ≤ T i)
        (E R : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1))
        (_hE : F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF)
          (fun _ => 1) T (Real.exp p) E)
        (_hR : F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF)
          (fun _ => 1) l R)
        (ε μ : F.RealFirstCoefficientModule (fun _ : σ => 1))
        (_hε : F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (Real.exp p) ε)
        (_hμ : F.FirstCoefficientGrid e ω hF (fun _ => 1) l μ),
        F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (Real.exp ((p + C) ^ C))
          (F.coefficientSlowCorrection A (fun i => (h i : ℝ)) ε
            (F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) E)) ∧
        F.FirstCoefficientGrid e ω hF (fun _ => 1) m
          (F.coefficientGridCorrection D (fun i => (h i : ℝ)) μ
            (F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) R))

theorem exists_synchronizedSquare_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ SynchronizedSquareBoundSpec.{uσ, uι, uL} s C := by
  obtain ⟨r, _, hrelative⟩ := exists_reducedRelativeCoefficient_bound.{uσ, uι, uL} s
  obtain ⟨a, _, hcorrection⟩ := exists_coefficient_correction_bound.{uσ, uι, uL} s
  obtain ⟨C, hC, hbudget⟩ := exists_synchronizedSquare_budget r a
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F e ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  obtain ⟨n, hn, hnp, hln, hrelative⟩ := hrelative F e ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  let q : ℝ := p + (p + r) ^ r
  have hpow : 0 ≤ (p + r) ^ r := by positivity
  have hq : 0 ≤ q := add_nonneg hp hpow
  have hpq : p ≤ q := le_add_of_nonneg_right hpow
  have hrq : (p + r) ^ r ≤ q := le_add_of_nonneg_left hp
  have hpqExp := Real.exp_le_exp.mpr hpq
  have hrqExp := Real.exp_le_exp.mpr hrq
  obtain ⟨m, hm, hmp, hnm, hcorrection⟩ := hcorrection F e ω hF H q hH hq
    (hι.trans hpq) (hσ.trans hpq) (hHp.trans hpqExp) hstructure n hn (hnp.trans hrqExp)
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr (hbudget p hp)), hln.trans hnm, ?_⟩
  intro T hT A D hA hD h hh E R hE hR ε μ hε hμ
  obtain ⟨hu, hv⟩ := hrelative T hT E R hE hR
  have hA' := F.realAdaptedCoefficientBound_mono e ω hF (fun _ => 1) T hT hpqExp A.coord hA
  have hD' := F.realAdaptedCoefficientGrid_mono e ω hF (fun _ => 1) hl hln D.coord hD
  have hε' := F.firstCoefficientSlowBound_mono e ω hF (fun _ => 1) T hT hpqExp ε hε
  have hu' := F.firstCoefficientSlowBound_mono e ω hF (fun _ => 1) T hT hrqExp _ hu
  have hμ' := F.firstCoefficientGrid_mono e ω hF (fun _ => 1) hl hln μ hμ
  obtain ⟨hleft, hright⟩ := hcorrection T hT A D hA' hD' h hh ε _ μ _ hε' hu' hμ' hv
  exact ⟨F.firstCoefficientSlowBound_mono e ω hF (fun _ => 1) T hT
    (Real.exp_le_exp.mpr (hbudget p hp)) _ hleft, hright⟩

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include b ω hF in
theorem synchronized_normalized_coefficient_common_derivative
    (h : σ → ℚ) (ε μ : ℝ ⊗[ℚ] L)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
    (A B D : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (r : F.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (E P R P₀ : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hf : F.realAdaptedPolynomialMap (fun _ => 1) (F.realSquareFstPolynomialHom (fun _ => 1) r).coord =
      normalizedShiftLog (s + 1) h (-ε) (-μ) (F.realAdaptedPolynomialMap (fun _ => 1) (A * B * D).coord))
    (hs : F.realAdaptedPolynomialMap (fun _ => 1) (F.realSquareSndPolynomialHom (fun _ => 1) r).coord =
      F.realAdaptedPolynomialMap (fun _ => 1) (A * B * D).coord)
    (hr : F.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r = E * P * R)
    (hA : F.adaptedReducedRealSymbolHom (fun _ => 1) A = F.reducedSquareRealSymbolHom (fun _ => 1) E)
    (hB : F.adaptedReducedRealSymbolHom (fun _ => 1) B = F.reducedSquareRealSymbolHom (fun _ => 1) P)
    (hP : P.coord ∈ realificationLieSubalgebra U)
    (hP₀ : P₀.coord ∈ realificationLieSubalgebra U)
    (hdiag : F.reducedSquareRealSymbolHom (fun _ => 1) P = F.reducedSquareRealSymbolHom (fun _ => 1) P₀) :
    F.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) -
      (F.coefficientSlowCorrection A (fun i => (h i : ℝ)) (F.realFirstCoefficientConstant (fun _ => 1) ε)
          (F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) E) +
        F.realFirstCoefficientAdjoint (fun _ => 1) B
          (F.coefficientGridCorrection D (fun i => (h i : ℝ)) (F.realFirstCoefficientConstant (fun _ => 1) μ)
            (F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) R)) +
        F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) P₀) ∈
      F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U) := by
  apply F.synchronized_coefficient_common_derivative b ω hF h U A B D E P R P₀
    (F.realFirstCoefficientConstant (fun _ => 1) ε) (F.realFirstCoefficientConstant (fun _ => 1) μ)
    hA hB hP hP₀ hdiag
  have hderivative := F.normalized_real_square_derivative_identity b ω hF h ε μ (A * B * D) r hf hs
  rwa [hr] at hderivative

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

universe uσ uι uL

variable {σ : Type uσ} {ι : Type uι} {L : Type uL}
  [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))

local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)
local notation "E₁" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "SGroup" => F.squareFiltration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1)

def NormalizedCommonFamilySpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p),
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
      ∀ (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
        (A B D : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
        (_hA : F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T (Real.exp p) A.coord)
        (_hD : F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l D.coord)
        (Hshifts : Finset (σ → ℤ))
        (r : (σ → ℤ) → F.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
        (E P R : (σ → ℤ) → SGroup) (P₀ : SGroup)
        (ε μ : (σ → ℤ) → ℝ ⊗[ℚ] L)
        (_hbox : ∀ h ∈ Hshifts, ∀ i, |(h i : ℝ)| ≤ T i)
        (_hf : ∀ h ∈ Hshifts,
          F.realAdaptedPolynomialMap (fun _ => 1) (F.realSquareFstPolynomialHom (fun _ => 1) (r h)).coord =
            normalizedShiftLog (s + 1) (fun i => (h i : ℚ)) (-ε h) (-μ h)
              (F.realAdaptedPolynomialMap (fun _ => 1) (A * B * D).coord))
        (_hs : ∀ h ∈ Hshifts,
          F.realAdaptedPolynomialMap (fun _ => 1) (F.realSquareSndPolynomialHom (fun _ => 1) (r h)).coord =
            F.realAdaptedPolynomialMap (fun _ => 1) (A * B * D).coord)
        (_hr : ∀ h ∈ Hshifts, F.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) (r h) =
          E h * P h * R h)
        (_hleft : ∀ h ∈ Hshifts, F.adaptedReducedRealSymbolHom (fun _ => 1) A =
          F.reducedSquareRealSymbolHom (fun _ => 1) (E h))
        (_hmiddle : ∀ h ∈ Hshifts, F.adaptedReducedRealSymbolHom (fun _ => 1) B =
          F.reducedSquareRealSymbolHom (fun _ => 1) (P h))
        (_hP : ∀ h ∈ Hshifts, (P h).coord ∈ realificationLieSubalgebra U)
        (_hP₀ : P₀.coord ∈ realificationLieSubalgebra U)
        (_hdiag : ∀ h ∈ Hshifts, F.reducedSquareRealSymbolHom (fun _ => 1) (P h) =
          F.reducedSquareRealSymbolHom (fun _ => 1) P₀)
        (_hE : ∀ h ∈ Hshifts, F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis b ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF)
          (fun _ => 1) T (Real.exp p) (E h))
        (_hR : ∀ h ∈ Hshifts, F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis b ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF)
          (fun _ => 1) l (R h))
        (_hε : ∀ h ∈ Hshifts, ∀ i, |(b.baseChange ℝ).repr (ε h) i| ≤ Real.exp p)
        (_hμ : ∀ h ∈ Hshifts, (fun i => (b.baseChange ℝ).repr (μ h) i) ∈ realDenominatorGrid l),
        ∃ S K : (σ → ℤ) → E₁, ∀ h ∈ Hshifts,
          (F.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) -
            (S h + F.realFirstCoefficientAdjoint (fun _ => 1) B (K h) +
              F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) P₀) ∈ J) ∧
          F.FirstCoefficientSlowBound b ω hF (fun _ => 1) T (Real.exp ((p + C) ^ C)) (S h) ∧
          F.FirstCoefficientGrid b ω hF (fun _ => 1) m (K h)

theorem exists_normalized_common_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {L : Type uL}
        [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
        (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1))),
        F.NormalizedCommonFamilySpec b ω hF U C := by
  obtain ⟨C, hC, hbound⟩ := exists_synchronizedSquare_bound.{uσ, uι, uL} s
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF U H p hH hp hι hσ hHp hstructure l hl hlp
  obtain ⟨m, hm, hmp, hlm, hcorrect⟩ := hbound F b ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro T hT A B D hA hD Hshifts r E P R P₀ ε μ hbox hf hs hr hleft hmiddle hP hP₀ hdiag hE hR hε hμ
  let S : (σ → ℤ) → F.RealFirstCoefficientModule (fun _ : σ => 1) := fun h =>
    F.coefficientSlowCorrection A (fun i => (h i : ℝ)) (F.realFirstCoefficientConstant (fun _ => 1) (ε h))
      (F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) (E h))
  let K : (σ → ℤ) → F.RealFirstCoefficientModule (fun _ : σ => 1) := fun h =>
    F.coefficientGridCorrection D (fun i => (h i : ℝ)) (F.realFirstCoefficientConstant (fun _ => 1) (μ h))
      (F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) (R h))
  refine ⟨S, K, ?_⟩
  intro h hh
  have hε' := F.realFirstCoefficientConstant_slow (fun _ => 1) b ω hF T hT
    (Real.exp p) (Real.exp_nonneg _) (ε h) (hε h hh)
  have hμ' := F.realFirstCoefficientConstant_grid (fun _ : σ => 1) b ω hF l (μ h) (hμ h hh)
  have hbounds := hcorrect T hT A D hA hD h (hbox h hh) (E h) (R h) (hE h hh) (hR h hh)
    (F.realFirstCoefficientConstant (fun _ : σ => 1) (ε h))
    (F.realFirstCoefficientConstant (fun _ : σ => 1) (μ h)) hε' hμ'
  refine ⟨?_, hbounds.1, hbounds.2⟩
  have hcommon := F.synchronized_normalized_coefficient_common_derivative b ω hF
    (fun i => (h i : ℚ)) (ε h) (μ h) U A B D (r h) (E h) (P h) (R h) P₀
    (hf h hh) (hs h hh) (hr h hh) (hleft h hh) (hmiddle h hh) (hP h hh) hP₀ (hdiag h hh)
  simpa only [Rat.cast_intCast] using hcommon

end Erdos3.NilpotentLieFiltration

end

end OAI
