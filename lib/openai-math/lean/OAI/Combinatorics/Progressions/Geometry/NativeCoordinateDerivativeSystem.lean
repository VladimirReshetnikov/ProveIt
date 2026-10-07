import OAI.Combinatorics.Progressions.Estimates.FastHorizontalFactorization
import OAI.Combinatorics.Progressions.Linear.LayerOneProjectionMatrixBounds

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι]
  [LieRing L] [LieAlgebra ℚ L] {s a d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))

local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) U
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "Q" => (E ⧸ J)
local notation "Hq" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U

def NativeCoordinateDerivativeSpec : Prop :=
  ∀ (b : Basis (Fin d) ℝ Q) (rows : Fin d → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (ha : a ≤ d) (η : (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)))
    (_hη : ∀ x, η (fun i => b.equivFun x (Fin.castLE ha i)) = Hq x)
    (sectionMap : (Fin d → ℝ) →ₗ[ℝ] E)
    (_hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y)
    (Cscale : ℝ) (_hC : 0 ≤ Cscale)
    (_hweighted : ∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
      (∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M x → ∀ i,
        |b.equivFun ((J).mkQ x) i| ≤ Cscale * M / monomialScale T (rows i).val.1) ∧
      (∀ y, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T (Cscale * M) (sectionMap y)))
    (m : ℕ) (_hm : 0 < m)
    (_hgrid : ∀ y, y ∈ realDenominatorGrid 1 → F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) m (sectionMap y))
    (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
    (g : F.realFastDiagonalSubgroup (fun _ : σ => 1) U)
    (bound : ℝ) (_hbound : 0 ≤ bound)
    (D : CoordinateDerivativeSystem ha T (b.equivFun.toLinearMap.comp (F.realFastCoefficientDirectionMap U g.val))
      (b.equivFun.symm.trans ((ρ g).trans b.equivFun))
      (fun i => monomialScale T (rows i).val.1) bound)
    (p : ℝ) (_hp : 0 ≤ p) (_hap : (a : ℝ) ≤ p) (_hmp : (m : ℝ) ≤ Real.exp p)
    (_hCp : Cscale ≤ Real.exp p) (_hDp : (D.heightBound : ℝ) ≤ Real.exp p),
    D.k ≤ a ∧ ∃ (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis (Fin D.k) ℚ K),
      ∃ H : ℕ, 1 ≤ H ∧ (H : ℝ) ≤ Real.exp ((p + 2) ^ 3) ∧
        (∀ i j, RationalHeightLE ((F.layerOneBasis e ω hF).repr (bK j : L ⧸ F.layer 2) i) H) ∧
        ∃ l : ℕ, 0 < l ∧ (l : ℝ) ≤ bound ^ 2 ∧
          ∃ S R : (K.baseChange ℝ) →ₗ[ℝ] Q,
            S = (ρ g).toLinearMap.comp R ∧ (Hq).comp S = (K.baseChange ℝ).subtype ∧
            (Hq).comp R = (K.baseChange ℝ).subtype ∧
            (∀ x, ‖basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1) (S x)‖ ≤
              (bound * Cscale) * ‖cH x.val‖) ∧
            (∀ j, b.equivFun (R (realSubmoduleBasis K bK j)) ∈ realDenominatorGrid l) ∧
            ∃ (small rational : σ → Q) (k : σ → K.baseChange ℝ),
              (∀ i, F.realFastCoefficientDirectionMap U g.val (Pi.single i 1) =
                small i + ρ g (rational i) + S (k i)) ∧
              (∀ i, b.equivFun (rational i) ∈ realDenominatorGrid l) ∧
              (∀ i, ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1) (small i)‖ ≤
                bound / T i) ∧
              (∀ i, ‖cH (Hq (small i))‖ ≤ (Cscale * bound) / T i)

theorem exists_native_coordinate_derivative_system :
    F.NativeCoordinateDerivativeSpec (σ := σ) (a := a) (d := d) e ω hF U := by
  intro b rows ha η hη sectionMap hsection Cscale hC hweighted m hm hgrid
    T hT g bound hbound D p hp hap hmp hCp hDp
  have hone (α : σ →₀ ℕ) : monomialScale (fun _ : σ => (1 : ℝ)) α = 1 := by
    simp [monomialScale]
  have hsectionOne (y : Fin d → ℝ) (M : ℝ) (hM : 0 ≤ M) (hy : ∀ j, |y j| ≤ M) :
      F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) (fun _ => 1) (Cscale * M) (sectionMap y) := by
    apply (hweighted (fun _ => 1) (fun _ => by norm_num) M hM).2 y
    intro j
    simpa only [hone, div_one] using hy j
  have hprojOne (x : E) (M : ℝ) (hM : 0 ≤ M)
      (hx : F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) (fun _ => 1) M x) (j : Fin d) :
      |b.equivFun ((J).mkQ x) j| ≤ Cscale * M := by
    simpa only [hone, div_one] using
      (hweighted (fun _ => 1) (fun _ => by norm_num) M hM).1 x hx j
  have hraw := F.layerOne_rational_kernel_basis e ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one)
    Uf b ha η hη sectionMap hsection 1 m hm Cscale hC hgrid hsectionOne
    D.K D.basisMatrix D.span_eq D.independent_real D.basis_height
  obtain ⟨v, hv, hspan, hli, hheight⟩ := hraw
  let K := Submodule.span ℚ (Set.range v)
  let bK : Basis (Fin D.k) ℚ K := Basis.span hli
  have hbK (j : Fin D.k) : (bK j : L ⧸ F.layer 2) = v j :=
    Basis.coe_span_apply hli j
  have hbasis (j : Fin D.k) : (1 : ℝ) ⊗ₜ[ℚ] (bK j : L ⧸ F.layer 2) =
      η ((D.basisMatrix.map (Rat.castHom ℝ)).col j) := by
    exact (congrArg (fun z : L ⧸ F.layer 2 => (1 : ℝ) ⊗ₜ[ℚ] z) (hbK j)).trans (hv j)
  have htransport := transport_coordinate_derivatives_to_rational_span ha b η Hq hη T
    (F.realFastCoefficientDirectionMap U g.val) (ρ g)
    (fun i => monomialScale T (rows i).val.1) bound D K bK hspan hbasis
  obtain ⟨S, R, hSR, hS, hR, hSnorm, hRgrid, small, rational, k, hsystem, hrgrid, hsmall⟩ := htransport
  let H₀ := (a + 1) * (max m (Nat.ceil ((m : ℝ) * Cscale)) * D.heightBound) ^ a
  have hH₀ : (H₀ : ℝ) ≤ Real.exp ((p + 2) ^ 3) :=
    layerOne_basis_transport_height_le_exp a m D.heightBound Cscale p hp hap hmp hC hCp hDp
  have hH : ((max 1 H₀ : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (Real.one_le_exp (by positivity)) hH₀
  let l := D.liftDenominator * D.derivativeDenominator
  have hl : 0 < l := Nat.mul_pos D.liftDenominator_pos D.derivativeDenominator_pos
  have hlb : (l : ℝ) ≤ bound ^ 2 := by
    rw [Nat.cast_mul, pow_two]
    exact mul_le_mul D.liftDenominator_le D.derivativeDenominator_le (Nat.cast_nonneg _) hbound
  have hk : D.k ≤ a := by
    simpa using D.independent_real.fintype_card_le_finrank
  refine ⟨hk, K, bK, max 1 H₀, le_max_left _ _, hH, ?_, l, hl, hlb,
    S, R, hSR, hS, hR, ?_, ?_, small, rational, k, ?_, ?_, hsmall, ?_⟩
  · intro i j
    exact (congrArg (fun z : L ⧸ F.layer 2 =>
      RationalHeightLE ((F.layerOneBasis e ω hF).repr z i) (max 1 H₀)) (hbK j)).mpr
        ((hheight i j).mono (le_max_right 1 H₀))
  · intro x
    have hx := F.layerOne_equiv_symm_norm e ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one)
      Uf b ha η hη Cscale hC hprojOne x.val
    calc
      _ ≤ bound * ‖η.symm x.val‖ := hSnorm x
      _ ≤ bound * (Cscale * ‖cH x.val‖) := mul_le_mul_of_nonneg_left hx hbound
      _ = (bound * Cscale) * ‖cH x.val‖ := (mul_assoc _ _ _).symm
  · intro j
    exact realDenominatorGrid_subset_of_dvd D.liftDenominator_pos
      (dvd_mul_right D.liftDenominator D.derivativeDenominator) (hRgrid j)
  · intro i
    exact hsystem i
  · intro i
    exact realDenominatorGrid_subset_of_dvd D.derivativeDenominator_pos
      (dvd_mul_left D.derivativeDenominator D.liftDenominator) (hrgrid i)
  · intro i
    have hx := F.realFastCoefficientHorizontal_section_norm_bound e ω hF (fun _ => 1)
      (fun _ => Nat.zero_lt_one) Uf b sectionMap hsection rows T hT Cscale hC
      (fun M hM => (hweighted T hT M hM).2) (small i)
    calc
      _ ≤ Cscale * ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1) (small i)‖ := hx
      _ ≤ Cscale * (bound / T i) := mul_le_mul_of_nonneg_left (hsmall i) hC
      _ = (Cscale * bound) / T i := (mul_div_assoc _ _ _).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
