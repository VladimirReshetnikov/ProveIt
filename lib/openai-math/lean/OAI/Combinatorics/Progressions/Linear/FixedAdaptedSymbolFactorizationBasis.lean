/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.UnnormalizedCommonSymbolFactorization
import OAI.Combinatorics.Progressions.Nilpotent.NiltestVerticalBounds

namespace OAI

section

namespace Erdos3

open Module

theorem rational_basis_coordinates_logHeight
    {ι κ V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (c : Basis κ ℚ V) {H : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (hentries : ∀ i j, RationalHeightLE (c.repr (b i) j) H)
    (x : V) (hx : ∀ i, rationalLogHeight (b.repr x i) ≤ p) (j : κ) :
    rationalLogHeight (c.repr x j) ≤ (p + 2) ^ 4 := by
  classical
  let K := ⌈Real.exp p⌉₊
  have hK : (K : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hKH : ((K * H : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp (p + 1) * Real.exp p :=
        mul_le_mul hK hH (Nat.cast_nonneg H) (Real.exp_nonneg _)
      _ = Real.exp (2 * p + 1) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
  have hcoord := linearMap_coordinate_height b c (LinearMap.id : V →ₗ[ℚ] V)
    hentries x (fun i => rationalHeightLE_ceil_exp (hx i)) j
  have hcost := rational_sum_cost_le_exp (Fintype.card ι) (K * H) hp 2 1 hKH
    (by simpa only [pow_one] using hι.trans (show p ≤ p + 2 by linarith))
  exact rationalLogHeight_le_of_height hcoord hcost

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (c : Basis κ ℚ L) (ν : κ → ℕ)
  (hC : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i})) (w : σ → ℕ)

theorem gradedSymbolPolynomial_basis_independent :
    F.gradedSymbolPolynomial c ν hC w = F.gradedSymbolPolynomial b ω hF w := by
  apply LinearMap.ext
  intro x
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  apply coefficients.injective
  ext α
  rw [F.gradedSymbolPolynomial_coefficient_symbol, F.gradedSymbolPolynomial_coefficient_symbol]

theorem symbolPointwiseSubalgebra_basis_independent (W : LieSubalgebra ℚ F.AssociatedGraded) :
    F.symbolPointwiseSubalgebra c ν hC w W = F.symbolPointwiseSubalgebra b ω hF w W := by
  ext x
  simp only [F.mem_symbolPointwiseSubalgebra_iff,
    F.gradedSymbolPolynomial_basis_independent b ω hF c ν hC w]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (c : Basis κ ℚ L) (ν : κ → ℕ)
  (hC : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))

theorem polynomialSymbolBasis_change_coordinate [DecidableEq σ] (w : σ → ℕ)
    (i : SymbolBasisIndex w ω) (j : SymbolBasisIndex w ν) :
    (F.polynomialSymbolBasis c ν hC w).repr (F.polynomialSymbolBasis b ω hF w i) j =
      if i.val.1 = j.val.1 then c.repr (b i.val.2) j.val.2 else 0 := by
  classical
  rw [F.polynomialSymbolBasis_apply, F.polynomialSymbolBasis_repr_map,
    F.adaptedMonomialBasis_coe, coefficients_monomial]
  by_cases hij : i.val.1 = j.val.1
  · simp only [hij, Finsupp.single_eq_same, ite_true]
  · simp only [Finsupp.single_eq_of_ne (Ne.symm hij), map_zero, Finsupp.zero_apply, ite_eq_right hij]

theorem associatedGradedBasis_change_coordinate (i : ι) (j : κ) :
    (F.associatedGradedBasis c ν hC).repr (F.associatedGradedBasis b ω hF i) j =
      if ω i = ν j then c.repr (b i) j else 0 := by
  classical
  rw [F.associatedGradedBasis_repr, F.associatedGradedBasis_apply,
    F.polynomialSymbolBasis_change_coordinate]
  simp only [unitMonomial_injective.eq_iff]

theorem associatedGradedBasis_projection (k : ℕ) (i : ι) :
    basisGradeProjection (F.associatedGradedBasis c ν hC) ν k (F.associatedGradedBasis b ω hF i) =
      if ω i = k then F.associatedGradedBasis b ω hF i else 0 := by
  classical
  by_cases hik : ω i = k
  · rw [ite_eq_left hik]
    apply (F.associatedGradedBasis c ν hC).repr.injective
    ext j
    simp only [basisGradeProjection_repr, F.associatedGradedBasis_change_coordinate]
    by_cases hj : ν j = k
    · rw [ite_eq_left hj]
    · rw [ite_eq_right hj, ite_eq_right (show ω i ≠ ν j by omega)]
  · rw [ite_eq_right hik]
    apply (F.associatedGradedBasis c ν hC).repr.injective
    ext j
    simp only [basisGradeProjection_repr, F.associatedGradedBasis_change_coordinate,
      map_zero, Finsupp.zero_apply]
    by_cases hj : ν j = k
    · rw [ite_eq_left hj, ite_eq_right (show ω i ≠ ν j by omega)]
    · rw [ite_eq_right hj]

theorem associatedGraded_projection_basis_independent (k : ℕ) :
    basisGradeProjection (F.associatedGradedBasis c ν hC) ν k =
      basisGradeProjection (F.associatedGradedBasis b ω hF) ω k := by
  apply (F.associatedGradedBasis b ω hF).ext
  intro i
  rw [F.associatedGradedBasis_projection b ω hF c ν hC,
    F.associatedGradedBasis_projection b ω hF b ω hF]

theorem associatedGraded_submodule_basis_independent (U : Submodule ℚ F.AssociatedGraded) :
    BasisGradedSubmodule (F.associatedGradedBasis c ν hC) ν U ↔
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U := by
  simp only [BasisGradedSubmodule, F.associatedGraded_projection_basis_independent b ω hF c ν hC]

theorem gradedFrequency_top_basis_independent (η : L →ₗ[ℚ] ℚ) (x : F.AssociatedGraded)
    (hx : basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x) :
    F.gradedFrequency c ν hC η x = F.gradedFrequency b ω hF η x := by
  have hm : x ∈ LinearMap.range (F.associatedGradedPieceMap s) := by
    rw [F.associatedGradedPieceMap_range b ω hF]
    rw [← hx]
    exact basisCoordinateProjection_mem_span (F.associatedGradedBasis b ω hF) {i | ω i = s} x
  obtain ⟨v, hv⟩ := hm
  rw [← hv, F.gradedFrequency_top_piece c ν hC, F.gradedFrequency_top_piece b ω hF]

theorem polynomialSymbolBasis_change_height (w : σ → ℕ) {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ i j, RationalHeightLE (c.repr (b i) j) H)
    (i : SymbolBasisIndex w ω) (j : SymbolBasisIndex w ν) :
    RationalHeightLE ((F.polynomialSymbolBasis c ν hC w).repr
      (F.polynomialSymbolBasis b ω hF w i) j) H := by
  classical
  rw [F.polynomialSymbolBasis_change_coordinate]
  split_ifs
  · exact hb i.val.2 j.val.2
  · exact rationalHeightLE_zero hH

theorem associatedGradedBasis_change_height {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ i j, RationalHeightLE (c.repr (b i) j) H) (i : ι) (j : κ) :
    RationalHeightLE ((F.associatedGradedBasis c ν hC).repr
      (F.associatedGradedBasis b ω hF i) j) H := by
  classical
  rw [F.associatedGradedBasis_change_coordinate]
  split_ifs
  · exact hb i j
  · exact rationalHeightLE_zero hH

theorem native_symbol_basis_independent (w : σ → ℕ) (g : F.RealAdaptedPolynomialGroup w) :
    F.realPolynomialSymbolHom c ν hC w (F.realAdaptedPolynomialGroupHom w g) =
      F.realPolynomialSymbolHom b ω hF w (F.realAdaptedPolynomialGroupHom w g) := by
  apply NilpotentLieBCHGroup.ext
  rw [F.realPolynomialSymbolHom_groupHom_coord, F.realPolynomialSymbolHom_groupHom_coord]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix NNReal

def ControlledSymbolBasisChangeSpec (s C : ℕ) : Prop :=
  ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ L) (ν : κ → ℕ)
    (hC : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hκ : (Fintype.card κ : ℝ) ≤ p)
    (_hσ : (Fintype.card σ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hb : ∀ i j, RationalHeightLE (c.repr (b i) j) H)
    (T : σ → ℝ) (_hT : ∀ i, 0 < T i) (η : L →ₗ[ℚ] ℚ)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)),
    F.ControlledSymbolFactorization b ω hF η T X p →
      F.ControlledSymbolFactorization c ν hC η T X ((p + C) ^ C)

theorem exists_controlled_symbol_basis_change (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ControlledSymbolBasisChangeSpec s C := by
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2)
  let P : Polynomial ℕ := (Q + 2) ^ 3 + Polynomial.X + (Polynomial.X + 2) ^ 4
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hF c ν hc H p hH hp hι hκ hσ hHp hb T hT η X hX
  classical
  let w := fun _ : σ => 1
  let q : ℝ := (p + (s + 2 : ℕ)) ^ (s + 2)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (show p ≤ p + (s + 2 : ℕ) from le_add_of_nonneg_right (Nat.cast_nonneg _)).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show (1 : ℝ) ≤ p + (s + 2 : ℕ) by have := Nat.cast_nonneg (α := ℝ) s; push_cast; linarith)
      (show 1 ≤ s + 2 by omega)
  have hcost : 0 ≤ (q + 2) ^ 3 + p := by positivity
  have hheight : 0 ≤ (p + 2) ^ 4 := by positivity
  have hbound : (q + 2) ^ 3 + p + (p + 2) ^ 4 ≤ (p + C) ^ C := by
    simpa [P, Q, q, Polynomial.eval₂_pow] using hfinal p hp
  have hcostC : (q + 2) ^ 3 + p ≤ (p + C) ^ C := by linarith
  have hheightC : (p + 2) ^ 4 ≤ (p + C) ^ C := by linarith
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s (fun _ => Nat.zero_lt_one) (F.adaptedBasis_weight_le_step b ω hF)
  let : Fintype (SymbolBasisIndex w ν) :=
    symbolBasisIndexFintype w ν s (fun _ => Nat.zero_lt_one) (F.adaptedBasis_weight_le_step c ν hc)
  let Bb := F.polynomialSymbolBasis b ω hF w
  let Bc := F.polynomialSymbolBasis c ν hc w
  let M : Matrix (SymbolBasisIndex w ν) (SymbolBasisIndex w ω) ℚ := fun i j => Bc.repr (Bb j) i
  have hMb : ∀ i j, RationalHeightLE (M i j) H :=
    fun i j => F.polynomialSymbolBasis_change_height b ω hF c ν hc w hH hb j i
  have hDb : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (symbolBasisIndex_card_le w ω s (fun _ => Nat.zero_lt_one)
      (F.adaptedBasis_weight_le_step b ω hF))).trans
        (by simpa only [q, Nat.cast_add, Nat.cast_ofNat] using
          symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hDc : (Fintype.card (SymbolBasisIndex w ν) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (symbolBasisIndex_card_le w ν s (fun _ => Nat.zero_lt_one)
      (F.adaptedBasis_weight_le_step c ν hc))).trans
        (by simpa only [q, Nat.cast_add, Nat.cast_ofNat] using
          symbol_dimension_bound_le_power s (Fintype.card κ) (Fintype.card σ) hp hκ hσ)
  have hHq : (H : ℝ) ≤ Real.exp q := hHp.trans (Real.exp_le_exp.mpr hpq)
  have hδ : (matrixDenominator M : ℝ) ≤ Real.exp ((q + 2) ^ 3) :=
    real_basis_transfer_denominator Bb Bc hq hDb hDc hHq hMb
  have hblock : ∀ i j, i.val.1 ≠ j.val.1 → M i j = 0 := by
    intro i j hij
    change (F.polynomialSymbolBasis c ν hc w).repr (F.polynomialSymbolBasis b ω hF w j) i = 0
    rw [F.polynomialSymbolBasis_change_coordinate, ite_eq_right hij.symm]
  obtain ⟨m, E, R, B, Z, v, hm, hmp, hprod, hE, hB, hv, hZ, hh, hη, hR⟩ := hX
  let n := matrixDenominator M * m
  have hn : 0 < n := Nat.mul_pos (matrixDenominator_pos M) hm
  have hnC : (n : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    dsimp only [n]
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp ((q + 2) ^ 3) * Real.exp p := mul_le_mul hδ hmp (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((q + 2) ^ 3 + p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hcostC
  have hgrid : F.SymbolRationalGrid c ν hc w n B :=
    real_basis_coordinates_grid Bb Bc m B.coord hB
  have hslow : F.SymbolSlowBound c ν hc w T (Real.exp ((p + C) ^ C)) E := by
    dsimp only [SymbolSlowBound] at hE
    intro i
    have hcoord := congrFun (real_basis_coordinates_transfer Bb Bc E.coord) i
    change |(Bc.baseChange ℝ).repr E.coord i| ≤ _
    rw [hcoord]
    have hEcoord : ∀ j : SymbolBasisIndex w ω,
        |(Bb.baseChange ℝ).repr E.coord j| ≤ Real.exp p / monomialScale T j.val.1 := by
      simpa only [Bb, w] using hE
    have hweighted := weighted_matrix_mulVec_bound (fun i : SymbolBasisIndex w ν => i.val.1)
      (fun j : SymbolBasisIndex w ω => j.val.1) (fun i j => (M i j : ℝ))
      (fun i j hij => by rw [hblock i j hij, Rat.cast_zero]) (H : ℝ≥0)
      (fun i j => (hMb i j).abs_real_le) (monomialScale T) (monomialScale_pos T hT)
      (Real.exp_nonneg p) (fun j => (Bb.baseChange ℝ).repr E.coord j) hEcoord i
    have hfactor : ((Fintype.card (SymbolBasisIndex w ω) : ℝ) + 1) * ((H : ℝ) + 1) ≤
        Real.exp ((q + 2) ^ 3) := by
      have hHlarge : (H : ℝ) ≤ Real.exp ((q + 2) ^ 1) :=
        hHq.trans (Real.exp_le_exp.mpr (by simp))
      calc
        _ ≤ ((Fintype.card (SymbolBasisIndex w ω) : ℝ) + 1) *
            (Real.exp ((q + 2) ^ 1) + 1) :=
          mul_le_mul_of_nonneg_left (add_le_add hHlarge le_rfl) (by positivity)
        _ ≤ _ := matrix_weighted_factor_le_exp_power _ hq hDb 1 (by decide)
    apply hweighted.trans
    apply div_le_div_of_nonneg_right _ (monomialScale_pos T hT i.val.1).le
    calc
      _ ≤ Real.exp ((q + 2) ^ 3) * Real.exp p := mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg p)
      _ = Real.exp ((q + 2) ^ 3 + p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hcostC
  have hcard : Fintype.card κ = Fintype.card ι := by
    rw [← finrank_eq_card_basis c, finrank_eq_card_basis b]
  let e := Fintype.equivOfCardEq hcard
  let v' : κ → F.AssociatedGraded := fun i => v (e i)
  have hrange : Set.range v' = Set.range v := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, congrArg v (e.apply_symm_apply i)⟩
  refine ⟨n, E, R, B, Z, v', hn, hnC, hprod, hslow, hgrid, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrange]
    exact hv
  · exact (F.associatedGraded_submodule_basis_independent b ω hF c ν hc Z.toSubmodule).mpr hZ
  · intro i j
    have hx : ∀ k, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (v (e i)) k) ≤ p := hh (e i)
    have hbc : ∀ j k, RationalHeightLE ((F.associatedGradedBasis c ν hc).repr
        (F.associatedGradedBasis b ω hF j) k) H :=
      F.associatedGradedBasis_change_height b ω hF c ν hc hH hb
    have htransfer := rational_basis_coordinates_logHeight (F.associatedGradedBasis b ω hF)
      (F.associatedGradedBasis c ν hc) hp hι hHp hbc (v (e i)) hx j
    exact htransfer.trans hheightC
  · intro x hx htop
    have htop' : basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x := by
      rw [← F.associatedGraded_projection_basis_independent b ω hF c ν hc s]
      exact htop
    exact (F.gradedFrequency_top_basis_independent b ω hF c ν hc η x htop').trans (hη x hx htop')
  · rw [F.symbolPointwiseSubalgebra_basis_independent b ω hF c ν hc w]
    simpa only [w] using hR

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

def fixedAdaptedSymbolTransferInput (p q : ℝ) : ℝ :=
  ((p + 3) ^ 5 + q + 1 + 2) ^ 4 + q + 1

theorem exists_fixed_adapted_symbol_factorization_basis (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p →
      ∃ (c : Basis (Fin (finrank ℚ L)) ℚ L)
        (ν : Fin (finrank ℚ L) → ℕ) (N : ℕ),
      ∃ hC : ∀ j, D.filtration.layer j =
        Submodule.span ℚ (c '' {i | j ≤ ν i}),
      Monotone ν ∧ IsCentralLieBasis c ∧
      (∀ j i, rationalLogHeight (D.basis.repr (c j) i) ≤ p + 1) ∧
      (∀ i j, rationalLogHeight (c.repr (D.basis i) j) ≤ (p + 3) ^ 5) ∧
      (∀ i j k, rationalLogHeight (lieStructureConstants c i j k) ≤ (p + 3) ^ 11) ∧
      0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 3) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates c D.lattice ∧
      bchSubgroupCoordinates c D.lattice ⊆ denominatorGrid N ∧
      ∀ {q : ℝ}, p ≤ q →
      ∀ {σ : Type*} [Fintype σ], (Fintype.card σ : ℝ) ≤ q →
      ∀ (b : Basis (Fin (finrank ℚ L)) ℚ L)
        (ω : Fin (finrank ℚ L) → ℕ)
        (hF : ∀ j, D.filtration.layer j =
          Submodule.span ℚ (b '' {i | j ≤ ω i})),
        (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ q) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ (η : L →ₗ[ℚ] ℚ)
        (X : D.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)),
        D.filtration.ControlledSymbolFactorization b ω hF η T X q →
        D.filtration.ControlledSymbolFactorization c ν hC η T X
          ((fixedAdaptedSymbolTransferInput p q + C) ^ C) := by
  obtain ⟨C, hC, hchange⟩ :=
    NilpotentLieFiltration.exists_controlled_symbol_basis_change s
  refine ⟨C, hC, ?_⟩
  intro L _ _ d D p hp hD
  obtain ⟨c, ν, N, hν, hc, hlayers, hcoord, hinv, hbracket,
    hN, hNp, hin, hout⟩ := D.exists_controlled_adapted_basis hp hD
  refine ⟨c, ν, N, hlayers, hν, hc, hcoord, hinv, hbracket,
    hN, hNp, hin, hout, ?_⟩
  intro q hpq σ _ hσ b ω hF hb T hT η X hX
  let t : ℝ := (p + 3) ^ 5 + q + 1
  let R : ℝ := (t + 2) ^ 4 + q + 1
  have hq : 0 ≤ q := hp.trans hpq
  have hA : 0 ≤ (p + 3) ^ 5 := by positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hqt : q ≤ t := by dsimp [t]; linarith
  have hqR : q ≤ R := by
    dsimp only [R]
    linarith [show 0 ≤ (t + 2) ^ 4 by positivity]
  have hR : 0 ≤ R := hq.trans hqR
  have hd : (Fintype.card (Fin d) : ℝ) ≤ q := by
    simpa only [Fintype.card_fin] using hD.1.trans hpq
  have hdim : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ q := by
    simpa only [Fintype.card_fin, finrank_eq_card_basis D.basis] using hd
  have hH₀ : (⌈Real.exp ((p + 3) ^ 5)⌉₊ : ℝ) ≤ Real.exp t :=
    (ceil_exp_le_exp_add_one hA).trans
      (Real.exp_le_exp.mpr (by dsimp [t]; linarith))
  have hbc : ∀ i j, rationalLogHeight (c.repr (b i) j) ≤ (t + 2) ^ 4 := by
    intro i j
    exact rational_basis_coordinates_logHeight D.basis c ht (hd.trans hqt) hH₀
      (fun i j => rationalHeightLE_ceil_exp (hinv i j)) (b i)
      (fun j => (hb i j).trans hqt) j
  have hH : (⌈Real.exp ((t + 2) ^ 4)⌉₊ : ℝ) ≤ Real.exp R :=
    (ceil_exp_le_exp_add_one (by positivity)).trans
      (Real.exp_le_exp.mpr (by dsimp [R]; linarith))
  apply hchange D.filtration b ω hF c ν hlayers
    ⌈Real.exp ((t + 2) ^ 4)⌉₊ R (one_le_ceil_exp _) hR
    (hdim.trans hqR) (hdim.trans hqR) (hσ.trans hqR) hH
    (fun i j => rationalHeightLE_ceil_exp (hbc i j)) T hT η X
  exact hX.mono D.filtration b ω hF hqR hT

end Erdos3.RationalFilteredNilmanifold

end

end OAI
