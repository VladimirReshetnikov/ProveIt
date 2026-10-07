import OAI.Combinatorics.Progressions.Polynomial.NativeMarkedPolynomialFreezing

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ η L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (w : σ → ℕ) (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)

noncomputable def frozenMarkedLeftOrbit
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group) :
    F.realification.PolynomialOrbit w :=
  (F.realification.polynomialOrbitCoordinates w).symm
    (F.frozenMarkedLeft G w S hS
      (G.realification.polynomialOrbitCoordinates w marked) center)

noncomputable def frozenMarkedRightOrbit
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group) :
    F.realification.PolynomialOrbit w :=
  (F.realification.polynomialOrbitCoordinates w).symm
    (F.frozenMarkedRight G w S hS
      (G.realification.polynomialOrbitCoordinates w marked) center)

theorem nativeFrozenMarkedOrbitCoordinates_realValue
    (g : F.realification.PolynomialOrbit w) (x : σ → ℝ) :
    F.adaptedPolynomialRealValueHom w x (F.realification.polynomialOrbitCoordinates w g) =
      F.realification.polynomialOrbitRealEval w x g := rfl

theorem nativeFrozenMarkedOrbitCoordinates_symm_realEval
    (g : (F.realification.adaptedPolynomialFiltration w).Group) (x : σ → ℝ) :
    F.realification.polynomialOrbitRealEval w x
      ((F.realification.polynomialOrbitCoordinates w).symm g) =
      F.adaptedPolynomialRealValueHom w x g := rfl

theorem frozenMarkedLeftOrbit_realEval
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group)
    (x : σ → ℝ) :
    F.realification.polynomialOrbitRealEval w x
      (F.frozenMarkedLeftOrbit G w S hS marked center) =
      center * ⟨S.baseChange ℝ (G.realification.polynomialOrbitRealEval w x marked).coord⟩ := by
  rw [frozenMarkedLeftOrbit, F.nativeFrozenMarkedOrbitCoordinates_symm_realEval,
    frozenMarkedLeft, map_mul, F.adaptedPolynomialRealValueHom_constant,
    F.filteredRealPolynomialSection_value, G.nativeFrozenMarkedOrbitCoordinates_realValue]

theorem frozenMarkedRightOrbit_realEval
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group)
    (x : σ → ℝ) :
    F.realification.polynomialOrbitRealEval w x
      (F.frozenMarkedRightOrbit G w S hS marked center) =
      ⟨S.baseChange ℝ (G.realification.polynomialOrbitRealEval w x marked).coord⟩ * center := by
  rw [frozenMarkedRightOrbit, F.nativeFrozenMarkedOrbitCoordinates_symm_realEval,
    frozenMarkedRight, map_mul, F.adaptedPolynomialRealValueHom_constant,
    F.filteredRealPolynomialSection_value, G.nativeFrozenMarkedOrbitCoordinates_realValue]

theorem frozenMarkedLeftOrbit_realEval_eq_local
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group)
    (v : η → ℕ) (localMarked : (G.realification.adaptedPolynomialFiltration v).Group)
    (x : η → ℝ) (y : σ → ℝ)
    (hmarked : G.adaptedPolynomialRealValueHom v x localMarked =
      G.realification.polynomialOrbitRealEval w y marked) :
    F.realification.polynomialOrbitRealEval w y
      (F.frozenMarkedLeftOrbit G w S hS marked center) =
      F.adaptedPolynomialRealValueHom v x (F.frozenMarkedLeft G v S hS localMarked center) := by
  rw [F.frozenMarkedLeftOrbit_realEval, frozenMarkedLeft, map_mul,
    F.adaptedPolynomialRealValueHom_constant, F.filteredRealPolynomialSection_value, hmarked]

theorem frozenMarkedRightOrbit_realEval_eq_local
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group)
    (v : η → ℕ) (localMarked : (G.realification.adaptedPolynomialFiltration v).Group)
    (x : η → ℝ) (y : σ → ℝ)
    (hmarked : G.adaptedPolynomialRealValueHom v x localMarked =
      G.realification.polynomialOrbitRealEval w y marked) :
    F.realification.polynomialOrbitRealEval w y
      (F.frozenMarkedRightOrbit G w S hS marked center) =
      F.adaptedPolynomialRealValueHom v x (F.frozenMarkedRight G v S hS localMarked center) := by
  rw [F.frozenMarkedRightOrbit_realEval, frozenMarkedRight, map_mul,
    F.adaptedPolynomialRealValueHom_constant, F.filteredRealPolynomialSection_value, hmarked]

variable (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (hsection : Function.RightInverse S φ)

include hφ hsection

theorem frozenMarkedLeftOrbit_formal_mark
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group)
    (hcenter : realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ center = 1) :
    map (realLieHomToRat (realificationLieHom φ)).toLinearMap
      (F.frozenMarkedLeftOrbit G w S hS marked center).log = marked.log := by
  have h := (F.frozenMarked_factors_mark G w φ hφ S hS hsection
    (G.realification.polynomialOrbitCoordinates w marked)
    (G.realification.polynomialOrbitCoordinates w marked) center center hcenter hcenter).1
  exact congrArg (fun q : (G.realification.adaptedPolynomialFiltration w).Group =>
    (q.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M))) h

theorem frozenMarkedRightOrbit_formal_mark
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group)
    (hcenter : realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ center = 1) :
    map (realLieHomToRat (realificationLieHom φ)).toLinearMap
      (F.frozenMarkedRightOrbit G w S hS marked center).log = marked.log := by
  have h := (F.frozenMarked_factors_mark G w φ hφ S hS hsection
    (G.realification.polynomialOrbitCoordinates w marked)
    (G.realification.polynomialOrbitCoordinates w marked) center center hcenter hcenter).2
  exact congrArg (fun q : (G.realification.adaptedPolynomialFiltration w).Group =>
    (q.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M))) h

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ η L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {v : η → ℕ}

theorem observable_frozenMarked_outerOrbits
    (test : D.Niltest v) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ D.filtration.layer j)
    (hsection : Function.RightInverse S φ)
    (g E P R : (D.filtration.realification.adaptedPolynomialFiltration v).Group)
    (hfac : E * P * R = g)
    (EF RF : (G.realification.adaptedPolynomialFiltration v).Group)
    (w : σ → ℕ) (leftMark rightMark : G.realification.PolynomialOrbit w)
    (kE kR : D.RealGroup)
    (hkE : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ kE = 1)
    (hkR : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ kR = 1)
    (x : η → ℝ) (y : σ → ℝ)
    (hleft : G.adaptedPolynomialRealValueHom v x EF =
      G.realification.polynomialOrbitRealEval w y leftMark)
    (hright : G.adaptedPolynomialRealValueHom v x RF =
      G.realification.polynomialOrbitRealEval w y rightMark)
    (hcoset : (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom v x
      ((D.filtration.filteredRealPolynomialSection G v S hS RF)⁻¹ * R)) : D.Space) =
        QuotientGroup.mk kR) :
    letI := rightMetricSpace
      (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
    ‖test.observable (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom v x g)) -
      test.observable (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitRealEval w y
            (D.filtration.frozenMarkedLeftOrbit G w S hS leftMark kE) *
          D.filtration.adaptedPolynomialRealValueHom v x P *
          D.filtration.realification.polynomialOrbitRealEval w y
            (D.filtration.frozenMarkedRightOrbit G w S hS rightMark kR)))‖ ≤
      (test.lipBound : ℝ) * dist
        (D.filtration.adaptedPolynomialRealValueHom v x
          (E * (D.filtration.filteredRealPolynomialSection G v S hS EF)⁻¹)) kE := by
  rw [D.filtration.frozenMarkedLeftOrbit_realEval_eq_local G w S hS leftMark kE v EF x y hleft,
    D.filtration.frozenMarkedRightOrbit_realEval_eq_local G w S hS rightMark kR v RF x y hright,
    ← map_mul, ← map_mul]
  exact test.observable_frozenMarked_polynomial_factors G φ S hS hsection
    g E P R hfac EF RF kE kR hkE hkR x hcoset

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_frozenMarkedLeftOrbit_exp_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ ι κ L M : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
        [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
        {t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
        (b : Basis ι ℚ L) (c : Basis κ ℚ M) (w : σ → ℕ) (S : M →ₗ[ℚ] L)
        (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j) (H HS : ℕ) (p : ℝ),
        0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
        (H : ℝ) ≤ Real.exp p → (HS : ℝ) ≤ Real.exp p →
        (∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H) →
        (∀ i j, RationalHeightLE (LinearMap.toMatrix c b S i j) HS) →
        ∀ (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group)
          (x : σ → ℤ),
          (∀ i, |(c.baseChange ℝ).repr
            (G.realification.polynomialOrbitEval w x marked).coord i| ≤ Real.exp p) →
          (∀ i, |(b.baseChange ℝ).repr center.coord i| ≤ Real.exp p) →
          ∀ i, |(b.baseChange ℝ).repr
            (F.realification.polynomialOrbitEval w x
              (F.frozenMarkedLeftOrbit G w S hS marked center)).coord i| ≤
                Real.exp ((p + C) ^ C) := by
  obtain ⟨C, hC, hproduct⟩ := exists_bch_fixed_product_exp_bound s 2 2
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L M _ _ _ _ _ _ _ t F G b c w S hS H HS p hp hd hdmark hH hHS hb hSheight
    marked center x hmarked hcenter i
  have hmarkedNorm :
      ‖(c.baseChange ℝ).equivFun
        (G.realification.polynomialOrbitEval w x marked).coord‖ ≤ Real.exp p := by
    apply (pi_norm_le_iff_of_nonneg (Real.exp_nonneg p)).mpr
    intro j
    simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using hmarked j
  have hdim : (Fintype.card κ : ℝ) + 1 ≤ Real.exp p := by
    linarith [Real.add_one_le_exp p]
  have hheight : (HS : ℝ) + 1 ≤ Real.exp (p + 1) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp p * 2 := by linarith [Real.one_le_exp hp]
      _ ≤ Real.exp p * Real.exp 1 :=
        mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg p)
      _ = _ := (Real.exp_add _ _).symm
  have hsectionNorm :
      ‖(b.baseChange ℝ).equivFun
        (S.baseChange ℝ (G.realification.polynomialOrbitEval w x marked).coord)‖ ≤
          Real.exp ((p + 2) ^ 2) := by
    apply (realified_linear_coordinate_norm c b S hSheight _).trans
    calc
      _ ≤ (Real.exp p * Real.exp (p + 1)) * Real.exp p :=
        mul_le_mul (mul_le_mul hdim hheight (by positivity) (Real.exp_nonneg p))
          hmarkedNorm (norm_nonneg _) (by positivity)
      _ = Real.exp (3 * p + 1) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
  let sectionValue : F.realification.Group :=
    ⟨S.baseChange ℝ (G.realification.polynomialOrbitEval w x marked).coord⟩
  have hsection (j : ι) :
      |(b.baseChange ℝ).repr sectionValue.coord j| ≤ Real.exp ((p + 2) ^ 2) := by
    have hj := norm_le_pi_norm ((b.baseChange ℝ).equivFun sectionValue.coord) j
    have hj' : |(b.baseChange ℝ).repr sectionValue.coord j| ≤
        ‖(b.baseChange ℝ).equivFun sectionValue.coord‖ := by
      simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using hj
    exact hj'.trans hsectionNorm
  have hcenter' (j : ι) :
      |(b.baseChange ℝ).repr center.coord j| ≤ Real.exp ((p + 2) ^ 2) :=
    (hcenter j).trans (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p]))
  have hbound := hproduct (b.baseChange ℝ) (lieStructureConstants b) H p
    F.realification.lowerCentralSeries_eq_bot [center, sectionValue]
    (fun j k z => (realLieBasis_structure b j k z).symm) hp hd (by simp) hH hb
    (by
      intro a ha j
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact hcenter' j
      · exact hsection j) i
  rw [← polynomialOrbitRealEval_integer, frozenMarkedLeftOrbit_realEval,
    polynomialOrbitRealEval_integer]
  simpa only [List.prod_cons, List.prod_nil, mul_one] using hbound

end Erdos3.NilpotentLieFiltration

end

end OAI
