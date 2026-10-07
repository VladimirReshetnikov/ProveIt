import OAI.Combinatorics.Progressions.Estimates.NativeOrbitOuterControl
import OAI.Combinatorics.Progressions.Lattices.AuxiliaryResidueLocalization
import OAI.Combinatorics.Progressions.Lattices.ResidueStrideRebase
import OAI.Combinatorics.Progressions.Polynomial.UniformPolynomialPeriodBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem complex_expect_error_le {X : Type*} (A : Finset X) (f g : X → ℂ)
    {η : ℝ} (hη : 0 ≤ η) (herr : ∀ x ∈ A, ‖f x - g x‖ ≤ η) :
    ‖(𝔼 x ∈ A, f x) - (𝔼 x ∈ A, g x)‖ ≤ η := by
  rw [← Finset.expect_sub_distrib]
  by_cases hA : A.Nonempty
  · exact (RCLike.norm_expect_le (K := ℂ)).trans
      ((Finset.expect_le_expect herr).trans_eq (Finset.expect_const hA η))
  · have he := Finset.not_nonempty_iff_eq_empty.mp hA
    simpa only [he, Finset.expect_empty, norm_zero] using hη

theorem complex_discrepancy_after_freezing {X Y : Type*} (A : Finset X) (B : Finset Y)
    (f f₀ : X → ℂ) (g g₀ : Y → ℂ) {η₀ η₁ : ℝ} (hη₀ : 0 ≤ η₀) (hη₁ : 0 ≤ η₁)
    (hf : ∀ x ∈ A, ‖f x - f₀ x‖ ≤ η₀) (hg : ∀ y ∈ B, ‖g y - g₀ y‖ ≤ η₁) :
    ‖(𝔼 x ∈ A, f x) - (𝔼 y ∈ B, g y)‖ - η₀ - η₁ ≤
      ‖(𝔼 x ∈ A, f₀ x) - (𝔼 y ∈ B, g₀ y)‖ := by
  have hf' := complex_expect_error_le A f f₀ hη₀ hf
  have hg' := complex_expect_error_le B g g₀ hη₁ hg
  have h₁ := norm_sub_le_norm_sub_add_norm_sub (𝔼 x ∈ A, f x) (𝔼 x ∈ A, f₀ x) (𝔼 y ∈ B, g y)
  have h₂ := norm_sub_le_norm_sub_add_norm_sub (𝔼 x ∈ A, f₀ x) (𝔼 y ∈ B, g₀ y) (𝔼 y ∈ B, g y)
  rw [norm_sub_rev (𝔼 y ∈ B, g₀ y) (𝔼 y ∈ B, g y)] at h₂
  linarith

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem polynomialRationalGrid_uniform_cosets {σ L : Type*} [Fintype σ]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (q : ℕ) (hq : 0 < q)
    (g : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (hg : D.filtration.PolynomialRationalGrid D.basis w q g) (x y : σ → ℤ)
    (hxy : ∀ j, (uniformPolynomialBCHPeriod (σ := σ) D.basis s s D.grid q : ℤ) ∣ x j - y j) :
    let f := fun z : σ → ℤ => D.filtration.adaptedPolynomialRealValueHom w (fun j => (z j : ℝ)) g
    ((QuotientGroup.mk (f x) : D.Space) = QuotientGroup.mk (f y)) ∧
    ((QuotientGroup.mk (f x)⁻¹ : D.Space) = QuotientGroup.mk (f y)⁻¹) := by
  obtain ⟨P, hdegree, hden, hval⟩ :=
    D.filtration.polynomialRationalGrid_exists_coordinates D.basis w hw q hq g hg
  dsimp only
  rw [← hval (fun j => (x j : ℝ)), ← hval (fun j => (y j : ℝ))]
  exact realPolynomialBCHMap_uniform_cosets D.basis D.filtration.lowerCentralSeries_eq_bot
    D.lattice s D.grid q P hdegree hden D.inner_grid x y hxy

theorem exists_native_rational_period (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : (D.filtration.realification.adaptedPolynomialFiltration w).Group,
          D.filtration.PolynomialRationalGrid D.basis w q g →
          let f := fun z : σ → ℤ => D.filtration.adaptedPolynomialRealValueHom w (fun j => (z j : ℝ)) g
          ∀ x y : σ → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
            ((QuotientGroup.mk (f x) : D.Space) = QuotientGroup.mk (f y)) ∧
            ((QuotientGroup.mk (f x)⁻¹ : D.Space) = QuotientGroup.mk (f y)⁻¹) := by
  obtain ⟨a, _, hperiod⟩ := exists_uniformPolynomialBCHPeriod_exp_bound s s
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + 1 + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ d D w hw p hp hD hσ q hq hqp
  let M := uniformPolynomialBCHPeriod (σ := σ) D.basis s s D.grid q
  have hpp : p ≤ p + 1 := le_add_of_nonneg_right zero_le_one
  have hb := hperiod (σ := σ) D.basis D.grid ⌈Real.exp p⌉₊ q (p + 1)
    (by linarith) (by simpa only [Fintype.card_fin] using hD.1.trans hpp) (hσ.trans hpp)
    (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr hpp))
    (hqp.trans (Real.exp_le_exp.mpr hpp))
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
  have hMb : (M : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    apply hb.trans (Real.exp_le_exp.mpr _)
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨M, uniformPolynomialBCHPeriod_pos D.basis s s D.grid q D.grid_pos hq, hMb,
    fun g hg x y hxy => D.polynomialRationalGrid_uniform_cosets w hw q hq g hg x y hxy⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_slow_factor_freezing (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (p : ℝ), 0 ≤ p → (Fintype.card σ : ℝ) ≤ p →
      ∀ S : D.Niltest w, S.ComplexityLE p →
      ∀ (E b R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (κ : D.RealGroup), κ ∈ D.realLattice →
        E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ =
          ⟨⟨S.orbit.log, S.orbit.property⟩⟩ →
        ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
          D.filtration.PolynomialSlowBound D.basis w T (Real.exp ((p + 2) ^ r)) E →
          ∀ (x : σ → ℤ) (z : σ → ℝ) (r₀ : D.RealGroup) (δ : ℝ), 0 ≤ δ →
            (∀ i, |(x i : ℝ)| ≤ T i) → (∀ i, |z i| ≤ T i) →
            (∀ i, |(x i : ℝ) - z i| ≤ T i * δ) →
            (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
              (fun i => (x i : ℝ)) R) : D.Space) = QuotientGroup.mk r₀ →
            ‖S.eval x - S.observable (QuotientGroup.mk
              (D.filtration.adaptedPolynomialRealValueHom w z E *
                D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) b * r₀))‖ ≤
              Real.exp ((p + C) ^ C) * δ := by
  obtain ⟨a, _, hmove⟩ := exists_polynomialSlowBound_dist_exp s r
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Polynomial.X + (Polynomial.X + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D w hw p hp hσ S hS E b R κ hκ hprod T hT hE x z r₀ δ hδ hx hz hxz hR
  have hdist := hmove D w hw p hp hS.1 hσ T hT E hE
    (fun i => (x i : ℝ)) z δ hδ hx hz hxz
  have hfreeze := S.eval_freeze_of_lattice_factorization E b R κ hκ hprod x
    (D.filtration.adaptedPolynomialRealValueHom w z E) r₀ hS hR hdist
  apply hfreeze.trans
  rw [← mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr _) hδ
  simpa [Polynomial.eval₂_pow] using hbudget p hp

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_anchored_factor_freezing (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ p : ℝ, 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
      ∀ S : D.Niltest w, S.ComplexityLE p →
      ∀ (E b R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (κ : D.RealGroup), κ ∈ D.realLattice →
        E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ =
          ⟨⟨S.orbit.log, S.orbit.property⟩⟩ →
        D.filtration.PolynomialRationalGrid D.basis w q R →
        ∀ A : σ → ℝ, (∀ i, 0 < A i) →
          D.filtration.PolynomialSlowBound D.basis w A (Real.exp ((p + 2) ^ a)) E →
          ∀ z : σ → ℤ, (∀ i, |(z i : ℝ)| ≤ A i) →
            let l₀ := D.filtration.adaptedPolynomialRealValueHom w (fun i => (z i : ℝ)) E
            let r₀ := D.filtration.adaptedPolynomialRealValueHom w (fun i => (z i : ℝ)) R
            (∀ i, |(D.basis.baseChange ℝ).repr l₀.coord i| ≤ Real.exp ((p + 2) ^ C)) ∧
            (D.basis.baseChange ℝ).equivFun r₀.coord ∈ realDenominatorGrid q ∧
            ∀ (x : σ → ℤ) (δ : ℝ), 0 ≤ δ →
              (∀ i, |(x i : ℝ)| ≤ A i) → (∀ i, (P : ℤ) ∣ x i - z i) →
              (∀ i, |(x i : ℝ) - (z i : ℝ)| ≤ A i * δ) →
              ‖S.eval x - S.observable (QuotientGroup.mk
                (l₀ * D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) b * r₀))‖ ≤
                Real.exp ((p + 2) ^ C) * δ := by
  obtain ⟨u, _, hperiod⟩ := exists_native_rational_period s
  obtain ⟨v, _, hfreeze⟩ := exists_slow_factor_freezing s a
  let X : Polynomial ℕ := Polynomial.X
  let B := Polynomial.C s * (X + 1) + (X + 2) ^ a +
    (X + Polynomial.C u) ^ u + (X + Polynomial.C v) ^ v
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget B
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D w hw p hp hD hσ q hq hqp
  have hsum : (s : ℝ) * (p + 1) + (p + 2) ^ a + (p + u) ^ u + (p + v) ^ v ≤
      (p + 2) ^ C := by
    simpa [B, X, Polynomial.eval₂_pow] using hbudget p hp
  have hcoord : (s : ℝ) * (p + 1) + (p + 2) ^ a ≤ (p + 2) ^ C := by
    nlinarith [pow_nonneg (by positivity : 0 ≤ p + (u : ℝ)) u,
      pow_nonneg (by positivity : 0 ≤ p + (v : ℝ)) v]
  have hu : (p + u) ^ u ≤ (p + 2) ^ C := by
    nlinarith [pow_nonneg (by positivity : 0 ≤ p + 2) a,
      pow_nonneg (by positivity : 0 ≤ p + (v : ℝ)) v, Nat.cast_nonneg (α := ℝ) s]
  have hv : (p + v) ^ v ≤ (p + 2) ^ C := by
    nlinarith [pow_nonneg (by positivity : 0 ≤ p + 2) a,
      pow_nonneg (by positivity : 0 ≤ p + (u : ℝ)) u, Nat.cast_nonneg (α := ℝ) s]
  obtain ⟨P, hP, hPb, hcoset⟩ := hperiod D w hw p hp hD hσ q hq hqp
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hu), ?_⟩
  intro S hS E b R κ hκ hprod hgrid A hA hE z hz l₀ r₀
  refine ⟨?_, D.filtration.polynomialRationalGrid_value D.basis w q R hgrid z, ?_⟩
  · intro i
    have hzbound := D.filtration.polynomialSlowBound_value D.basis w hw A hA
      (Real.exp_nonneg _) E hE (fun j => (z j : ℝ)) hz i
    have hn1 : (Fintype.card σ : ℝ) + 1 ≤ Real.exp p := by
      linarith [Real.add_one_le_exp p]
    apply hzbound.trans
    calc
      _ ≤ Real.exp s * (Real.exp p) ^ s * Real.exp ((p + 2) ^ a) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (Real.add_one_le_exp (s : ℝ))
            (pow_le_pow_left₀ (by positivity) hn1 _) (by positivity) (Real.exp_nonneg _))
          (Real.exp_nonneg _)
      _ = Real.exp ((s : ℝ) * (p + 1) + (p + 2) ^ a) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hcoord
  · intro x δ hδ hx hcongr hdist
    have hb := hfreeze D w hw p hp hσ S hS E b R κ hκ hprod A hA hE
      x (fun i => (z i : ℝ)) r₀ δ hδ hx hz hdist (hcoset R hgrid x z hcongr).1
    exact hb.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hv) hδ)

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

theorem exists_auxiliary_frozen_discrepancy (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ p : ℝ, 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ (P : ℕ) (hP : 0 < P), (P : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
      ∀ S : D.Niltest w, S.ComplexityLE p → S.UnitIntervalValued →
      ∀ (E b R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (κ : D.RealGroup), κ ∈ D.realLattice →
        E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ =
          ⟨⟨S.orbit.log, S.orbit.property⟩⟩ →
        D.filtration.PolynomialRationalGrid D.basis w q R →
        ∀ A : σ → ℝ, (∀ i, 0 < A i) →
          D.filtration.PolynomialSlowBound D.basis w A (Real.exp ((p + 2) ^ a)) E →
          ∀ (M : ℕ) (hM : 0 < M) (lo : σ → ℤ) (N H : σ → ℕ)
            (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i) (u v : σ → ℤ) (J : σ → ℕ),
            (∀ i, 0 < J i) → ∀ (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]),
            (∀ i, (M * (M * P)).Coprime (J i)) →
            ∀ (δ ε : ℝ), 0 ≤ δ → ε < 1 / 2 →
            (∀ i, 2 * (H i : ℝ) ≤ (M : ℝ) * A i * δ) →
            (∀ i, (u i : ℝ) - (M : ℝ) * A i ≤ (lo i : ℝ) ∧
              (lo i : ℝ) + (N i : ℝ) ≤ (u i : ℝ) + (M : ℝ) * A i) →
            (∑ i, ((Nat.lcm M (M * P) * J i : ℕ) : ℝ) / (H i : ℝ)) ≤ ε →
            let Q := comparableBoxPartitions N H hH hHN
            let c₀ := baseAuxiliaryBoxCell lo N Q (fun _ => M) (fun _ => M * P)
              (fun _ => Nat.mul_pos hM hP) u
            let c₁ := refinedAuxiliaryBoxCell lo N Q (fun _ => M) (fun _ => M * P) J
              (fun _ => Nat.mul_pos hM hP) u v hv
            let F : IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) u → ℂ :=
              residueBoxStrideValue S.eval u M
            let G : IntegerResidueBox lo (fun i => lo i + N i) (fun i => (M * J i : ℕ)) v → ℂ :=
              residueBoxStrideValue S.eval u M
            ∃ k : AuxiliaryBoxLabels Q (fun _ => M) (fun _ => M * P) u,
              0 < (partitionCell c₀ k).card ∧ 0 < (partitionCell c₁ k).card ∧
              ∃ l₀ r₀ : D.RealGroup,
                (∀ i, |(D.basis.baseChange ℝ).repr l₀.coord i| ≤ Real.exp ((p + 2) ^ C)) ∧
                (D.basis.baseChange ℝ).equivFun r₀.coord ∈ realDenominatorGrid q ∧
                let T : (σ → ℤ) → ℂ := fun x => S.observable (QuotientGroup.mk
                  (l₀ * D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) b * r₀))
                ‖(𝔼 x, F x) - (𝔼 x, G x)‖ - 8 * ε - 2 * (Real.exp ((p + 2) ^ C) * δ) ≤
                  ‖(𝔼 x ∈ partitionCell c₀ k, residueBoxStrideValue T u M x) -
                    (𝔼 x ∈ partitionCell c₁ k, residueBoxStrideValue T u M x)‖ := by
  obtain ⟨C, hC, hanchor⟩ := exists_anchored_factor_freezing s a
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ _ d D w hw p hp hD hσ q hq hqp
  obtain ⟨P, hP, hPb, hfreeze⟩ := hanchor D w hw p hp hD hσ q hq hqp
  refine ⟨P, hP, hPb, ?_⟩
  intro S hS hunit E b R κ hκ hprod hgrid A hA hE M hM lo N H hH hHN u v J hJ hv hcop
    δ ε hδ hε hsize hphysical hsmall Q c₀ c₁ F G
  have hG : ∀ x, ‖G x‖ ≤ 1 := fun x => hunit.norm_le_one _
  obtain ⟨k, hk₀, hk₁, hgap⟩ := exists_auxiliary_residue_piece lo N H hH hHN
    (fun _ => M) (fun _ => M * P) J (fun _ => hM) (fun _ => Nat.mul_pos hM hP) hJ
    u v hv hcop hε hsmall F G hG
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hk₀
  have hzb := residueBox_stride_bound lo N M hM u (fun _ => (M : ℤ)) u
    (fun _ _ hx => hx) A hphysical z
  let z₀ := commonStrideIndex u M (fun i => (z i).val)
  let l₀ := D.filtration.adaptedPolynomialRealValueHom w (fun i => (z₀ i : ℝ)) E
  let r₀ := D.filtration.adaptedPolynomialRealValueHom w (fun i => (z₀ i : ℝ)) R
  obtain ⟨hl₀, hr₀, hpoint⟩ := hfreeze S hS E b R κ hκ hprod hgrid A hA hE z₀ hzb
  refine ⟨k, hk₀, hk₁, l₀, r₀, hl₀, hr₀, ?_⟩
  intro T
  have hstep : ∀ i j, (Q i).step j = 1 := comparableBoxPartitions_step N H hH hHN
  have hwidth : ∀ i, ((Q i).length (k i).1 : ℝ) ≤ (M : ℝ) * A i * δ := by
    intro i
    have hlen : ((Q i).length (k i).1 : ℝ) < 2 * (H i : ℝ) := by
      exact_mod_cast (comparableBoxPartitions_length N H hH hHN i (k i).1).2
    exact hlen.le.trans (hsize i)
  have hnear₀ : ∀ x ∈ partitionCell c₀ k,
      ‖F x - residueBoxStrideValue T u M x‖ ≤ Real.exp ((p + 2) ^ C) * δ := by
    intro x hx
    have hgeom := auxiliaryPiece_stride_geometry lo N Q hstep M P hM hP
      u (fun _ => (M : ℤ)) u (fun _ _ he => he) k x z hx hz A δ hwidth
    have hxb := residueBox_stride_bound lo N M hM u (fun _ => (M : ℤ)) u
      (fun _ _ he => he) A hphysical x
    exact hpoint (commonStrideIndex u M (fun i => (x i).val)) δ hδ hxb hgeom.1 hgeom.2
  have hnear₁ : ∀ x ∈ partitionCell c₁ k,
      ‖G x - residueBoxStrideValue T u M x‖ ≤ Real.exp ((p + 2) ^ C) * δ := by
    intro x hx
    have hgeom := auxiliaryPiece_stride_geometry lo N Q hstep M P hM hP
      u (fun i => (M * J i : ℕ)) v
      (fun i => refinedResidue_implies_base M (J i) (u i) (v i) (hv i)) k x z hx hz A δ hwidth
    have hxb := residueBox_stride_bound lo N M hM u (fun i => (M * J i : ℕ)) v
      (fun i => refinedResidue_implies_base M (J i) (u i) (v i) (hv i)) A hphysical x
    exact hpoint (commonStrideIndex u M (fun i => (x i).val)) δ hδ hxb hgeom.1 hgeom.2
  have hη : 0 ≤ Real.exp ((p + 2) ^ C) * δ := mul_nonneg (Real.exp_nonneg _) hδ
  have herr := complex_discrepancy_after_freezing (partitionCell c₀ k) (partitionCell c₁ k)
    F (residueBoxStrideValue T u M) G (residueBoxStrideValue T u M) hη hη hnear₀ hnear₁
  linarith

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

theorem polynomialOrbitCoordinates_realValue {σ L : Type*}
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ} (F : NilpotentLieFiltration L s)
    (w : σ → ℕ) (g : F.realification.PolynomialOrbit w) (x : σ → ℤ) :
    F.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ))
        (F.realification.polynomialOrbitCoordinates w g) =
      F.realification.polynomialOrbitEval w x g := by
  apply NilpotentLieBCHGroup.ext
  change eval₂ (fun i => (x i : ℝ)) g.log = eval (fun i => (x i : ℚ)) g.log
  simpa only [map_intCast] using
    (eval₂_algebraMap (S := ℝ) (fun i => (x i : ℚ)) g.log)

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold

theorem exists_native_orbit_rational_period (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : D.filtration.realification.PolynomialOrbit w,
          CoefficientGrid (D.basis.baseChange ℝ) q g.log →
          ∀ x y : σ → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
            ((QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g) : D.Space) =
              QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w y g)) ∧
            ((QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g)⁻¹ : D.Space) =
              QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w y g)⁻¹) := by
  obtain ⟨C, hC, hperiod⟩ := exists_native_rational_period s
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ d D w hw p hp hD hσ q hq hqp
  obtain ⟨M, hM, hMp, hsolve⟩ := hperiod D w hw p hp hD hσ q hq hqp
  refine ⟨M, hM, hMp, ?_⟩
  intro g hg x y hxy
  have hgrid := (D.filtration.polynomialRationalGrid_iff_formal D.basis w q
    (D.filtration.realification.polynomialOrbitCoordinates w g)).mpr hg
  have h := hsolve (D.filtration.realification.polynomialOrbitCoordinates w g) hgrid x y hxy
  simpa only [D.filtration.polynomialOrbitCoordinates_realValue] using h

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_orbit_local_control (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      {D : RationalFilteredNilmanifold L s d}
      {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
      {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
      (R : NativePolynomialOrbitFactors D g eta A p),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p → (∀ i, 0 < A i) →
      ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (∀ x y : σ → ℤ, (∀ i, (P : ℤ) ∣ x i - y i) →
          ((QuotientGroup.mk (R.rationalValue x) : D.Space) = QuotientGroup.mk (R.rationalValue y)) ∧
          ((QuotientGroup.mk (R.rationalValue x)⁻¹ : D.Space) = QuotientGroup.mk (R.rationalValue y)⁻¹)) ∧
        (letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
          (D.basis.baseChange ℝ)
         ∀ (x y : σ → ℤ) (δ : ℝ), 0 ≤ δ →
           (∀ i, |(x i : ℝ)| ≤ A i) → (∀ i, |(y i : ℝ)| ≤ A i) →
           (∀ i, |(x i : ℝ) - (y i : ℝ)| ≤ A i * δ) →
           dist (R.slowValue x) (R.slowValue y) ≤ Real.exp ((p + C) ^ C) * δ) := by
  obtain ⟨a, _, hcoeff⟩ := exists_native_orbit_coefficient_control
  obtain ⟨b, _, hperiod⟩ := exists_native_rational_period s
  obtain ⟨c, _, hmetric⟩ := exists_polynomialSlowBound_dist_exp s 1
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + Polynomial.C a) ^ a + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Q + Polynomial.C b) ^ b + (Q + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D g eta A p R hp hD hσ hA
  obtain ⟨m, hm, hmb, hgrid, hslow⟩ := hcoeff R hp hD hA
  let q := p + (p + a) ^ a + 2
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have haq : (p + a) ^ a ≤ q := by dsimp [q]; linarith
  have hsum : (q + b) ^ b + (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hbC : (q + b) ^ b ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hcC : (q + c) ^ c ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity)).trans hsum
  obtain ⟨P, hP, hPb, hcosets⟩ := hperiod D (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    q hq (hD.mono D hpq) (hσ.trans hpq) m hm (hmb.trans (Real.exp_le_exp.mpr haq))
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hbC), hcosets R.rational hgrid, ?_⟩
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  intro x y δ hδ hx hy hxy
  have hs := D.filtration.polynomialSlowBound_mono D.basis (fun _ : σ => 1) A hA
    (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith : (p + a) ^ a ≤ (q + 2) ^ 1))
    R.slow hslow
  have hd := hmetric D (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) q hq (hD.mono D hpq)
    (hσ.trans hpq) A hA R.slow hs (fun i => (x i : ℝ)) (fun i => (y i : ℝ)) δ hδ hx hy hxy
  exact hd.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcC) hδ)

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_orbit_factor_freezing (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p →
      ∀ (Φ : D.Space → ℂ) (K : ℝ≥0), (∀ x, ‖Φ x‖ ≤ 1) →
      (letI := D.metricSpace; LipschitzWith K Φ) → (K : ℝ) ≤ Real.exp p →
      ∀ ε b γ g : D.filtration.realification.PolynomialOrbit w,
        ε * b * γ = g → ∀ T : σ → ℝ, (∀ i, 0 < T i) →
        CoefficientBound (D.basis.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) ε.log →
        ∀ (x y : σ → ℤ) (δ : ℝ), 0 ≤ δ →
        (∀ i, |(x i : ℝ)| ≤ T i) → (∀ i, |(y i : ℝ)| ≤ T i) →
        (∀ i, |(x i : ℝ) - y i| ≤ T i * δ) →
        (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x γ) : D.Space) =
          QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w y γ) →
        ‖Φ (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g)) -
          Φ (QuotientGroup.mk
            (D.filtration.realification.polynomialOrbitEval w y ε *
             D.filtration.realification.polynomialOrbitEval w x b *
             D.filtration.realification.polynomialOrbitEval w y γ))‖ ≤
          Real.exp ((p + C) ^ C) * δ := by
  obtain ⟨c, _, hmove⟩ := exists_polynomialSlowBound_dist_exp s a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Polynomial.X + (Polynomial.X + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D w hw p hp hD hσ Φ K hΦ hLip hK ε b γ g hprod T hT hε x y δ hδ hx hy hxy hγ
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let S : D.Niltest w := {
    orbit := g
    observable := Φ
    normBound := 1
    lipBound := K
    norm_le := hΦ
    lipschitz := hLip }
  have hslow := (D.filtration.polynomialSlowBound_iff_formal D.basis w T _
    (D.filtration.realification.polynomialOrbitCoordinates w ε)).mpr hε
  have hdist := hmove D w hw p hp hD hσ T hT
    (D.filtration.realification.polynomialOrbitCoordinates w ε) hslow
    (fun i => (x i : ℝ)) (fun i => (y i : ℝ)) δ hδ hx hy hxy
  simp only [D.filtration.polynomialOrbitCoordinates_realValue] at hdist
  have hfreeze := S.observable_freeze_factors
    (D.filtration.realification.polynomialOrbitEval w x ε)
    (D.filtration.realification.polynomialOrbitEval w y ε)
    (D.filtration.realification.polynomialOrbitEval w x b)
    (D.filtration.realification.polynomialOrbitEval w x γ)
    (D.filtration.realification.polynomialOrbitEval w y γ) hγ
  have hg : D.filtration.realification.polynomialOrbitEval w x g =
      D.filtration.realification.polynomialOrbitEval w x ε *
      D.filtration.realification.polynomialOrbitEval w x b *
      D.filtration.realification.polynomialOrbitEval w x γ := by
    rw [← hprod, map_mul, map_mul]
  rw [hg]
  apply hfreeze.trans
  have hcost : p + (p + c) ^ c ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  calc
    _ ≤ Real.exp p * (Real.exp ((p + c) ^ c) * δ) :=
      mul_le_mul hK hdist dist_nonneg (Real.exp_pos p).le
    _ = Real.exp (p + (p + c) ^ c) * δ := by rw [← mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcost) hδ

end Erdos3.RationalFilteredNilmanifold

end

end OAI
