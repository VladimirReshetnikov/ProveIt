import OAI.Combinatorics.Progressions.Estimates.NativeFiniteMarkedFreezing
import OAI.Combinatorics.Progressions.Estimates.UniformFiniteMarkedFactorParameters

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold
open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

def FiniteMarkedPolynomialFreezing
    {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (l : ℕ) (Tbox : σ → ℝ) (A ε B : ℝ) : Prop :=
  ∃ N Q M m n : ℕ, 0 < N ∧ 0 < Q ∧ 0 < M ∧ 0 < m ∧ 0 < n ∧
    (Fintype.card (Fin d → Fin (N + 1)) : ℝ) ≤ B ∧
    (Fintype.card (σ → Fin (Q + 1)) : ℝ) ≤ B ∧
    (M : ℝ) ≤ B ∧ (m : ℝ) ≤ B ∧ (n : ℝ) ≤ B ∧
    (Fintype.card ((Fin d → Fin (N + 1)) × Fin n) : ℝ) ≤ B ^ 2 ∧
    ∃ (left : (Fin d → Fin (N + 1)) → D.RealGroup) (right : Fin n → D.RealGroup),
      (∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) φ (left j) = 1 ∧
        ∀ i, |(D.basis.baseChange ℝ).repr (left j).coord i| ≤ B) ∧
      (∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) φ (right j) = 1 ∧
        (∀ i, |(D.basis.baseChange ℝ).repr (right j).coord i| ≤ B) ∧
        (D.basis.baseChange ℝ).equivFun (right j).coord ∈ realDenominatorGrid m) ∧
      ∀ (E : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (EF : (F.realification.adaptedPolynomialFiltration w).Group)
        (R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (RF : (F.realification.adaptedPolynomialFiltration w).Group),
        D.filtration.PolynomialSlowBound D.basis w Tbox A E →
        F.PolynomialSlowBound c w Tbox A EF →
        D.filtration.PolynomialRationalGrid D.basis w l R →
        F.PolynomialRationalGrid c w l RF →
        D.filtration.realPolynomialGroupMap F φ hφ w E = EF →
        D.filtration.realPolynomialGroupMap F φ hφ w R = RF →
        ∃ (leftLabel : (σ → Fin (Q + 1)) → (Fin d → Fin (N + 1)))
          (rightLabel : (σ → ZMod M) → Fin n),
          (∀ i j,
            D.filtration.realPolynomialGroupMap F φ hφ w
              (D.filtration.frozenMarkedLeft F w S hS EF (left i)) = EF ∧
            D.filtration.realPolynomialGroupMap F φ hφ w
              (D.filtration.frozenMarkedRight F w S hS RF (right j)) = RF) ∧
          ∀ (test : D.Niltest w)
            (g P : (D.filtration.realification.adaptedPolynomialFiltration w).Group),
            E * P * R = g →
            ∀ j (x : σ → ℤ), (∀ i, |(x i : ℝ)| ≤ Tbox i) →
              (∀ i, |(x i : ℝ) - normalizedRealBoxGrid Tbox Q j i| ≤ Tbox i * (2 / Q)) →
              ‖test.observable (QuotientGroup.mk
                  (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) g)) -
                test.observable (QuotientGroup.mk
                  (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ))
                    (D.filtration.frozenMarkedLeft F w S hS EF (left (leftLabel j)) * P *
                      D.filtration.frozenMarkedRight F w S hS RF
                        (right (rightLabel (fun i => (x i : ZMod M)))))))‖ ≤
                (test.lipBound : ℝ) * ε

theorem finiteMarkedPolynomialFreezing_of_factors
    {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (hsection : Function.RightInverse S φ)
    (l : ℕ) (Tbox : σ → ℝ) (A ε B : ℝ)
    (hrat : D.FiniteMarkedRationalFactorFreezing F c φ hφ w S hS l B)
    (hslow : D.MarkedSlowFactorFreezing F c φ hφ w S hS Tbox A ε B) :
    D.FiniteMarkedPolynomialFreezing F c φ hφ w S hS l Tbox A ε B := by
  obtain ⟨N, Q, hN, hQ, hNc, hQc, left, hlmark, hlcap, hl⟩ := hslow
  obtain ⟨M, m, n, hM, hm, hn, hMb, hmb, hnb, right, hr, hright⟩ := hrat
  have hB0 : 0 ≤ B := (Nat.cast_nonneg n).trans hnb
  have hpair : (Fintype.card ((Fin d → Fin (N + 1)) × Fin n) : ℝ) ≤ B ^ 2 := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two] using
      mul_le_mul hNc hnb (Nat.cast_nonneg n) hB0
  refine ⟨N, Q, M, m, n, hN, hQ, hM, hm, hn, hNc, hQc, hMb, hmb, hnb, hpair,
    left, right, fun j => ⟨hlmark j, hlcap j⟩, hr, ?_⟩
  intro E EF R RF hE hEF hR hRF hEmark hRmark
  obtain ⟨leftLabel, hleftLabel⟩ := hl E EF hE hEF hEmark
  obtain ⟨rightLabel, hrightLabel⟩ := hright R RF hR hRF hRmark
  refine ⟨leftLabel, rightLabel, ?_, ?_⟩
  · intro i j
    exact D.filtration.frozenMarked_factors_mark F w φ hφ S hS hsection EF RF
      (left i) (right j) (hlmark i) (hr j).1
  · intro test g P hfac j x hx hj
    obtain ⟨γ, hγ, hKR, _⟩ := hrightLabel x
    have hcoset : (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
        (fun i => (x i : ℝ))
        ((D.filtration.filteredRealPolynomialSection F w S hS RF)⁻¹ * R)) : D.Space) =
        QuotientGroup.mk (right (rightLabel (fun i => (x i : ZMod M)))) := by
      rw [hKR]
      exact QuotientGroup.mk_mul_of_mem _ hγ
    exact (test.observable_frozenMarked_polynomial_factors F φ S hS hsection g E P R hfac
      EF RF (left (leftLabel j)) (right (rightLabel (fun i => (x i : ZMod M))))
      (hlmark _) (hr _).1 (fun i => (x i : ℝ)) hcoset).trans
        (mul_le_mul_of_nonneg_left (hleftLabel j _ hx hj) (NNReal.coe_nonneg _))

theorem exists_uniform_finite_marked_polynomial_freezing (s a u : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
      (ω : Fin d → ℕ)
      (_hDlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (τ : κ → ℕ) (_hFlayers : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j),
      (∀ j, ∀ y ∈ F.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ w : σ → ℕ, (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∃ (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j),
        Function.RightInverse S φ ∧
        (∀ i j, RationalHeightLE (D.basis.repr (S (c j)) i)
          (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)) ∧
        ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
          ∀ Tbox : σ → ℝ, (∀ i, 0 < Tbox i) →
            D.FiniteMarkedPolynomialFreezing F c φ hφ w S hS l Tbox
              (Real.exp ((p + 2) ^ a)) (Real.exp (-((p + 2) ^ u)))
              (Real.exp ((p + C) ^ C)) := by
  obtain ⟨C, hC, hparams⟩ := exists_uniform_finite_marked_factor_parameters s a u
  refine ⟨C, hC, ?_⟩
  intro σ κ L T _ _ _ _ _ _ _ _ _ _ _ d t D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  obtain ⟨S, hS, hright, hSb, hboth⟩ := hparams D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  refine ⟨S, hS, hright, hSb, ?_⟩
  intro l hl hlp Tbox hT
  obtain ⟨hrat, hslow⟩ := hboth l hl hlp Tbox hT
  exact D.finiteMarkedPolynomialFreezing_of_factors F c φ hφ w S hS hright l Tbox
    _ _ _ hrat hslow

end Erdos3.RationalFilteredNilmanifold

end

end OAI
