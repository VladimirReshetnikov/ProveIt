import OAI.Combinatorics.Progressions.Polynomial.UniformFiniteMarkedPolynomialFreezing

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold
open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

def BoundedCellMarkedPolynomialFreezing
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
  ∃ N Q M m n : ℕ, 0 < N ∧ 0 < Q ∧ (Q : ℝ) ≤ max 1 B ∧ 0 < M ∧ 0 < m ∧ 0 < n ∧
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

theorem subdivisionCount_le_function_card {σ : Type*} [Fintype σ] [DecidableEq σ]
    [Nonempty σ] (Q : ℕ) : Q + 1 ≤ Fintype.card (σ → Fin (Q + 1)) := by
  classical
  have hinj : Function.Injective (fun a : Fin (Q + 1) => fun _ : σ => a) := by
    intro a b hab
    exact congrFun hab (Classical.choice inferInstance)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hinj

theorem FiniteMarkedPolynomialFreezing.bounded_cells
    {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {F : NilpotentLieFiltration T t} {c : Basis κ ℚ T} {φ : L →ₗ⁅ℚ⁆ T}
    {hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j}
    {w : σ → ℕ} {S : T →ₗ[ℚ] L}
    {hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j}
    {l : ℕ} {Tbox : σ → ℝ} {A ε B : ℝ}
    (h : D.FiniteMarkedPolynomialFreezing F c φ hφ w S hS l Tbox A ε B) :
    D.BoundedCellMarkedPolynomialFreezing F c φ hφ w S hS l Tbox A ε B := by
  obtain ⟨N, Q, M, m, n, hN, hQ, hM, hm, hn, hNc, hQc, hMb, hmb, hnb, hpair,
    left, right, hl, hr, hfreeze⟩ := h
  cases isEmpty_or_nonempty σ with
  | inr hne =>
    let : Nonempty σ := hne
    have hQb : (Q : ℝ) ≤ max 1 B := by
      have hQc' : ((Q + 1 : ℕ) : ℝ) ≤ B :=
        (Nat.cast_le.mpr (subdivisionCount_le_function_card (σ := σ) Q)).trans hQc
      exact (show (Q : ℝ) ≤ B by push_cast at hQc'; linarith).trans (le_max_right _ _)
    exact ⟨N, Q, M, m, n, hN, hQ, hQb, hM, hm, hn, hNc, hQc, hMb, hmb, hnb,
      hpair, left, right, hl, hr, hfreeze⟩
  | inl hempty =>
    let : IsEmpty σ := hempty
    have hone : (1 : ℝ) ≤ B :=
      (show (1 : ℝ) ≤ n by exact_mod_cast hn).trans hnb
    have hcard : (Fintype.card (σ → Fin (1 + 1)) : ℝ) ≤ B := by simpa using hone
    refine ⟨N, 1, M, m, n, hN, by omega, ?_, hM, hm, hn, hNc, hcard, hMb, hmb,
      hnb, hpair, left, right, hl, hr, ?_⟩
    · simpa only [Nat.cast_one] using le_max_left (1 : ℝ) B
    · intro E EF R RF hE hEF hR hRF hEproj hRproj
      obtain ⟨leftLabel, rightLabel, hmarks, herror⟩ := hfreeze E EF R RF
        hE hEF hR hRF hEproj hRproj
      let emptyCell : σ → Fin (Q + 1) := fun i => isEmptyElim i
      refine ⟨fun _ => leftLabel emptyCell, rightLabel, hmarks, ?_⟩
      intro test g P hfac j x hx hj
      exact herror test g P hfac emptyCell x hx (fun i => isEmptyElim i)

theorem exists_uniform_bounded_cell_marked_polynomial_freezing (s a u : ℕ) :
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
            D.BoundedCellMarkedPolynomialFreezing F c φ hφ w S hS l Tbox
              (Real.exp ((p + 2) ^ a)) (Real.exp (-((p + 2) ^ u)))
              (Real.exp ((p + C) ^ C)) := by
  obtain ⟨C, hC, hbase⟩ := exists_uniform_finite_marked_polynomial_freezing s a u
  refine ⟨C, hC, ?_⟩
  intro σ κ L T _ _ _ _ _ _ _ _ _ _ _ d t D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  obtain ⟨S, hS, hright, hSb, hfreeze⟩ := hbase D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  exact ⟨S, hS, hright, hSb, fun l hl hlp Tbox hT =>
    (hfreeze l hl hlp Tbox hT).bounded_cells⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
