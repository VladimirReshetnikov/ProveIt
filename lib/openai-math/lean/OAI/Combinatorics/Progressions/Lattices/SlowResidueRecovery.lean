import OAI.Combinatorics.Progressions.Estimates.NativeSquareRecovery
import OAI.Combinatorics.Progressions.Estimates.SlowInverseControl

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_residue_recovery (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L M : Type*} [Fintype σ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) (w : σ → ℕ), (∀ i, 0 < w i) → ∀ {p : ℝ},
      0 ≤ p → (Fintype.card σ : ℝ) ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ P m : ℕ, 0 < P ∧ 0 < m ∧
        (P : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
          (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
          (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ (N : ℕ) (hN : 0 < N)
            (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
            (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
            let Q := D.withLattice Λ N hN hin hout
            Q.GeometryComplexityLE ((p + C) ^ C) ∧
            letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot)
              (E.basis.baseChange ℝ)
            letI := Q.metricSpace
            letI := E.metricSpace
            let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
              (hM := E.filtration.lowerCentralSeries_eq_bot) φ
            ∀ R : (E.filtration.realification.adaptedPolynomialFiltration w).Group,
              E.filtration.PolynomialRationalGrid E.basis w q R →
              ∃ z : (σ → ZMod P) → E.RealGroup,
                (∀ c, (∀ i, |(E.basis.baseChange ℝ).repr (z c).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
                  (E.basis.baseChange ℝ).equivFun (z c).coord ∈ realDenominatorGrid m) ∧
                ∀ κ : D.RealGroup, κ ∈ D.realLattice →
                  ∀ a b r f : (σ → ℤ) → D.RealGroup,
                    (∀ x, a x * b x * r x * κ = f x) →
                    (∀ x, ψ (r x) = E.filtration.adaptedPolynomialRealValueHom w
                      (fun i => (x i : ℝ)) R) →
                    (∀ x, (QuotientGroup.mk (ψ (b x)) : E.Space) =
                      QuotientGroup.mk ((ψ (a x))⁻¹ * ψ (f x) * (ψ κ)⁻¹ *
                        (z (fun i => (x i : ZMod P)))⁻¹)) ∧
                    ∀ x y, (fun i => (x i : ZMod P)) = (fun i => (y i : ZMod P)) →
                      (∀ i, |(E.basis.baseChange ℝ).repr ((ψ (a x))⁻¹).coord i| ≤
                        Real.exp ((p + 2) ^ k)) →
                      dist (QuotientGroup.mk (ψ (b x)) : E.Space) (QuotientGroup.mk (ψ (b y))) ≤
                        Real.exp ((p + C) ^ C) * dist (QuotientGroup.mk (f x) : Q.Space)
                          (QuotientGroup.mk (f y)) + dist (ψ (a x))⁻¹ (ψ (a y))⁻¹ := by
  obtain ⟨A, _, hresidue⟩ := exists_native_residue_representatives s
  obtain ⟨B, _, hrecovery⟩ := exists_uniform_left_class_recovery s k
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  let U := T + (T + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget U
  refine ⟨C, hC, ?_⟩
  intro σ L M _ _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ w hw p hp hσ hD hE hφ q hq hqp
  obtain ⟨P, m, hP, hm, hPb, hmb, hrepresentatives⟩ := hresidue E w hw p hp hE hσ q hq hqp
  let t := p + (p + A) ^ A
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_left hp
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ, hmetric⟩ :=
    hrecovery D E φ ht (hD.mono D hpt) (hE.mono E hpt) (fun i j => (hφ i j).trans hpt)
      m hm (hmb.trans (Real.exp_le_exp.mpr hAt))
  let Q := D.withLattice Λ N hN hin hout
  let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ
  have hsum : t + (t + B) ^ B ≤ (p + C) ^ C := by
    simpa [U, T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) _)).trans hsum
  have hcost : (t + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  refine ⟨P, m, hP, hm, hPb.trans (Real.exp_le_exp.mpr (hAt.trans htC)),
    hmb.trans (Real.exp_le_exp.mpr (hAt.trans htC)), Λ, hΛ, hchar, hnormal, hfinite,
    hindex.trans (Real.exp_le_exp.mpr hcost), N, hN, hin, hout, hQ.mono Q hcost, ?_⟩
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  let := Q.metricSpace
  let := E.metricSpace
  dsimp only
  intro R hR
  obtain ⟨_, z, hz, hclasses⟩ := hrepresentatives R hR
  refine ⟨z, fun c => ⟨fun i => ((hz c).2.2.1 i).trans
    (Real.exp_le_exp.mpr (hAt.trans htC)), (hz c).2.2.2⟩, ?_⟩
  intro κ hκ a b r f hfactor hvalue
  have hleft (x : σ → ℤ) : ∃ γ ∈ E.realLattice, ψ (r x) = γ * z (fun i => (x i : ZMod P)) := by
    obtain ⟨γ, hγ, heq⟩ := (hclasses x).2
    exact ⟨γ, hγ, (hvalue x).trans heq⟩
  refine ⟨?_, ?_⟩
  · intro x
    obtain ⟨γ, hγ, heq⟩ := hleft x
    exact recover_mapped_middle_coset_of_left_class ψ E.realLattice
      (a x) (b x) (r x) κ (f x) _ γ (hfactor x) hγ heq
  · intro x y hxy ha
    have hy : ∃ γ ∈ E.realLattice, ψ (r y) = γ * z (fun i => (x i : ZMod P)) := by
      rw [hxy]
      exact hleft y
    have ha' : ∀ i, |(E.basis.baseChange ℝ).repr ((ψ (a x))⁻¹).coord i| ≤ Real.exp ((t + 2) ^ k) :=
      fun i => (ha i).trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) k))
    have hdist := hmetric κ hκ (z (fun i => (x i : ZMod P))) ((hz _).2.2.2)
      (a x) (a y) (b x) (b y) (r x) (r y) (f x) (f y) (hfactor x) (hfactor y) (hleft x) hy ha'
    exact hdist.trans (add_le_add
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcost) dist_nonneg) le_rfl)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_slow_residue_recovery (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L M : Type*} [Fintype σ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) (w : σ → ℕ), (∀ i, 0 < w i) → ∀ {p : ℝ},
      0 ≤ p → (Fintype.card σ : ℝ) ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ P m : ℕ, 0 < P ∧ 0 < m ∧
        (P : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
          (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
          (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ (N : ℕ) (hN : 0 < N)
            (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
            (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
            let Q := D.withLattice Λ N hN hin hout
            Q.GeometryComplexityLE ((p + C) ^ C) ∧
            letI := Q.metricSpace
            letI := E.metricSpace
            let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
              (hM := E.filtration.lowerCentralSeries_eq_bot) φ
            ∀ R : (E.filtration.realification.adaptedPolynomialFiltration w).Group,
              E.filtration.PolynomialRationalGrid E.basis w q R →
              ∃ z : (σ → ZMod P) → E.RealGroup,
                (∀ c, (∀ i, |(E.basis.baseChange ℝ).repr (z c).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
                  (E.basis.baseChange ℝ).equivFun (z c).coord ∈ realDenominatorGrid m) ∧
                ∀ κ : D.RealGroup, κ ∈ D.realLattice →
                  ∀ a b r f : (σ → ℤ) → D.RealGroup,
                    (∀ x, a x * b x * r x * κ = f x) →
                    (∀ x, ψ (r x) = E.filtration.adaptedPolynomialRealValueHom w
                      (fun i => (x i : ℝ)) R) →
                    (∀ x, (QuotientGroup.mk (ψ (b x)) : E.Space) =
                      QuotientGroup.mk ((ψ (a x))⁻¹ * ψ (f x) * (ψ κ)⁻¹ *
                        (z (fun i => (x i : ZMod P)))⁻¹)) ∧
                    ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
                      ∀ S : (E.filtration.realification.adaptedPolynomialFiltration w).Group,
                        E.filtration.PolynomialSlowBound E.basis w T (Real.exp ((p + 2) ^ k)) S →
                        (∀ x, ψ (a x) = E.filtration.adaptedPolynomialRealValueHom w
                          (fun i => (x i : ℝ)) S) →
                        ∀ x y, (fun i => (x i : ZMod P)) = (fun i => (y i : ZMod P)) →
                          ∀ δ : ℝ, 0 ≤ δ →
                            (∀ i, |(x i : ℝ)| ≤ T i) → (∀ i, |(y i : ℝ)| ≤ T i) →
                            (∀ i, |(x i : ℝ) - (y i : ℝ)| ≤ T i * δ) →
                            dist (QuotientGroup.mk (ψ (b x)) : E.Space) (QuotientGroup.mk (ψ (b y))) ≤
                              Real.exp ((p + C) ^ C) *
                                (dist (QuotientGroup.mk (f x) : Q.Space) (QuotientGroup.mk (f y)) + δ) := by
  obtain ⟨A, _, hslow⟩ := exists_slow_inverse_control s k
  obtain ⟨B, _, hresidue⟩ := exists_uniform_residue_recovery s A
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C B) ^ B + (X + 2) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget U
  refine ⟨C, hC, ?_⟩
  intro σ L M _ _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ w hw p hp hσ hD hE hφ q hq hqp
  obtain ⟨P, m, hP, hm, hPb, hmb, Λ, hΛ, hchar, hnormal, hfinite, hindex,
    N, hN, hin, hout, hQ, hrecover⟩ := hresidue D E φ w hw hp hσ hD hE hφ q hq hqp
  let Q := D.withLattice Λ N hN hin hout
  let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ
  have hsum : (p + B) ^ B + (p + 2) ^ A ≤ (p + C) ^ C := by
    simpa [U, X, Polynomial.eval₂_pow] using hbudget p hp
  have hBC : (p + B) ^ B ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) _)).trans hsum
  have hAC : (p + 2) ^ A ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (pow_nonneg (by positivity) _)).trans hsum
  refine ⟨P, m, hP, hm, hPb.trans (Real.exp_le_exp.mpr hBC), hmb.trans (Real.exp_le_exp.mpr hBC),
    Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hBC),
    N, hN, hin, hout, hQ.mono Q hBC, ?_⟩
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  let := Q.metricSpace
  let := E.metricSpace
  dsimp only
  intro R hR
  obtain ⟨z, hz, heval⟩ := hrecover R hR
  refine ⟨z, fun c => ⟨fun i => ((hz c).1 i).trans (Real.exp_le_exp.mpr hBC), (hz c).2⟩, ?_⟩
  intro κ hκ a b r f hfactor hvalue
  obtain ⟨hexact, hmove⟩ := heval κ hκ a b r f hfactor hvalue
  refine ⟨hexact, ?_⟩
  intro T hT S hS hslowvalue x y hxy δ hδ hx hy hdelta
  obtain ⟨hcoords, hdist⟩ := hslow E w hw p hp hE hσ T hT S hS
  have hleft : ∀ i, |(E.basis.baseChange ℝ).repr ((ψ (a x))⁻¹).coord i| ≤ Real.exp ((p + 2) ^ A) := by
    rw [hslowvalue x]
    exact hcoords (fun i => (x i : ℝ)) hx
  have hinverse : dist (ψ (a x))⁻¹ (ψ (a y))⁻¹ ≤ Real.exp ((p + 2) ^ A) * δ := by
    rw [hslowvalue x, hslowvalue y]
    exact hdist _ _ δ hδ hx hy hdelta
  apply (hmove x y hxy hleft).trans
  calc
    _ ≤ Real.exp ((p + B) ^ B) *
        dist (QuotientGroup.mk (f x) : Q.Space) (QuotientGroup.mk (f y)) +
          Real.exp ((p + 2) ^ A) * δ := add_le_add le_rfl hinverse
    _ ≤ Real.exp ((p + C) ^ C) *
        dist (QuotientGroup.mk (f x) : Q.Space) (QuotientGroup.mk (f y)) +
          Real.exp ((p + C) ^ C) * δ :=
      add_le_add (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hBC) dist_nonneg)
        (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hAC) hδ)
    _ = _ := (mul_add _ _ _).symm

end Erdos3.RationalFilteredNilmanifold

end

end OAI
