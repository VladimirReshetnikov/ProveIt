import OAI.Combinatorics.Progressions.Estimates.PrescribedSquareImagePartition

namespace OAI

section

universe u v w

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

def SquareImagePathRecoverySpec (s t C : ℕ) : Prop :=
    ∀ {L : Type u} {M : Type v} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {d dV dQ : ℕ}
      (D : RationalFilteredNilmanifold L s d)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      (V : RationalFilteredNilmanifold D.filtration.squareLieSubalgebra s dV)
      (Q : RationalFilteredNilmanifold M t dQ)
      (φ : D.filtration.squareLieSubalgebra →ₗ⁅ℚ⁆ M) {p : ℝ},
      2 ≤ p → D.GeometryComplexityLE p → V.GeometryComplexityLE p → Q.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight ((pi (fun _ : Bool => D)).basis.repr
        (D.filtration.squarePairMap (V.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (Q.basis.repr (φ (V.basis j)) i) ≤ p) →
      ∃ (Δ : Bool → Subgroup D.filtration.Group) (l : Bool → ℕ)
        (hl : ∀ i, 0 < l i)
        (hlin : ∀ i, scaledIntegerGrid (l i) ⊆ bchSubgroupCoordinates D.basis (Δ i))
        (hlout : ∀ i, bchSubgroupCoordinates D.basis (Δ i) ⊆ denominatorGrid (l i)),
        let E := fun i => D.withLattice (Δ i) (l i) (hl i) (hlin i) (hlout i)
        (∀ i, Δ i ≤ D.lattice ∧ ((Δ i).subgroupOf D.lattice).Characteristic ∧
          ((Δ i).subgroupOf D.lattice).Normal ∧ ((Δ i).subgroupOf D.lattice).FiniteIndex ∧
          ((Δ i).relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        (∀ i, (E i).GeometryComplexityLE ((p + C) ^ C)) ∧
        letI : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
        letI := Q.metricSpace
        let ψ := realificationMap (hnil := D.filtration.squareFiltration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot) φ
        ∀ {σ : Type w} (ω : σ → ℕ), (∀ i, 0 < ω i) →
          ∀ (g : D.filtration.realification.PolynomialOrbit ω) (a b : σ → ℤ),
          ∃ (η γ : D.RealGroup) (rSq : D.filtration.squareFiltration.realification.PolynomialOrbit ω),
            γ ∈ D.realLattice ∧
            (∀ i, |(D.basis.baseChange ℝ).repr η.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
            (∀ x : σ → ℤ,
              D.filtration.realSquareFstHom
                (D.filtration.squareFiltration.realification.polynomialOrbitEval ω x rSq) =
                  η⁻¹ * D.filtration.realification.polynomialOrbitEval ω (x + a) g * γ⁻¹ ∧
              D.filtration.realSquareSndHom
                (D.filtration.squareFiltration.realification.polynomialOrbitEval ω x rSq) =
                  D.filtration.realification.polynomialOrbitEval ω (x + b) g) ∧
            ∀ (x y : σ → ℤ) (ρ : ℝ), 0 ≤ ρ → ρ ≤ Real.exp (-((p + C) ^ C)) →
              dist (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval ω (x + a) g) :
                (E true).Space)
                (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval ω (y + a) g)) ≤ ρ →
              dist (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval ω (x + b) g) :
                (E false).Space)
                (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval ω (y + b) g)) ≤ ρ →
              dist (QuotientGroup.mk (ψ
                  (D.filtration.squareFiltration.realification.polynomialOrbitEval ω x rSq)) : Q.Space)
                (QuotientGroup.mk (ψ
                  (D.filtration.squareFiltration.realification.polynomialOrbitEval ω y rSq))) ≤
                    Real.exp ((p + C) ^ C) * ρ

theorem exists_square_image_path_recovery (s t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ SquareImagePathRecoverySpec.{u, v, w} s t C := by
  obtain ⟨A, _, hnorm⟩ := exists_native_two_shift_normalization s
  obtain ⟨B, _, hrec⟩ := exists_square_image_recovery s t A
  let X : Polynomial ℕ := Polynomial.X
  let R := X + Polynomial.C A + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((R + Polynomial.C B) ^ B + (X + 1 + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  dsimp only [SquareImagePathRecoverySpec]
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d dV dQ D _ _ _ _ V Q φ p hp hD hV hQ hpair hφ
  have hp0 : 0 ≤ p := by linarith
  let r := p + A + 1
  have hpr : p ≤ r := by
    have hA : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
    dsimp [r]
    linarith
  obtain ⟨Δ, l, hl, hlin, hlout, hindex, hE, hrecover⟩ :=
    hrec D V Q φ (hp.trans hpr) (hD.mono D hpr) (hV.mono V hpr) (hQ.mono Q hpr)
      (fun i j => (hpair i j).trans hpr) (fun i j => (hφ i j).trans hpr)
  let E := fun i => D.withLattice (Δ i) (l i) (hl i) (hlin i) (hlout i)
  have hsum : (r + B) ^ B + (p + 1 + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, R, r, Polynomial.eval₂_pow] using hbudget p hp0
  have hBC : (r + B) ^ B ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) _)).trans hsum
  have hAC : (p + 1 + A) ^ A ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (pow_nonneg (by dsimp [r]; positivity) _)).trans hsum
  refine ⟨Δ, l, hl, hlin, hlout, ?_, fun i => (hE i).mono (E i) hBC, ?_⟩
  · intro i
    obtain ⟨hle, hchar, hnormal, hfinite, hbound⟩ := hindex i
    exact ⟨hle, hchar, hnormal, hfinite, hbound.trans (Real.exp_le_exp.mpr hBC)⟩
  let : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
  let := Q.metricSpace
  intro σ ω hω g a b
  obtain ⟨η, γ, hγ, hη, rSq, hnorm⟩ := hnorm D hp0 hD ω hω a b g
  refine ⟨η, γ, rSq, hγ, fun i => (hη i).trans (Real.exp_le_exp.mpr hAC), hnorm, ?_⟩
  intro x y ρ hρ hsmall hfirst hsecond
  have hηr : ∀ i, |(D.basis.baseChange ℝ).repr η.coord i| ≤ Real.exp ((r + 2) ^ A) := by
    intro i
    apply (hη i).trans
    apply Real.exp_le_exp.mpr
    apply pow_le_pow_left₀ (by positivity) _ A
    dsimp [r]
    linarith
  have hd := hrecover η γ hγ hηr
    (D.filtration.realification.polynomialOrbitEval ω (x + a) g)
    (D.filtration.realification.polynomialOrbitEval ω (x + b) g)
    (D.filtration.realification.polynomialOrbitEval ω (y + a) g)
    (D.filtration.realification.polynomialOrbitEval ω (y + b) g)
    (D.filtration.squareFiltration.realification.polynomialOrbitEval ω x rSq)
    (D.filtration.squareFiltration.realification.polynomialOrbitEval ω y rSq)
    (hnorm x).1 (hnorm x).2 (hnorm y).1 (hnorm y).2 ρ hρ
    (hsmall.trans (Real.exp_le_exp.mpr (neg_le_neg hBC))) hfirst hsecond
  exact hd.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hBC) hρ)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
