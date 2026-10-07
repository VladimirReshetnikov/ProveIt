/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.AdaptedDiagramNativeExternalNet

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_single_refiltered_reconstruction (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      (D : RationalFilteredNilmanifold L (s + 1) d)
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded),
      let H := D.filtration.gradedRefiltrationSubalgebra W
      ∀ {e n : ℕ} (E : RationalFilteredNilmanifold H (s + 1) e)
        (Q : RationalFilteredNilmanifold (H ⧸ E.filtration.layerIdeal (s + 1)) s n),
      ∀ [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
        [TopologicalSpace (ℝ ⊗[ℚ] H)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] H)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] H)] [T2Space (ℝ ⊗[ℚ] H)]
        [TopologicalSpace (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))]
        [IsTopologicalAddGroup (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))]
        [T2Space (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))] (p : ℝ),
      E.filtration = D.filtration.gradedRefiltration W →
      0 ≤ p → E.GeometryComplexityLE p → D.GeometryComplexityLE p → Q.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (D.basis.repr (H.incl (E.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (Q.basis.repr
        (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      let T := Q.raiseStep (Nat.le_succ s)
      ∃ Λ : Subgroup T.filtration.Group, Λ ≤ T.lattice ∧
        (Λ.subgroupOf T.lattice).Characteristic ∧ (Λ.subgroupOf T.lattice).Normal ∧
        (Λ.subgroupOf T.lattice).FiniteIndex ∧ (Λ.relIndex T.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (B : ℕ) (hB : 0 < B)
          (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates Q.basis Λ)
          (hout : bchSubgroupCoordinates Q.basis Λ ⊆ denominatorGrid B),
          let V := Q.loweredCover (Nat.le_succ s) Λ B hB hin hout
          V.filtration = Q.filtration ∧ V.lattice ≤ Q.lattice ∧
          V.GeometryComplexityLE ((p + C) ^ C) ∧
          ∀ l r : D.RealGroup,
            (∀ i, |(D.basis.baseChange ℝ).repr l.coord i| ≤ Real.exp ((p + 2) ^ k)) →
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
            ∀ (S : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
              (let := D.metricSpace; LipschitzWith ℓ S) →
              (∀ x, (S x).im = 0 ∧ 0 ≤ (S x).re ∧ (S x).re ≤ 1) →
              (∀ z : D.RealGroup, z.coord ∈ D.filtration.realGradedRefiltrationLayer W (s + 1) →
                ∀ x, S (z • x) = S x) →
              ∃ (v : V.Space → ℂ) (K : ℝ≥0),
                (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (let := V.metricSpace; LipschitzWith K v) ∧
                (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧ (∀ x, ‖v x‖ ≤ 1) ∧
                ∀ x : E.RealGroup,
                  v (QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                    (hM := V.filtration.lowerCentralSeries_eq_bot)
                    (lieQuotientMap (E.filtration.layerIdeal (s + 1))) x)) =
                  S (QuotientGroup.mk (l * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                    (hM := D.filtration.lowerCentralSeries_eq_bot) H.incl x * r)) := by
  obtain ⟨a, _, hrec⟩ := exists_uniform_frozen_reconstruction (s + 1) k
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Polynomial.X + (Polynomial.X + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro L _ _ d D W H e n E Q _ _ _ _ _ _ _ _ _ _ _ _ p hEF hp hE hD hQ hφ hψ q hq hqp T
  have hsum : p + (p + a) ^ a ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  have ha0 : 0 ≤ (p + a) ^ a := by positivity
  have hpC : p ≤ (p + C) ^ C := by linarith
  have haC : (p + a) ^ a ≤ (p + C) ^ C := by linarith
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, B, hB, hin, hout, hV, hfrozen⟩ :=
    hrec E D T H.incl (lieQuotientMap (E.filtration.layerIdeal (s + 1))) p hp hE hD
      (Q.raiseStep_geometry (Nat.le_succ s) hQ) hφ hψ q hq hqp
  let V := Q.loweredCover (Nat.le_succ s) Λ B hB hin hout
  have hVlow : V.GeometryComplexityLE ((p + C) ^ C) :=
    Q.loweredCover_geometry (Nat.le_succ s) Λ B hB hin hout hQ hpC
      (hV.2.1.trans (Real.exp_le_exp.mpr haC))
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr haC),
    B, hB, hin, hout, rfl, Q.lowerCoverLattice_le (Nat.le_succ s) Λ hΛ, hVlow, ?_⟩
  intro l r hl hr S ℓ hℓ hS hunit hinvariant
  have hkernel : ∀ z ∈ (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := T.filtration.lowerCentralSeries_eq_bot)
      (lieQuotientMap (E.filtration.layerIdeal (s + 1)))).ker, ∀ x : E.RealGroup,
      S (QuotientGroup.mk (l * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) H.incl (z * x) * r)) =
      S (QuotientGroup.mk (l * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) H.incl x * r)) := by
    intro z hz x
    apply single_refiltered_frozen_invariant D W E hEF S hinvariant l r z x
    exact congrArg NilpotentLieBCHGroup.coord (MonoidHom.mem_ker.mp hz)
  obtain ⟨v, K, hK, hv, hpos, hcap, heval⟩ := hfrozen l r hl hr S ℓ hℓ hS hunit hkernel
  let lower := Q.loweredCoverMap (Nat.le_succ s) Λ B hB hin hout
  let := V.metricSpace
  let := (T.withLattice Λ B hB hin hout).metricSpace
  have hLip : LipschitzWith K (v ∘ lower) := by
    simpa only [mul_one] using hv.comp (Q.loweredCoverMap_lipschitz (Nat.le_succ s) Λ B hB hin hout)
  refine ⟨v ∘ lower, K, hK.trans (Real.exp_le_exp.mpr haC), hLip,
    (fun x => hpos (lower x)), (fun x => hcap (lower x)), ?_⟩
  intro x
  have hmap := Q.loweredCoverMap_mk (Nat.le_succ s) Λ B hB hin hout
    (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := Q.filtration.lowerCentralSeries_eq_bot)
      (lieQuotientMap (E.filtration.layerIdeal (s + 1))) x)
  exact (congrArg v hmap).trans (heval x)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d e n : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
  (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

noncomputable def SingleRefilteredRecoveryFamily (p : ℝ) (q k : ℕ) (cost : ℝ) : Prop :=
  let H := D.filtration.gradedRefiltrationSubalgebra W
  let N := H ⧸ E.filtration.layerIdeal (s + 1)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] N)
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] N)
  let := realification_moduleTopology_t2 Q.basis
  let T := Q.raiseStep (Nat.le_succ s)
  ∃ Λ : Subgroup T.filtration.Group, Λ ≤ T.lattice ∧
    (Λ.subgroupOf T.lattice).Characteristic ∧ (Λ.subgroupOf T.lattice).Normal ∧
    (Λ.subgroupOf T.lattice).FiniteIndex ∧ (Λ.relIndex T.lattice : ℝ) ≤ Real.exp cost ∧
    ∃ (B : ℕ) (hB : 0 < B)
      (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates Q.basis Λ)
      (hout : bchSubgroupCoordinates Q.basis Λ ⊆ denominatorGrid B),
      let V := Q.loweredCover (Nat.le_succ s) Λ B hB hin hout
      V.filtration = Q.filtration ∧ V.lattice ≤ Q.lattice ∧
      V.GeometryComplexityLE cost ∧
      ∀ l r : D.RealGroup,
        (∀ i, |(D.basis.baseChange ℝ).repr l.coord i| ≤ Real.exp ((p + 2) ^ k)) →
        (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
        ∀ (S : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
          (let := D.metricSpace; LipschitzWith ℓ S) →
          (∀ x, (S x).im = 0 ∧ 0 ≤ (S x).re ∧ (S x).re ≤ 1) →
          (∀ z : D.RealGroup, z.coord ∈ D.filtration.realGradedRefiltrationLayer W (s + 1) →
            ∀ x, S (z • x) = S x) →
          ∃ (v : V.Space → ℂ) (K : ℝ≥0),
            (K : ℝ) ≤ Real.exp cost ∧ (let := V.metricSpace; LipschitzWith K v) ∧
            (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧ (∀ x, ‖v x‖ ≤ 1) ∧
            ∀ x : E.RealGroup,
              v (QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := V.filtration.lowerCentralSeries_eq_bot)
                (lieQuotientMap (E.filtration.layerIdeal (s + 1))) x)) =
              S (QuotientGroup.mk (l * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := D.filtration.lowerCentralSeries_eq_bot) H.incl x * r))

theorem SingleRefilteredRecoveryFamily.mono {p p' cost cost' : ℝ} {q k : ℕ}
    (h : SingleRefilteredRecoveryFamily D W E Q p q k cost)
    (hp' : 0 ≤ p') (hpp : p' ≤ p) (hc : cost ≤ cost') :
    SingleRefilteredRecoveryFamily D W E Q p' q k cost' := by
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, B, hB, hin, hout,
    hVF, hVL, hV, hfrozen⟩ := h
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hc),
    B, hB, hin, hout, hVF, hVL, hV.mono _ hc, ?_⟩
  intro l r hl hr S ℓ hℓ hS hunit hinvariant
  have hl' : ∀ i, |(D.basis.baseChange ℝ).repr l.coord i| ≤ Real.exp ((p + 2) ^ k) := by
    intro i
    exact (hl i).trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) k))
  obtain ⟨v, K, hK, hv, hpos, hcap, heval⟩ := hfrozen l r hl' hr S ℓ
    (hℓ.trans (Real.exp_le_exp.mpr hpp)) hS hunit hinvariant
  exact ⟨v, K, hK.trans (Real.exp_le_exp.mpr hc), hv, hpos, hcap, heval⟩

theorem exists_uniform_single_refilteredRecoveryFamily (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      (D : RationalFilteredNilmanifold L (s + 1) d)
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) {e n : ℕ}
      (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
      (Q : RationalFilteredNilmanifold
        ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
      (p : ℝ), E.filtration = D.filtration.gradedRefiltration W →
      0 ≤ p → E.GeometryComplexityLE p → D.GeometryComplexityLE p → Q.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (D.basis.repr
        ((D.filtration.gradedRefiltrationSubalgebra W).incl (E.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (Q.basis.repr
        (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      SingleRefilteredRecoveryFamily D W E Q p q k ((p + C) ^ C) := by
  obtain ⟨C, hC, hrec⟩ := exists_single_refiltered_reconstruction s k
  refine ⟨C, hC, ?_⟩
  intro L _ _ d D _ _ _ _ W e n E Q p hEF hp hE hD hQ hφ hψ q hq hqp
  let H := D.filtration.gradedRefiltrationSubalgebra W
  let N := H ⧸ E.filtration.layerIdeal (s + 1)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] H)
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] H)
  let := realification_moduleTopology_t2 E.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] N)
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] N)
  let := realification_moduleTopology_t2 Q.basis
  exact hrec D W E Q p hEF hp hE hD hQ hφ hψ q hq hqp

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct NNReal

def FixedPositiveNiltestRealization {σ K : Type*} [LieRing K] [LieAlgebra ℚ K]
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {t d : ℕ}
    (V : RationalFilteredNilmanifold K t d) {w : σ → ℕ}
    (g : V.filtration.realification.PolynomialOrbit w) (cost : ℝ) (f : (σ → ℤ) → ℂ) : Prop :=
  ∃ U : V.Niltest w, U.orbit = g ∧ U.UnitIntervalValued ∧ U.ComplexityLE cost ∧
    ∀ x, U.eval x = f x

theorem SingleRefilteredRecoveryFamily.exists_fixed_child
    {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d e n : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
    (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
    (hEF : E.filtration = D.filtration.gradedRefiltration W)
    (hQF : Q.filtration = E.filtration.quotientTop)
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (b : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (hb : ∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
      D.filtration.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hb0 : coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0)
    {p cost : ℝ} {q k : ℕ} (hcost : 0 ≤ cost)
    (h : SingleRefilteredRecoveryFamily D W E Q p q k cost) :
    let H := D.filtration.gradedRefiltrationSubalgebra W
    let N := H ⧸ E.filtration.layerIdeal (s + 1)
    let := moduleTopology ℝ (ℝ ⊗[ℚ] N)
    let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] N)
    let := realification_moduleTopology_t2 Q.basis
    let T := Q.raiseStep (Nat.le_succ s)
    ∃ Λ : Subgroup T.filtration.Group, Λ ≤ T.lattice ∧
      (Λ.subgroupOf T.lattice).Characteristic ∧ (Λ.subgroupOf T.lattice).Normal ∧
      (Λ.subgroupOf T.lattice).FiniteIndex ∧ (Λ.relIndex T.lattice : ℝ) ≤ Real.exp cost ∧
      ∃ (B : ℕ) (hB : 0 < B)
        (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates Q.basis Λ)
        (hout : bchSubgroupCoordinates Q.basis Λ ⊆ denominatorGrid B),
        let V := Q.loweredCover (Nat.le_succ s) Λ B hB hin hout
        V.filtration = Q.filtration ∧ V.lattice ≤ Q.lattice ∧ V.GeometryComplexityLE cost ∧
        ∃ child : V.filtration.realification.PolynomialOrbit w,
          DegreeLE w s child.log ∧
          ∀ l r : D.RealGroup,
            (∀ i, |(D.basis.baseChange ℝ).repr l.coord i| ≤ Real.exp ((p + 2) ^ k)) →
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
            ∀ (S : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
              (let := D.metricSpace; LipschitzWith ℓ S) →
              (∀ x, (S x).im = 0 ∧ 0 ≤ (S x).re ∧ (S x).re ≤ 1) →
              (∀ z : D.RealGroup, z.coord ∈ D.filtration.realGradedRefiltrationLayer W (s + 1) →
                ∀ x, S (z • x) = S x) →
              V.FixedPositiveNiltestRealization child (cost + 4) (fun x =>
                S (QuotientGroup.mk (l *
                  D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) b * r))) := by
  intro H N _ _ _ T
  obtain ⟨g, hg⟩ := D.filtration.exists_model_refiltered_polynomial W E hEF w hw b hb hb0
  let gbar := E.topQuotientOrbit Q hQF g
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, B, hB, hin, hout, hVF, hVL, hV, hfrozen⟩ := h
  let V := Q.loweredCover (Nat.le_succ s) Λ B hB hin hout
  let child : V.filtration.realification.PolynomialOrbit w := gbar
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, B, hB, hin, hout, hVF, hVL, hV,
    child, child.degreeLE, ?_⟩
  intro l r hl hr S ℓ hℓ hS hunit hinvariant
  obtain ⟨v, K, hK, hv, hpos, hcap, heval⟩ := hfrozen l r hl hr S ℓ hℓ hS hunit hinvariant
  let U : V.Niltest w := {
    orbit := child
    observable := v
    normBound := 1
    lipBound := K
    norm_le := hcap
    lipschitz := hv }
  have hUc : U.ComplexityLE (cost + 4) := by
    refine ⟨hV.mono V (by linarith), ?_⟩
    change Real.log (2 + (1 : ℝ) + (K : ℝ)) ≤ cost + 4
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    calc
      _ ≤ 4 * Real.exp cost := by linarith [Real.one_le_exp hcost]
      _ ≤ Real.exp 4 * Real.exp cost := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
      _ = Real.exp (cost + 4) := by rw [← Real.exp_add, add_comm]
  refine ⟨U, rfl, hpos, hUc, ?_⟩
  intro x
  have hquot := E.topQuotientOrbit_eval Q hQF g x
  have hfirst := congrArg (fun y : Q.RealGroup => v (QuotientGroup.mk y)) hquot
  have hsecond := heval (E.filtration.realification.polynomialOrbitEval w x g)
  have hthird := congrArg (fun y : D.RealGroup => S (QuotientGroup.mk (l * y * r))) (hg x)
  exact hfirst.trans (hsecond.trans hthird)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem FixedPositiveNiltestRealization.transfer_discrepancy
    {σ K X Y : Type*} [LieRing K] [LieAlgebra ℚ K]
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {t d : ℕ}
    {V : RationalFilteredNilmanifold K t d} {w : σ → ℕ}
    {child : V.filtration.realification.PolynomialOrbit w} {cost : ℝ} {f : (σ → ℤ) → ℂ}
    (h : V.FixedPositiveNiltestRealization child cost f)
    (A : Finset X) (B : Finset Y) (x : X → σ → ℤ) (y : Y → σ → ℤ)
    {Δ : ℝ} (hgap : Δ ≤ ‖(𝔼 i ∈ A, f (x i)) - (𝔼 j ∈ B, f (y j))‖) :
    ∃ U : V.Niltest w, U.orbit = child ∧ U.UnitIntervalValued ∧ U.ComplexityLE cost ∧
      Δ ≤ ‖(𝔼 i ∈ A, U.eval (x i)) - (𝔼 j ∈ B, U.eval (y j))‖ := by
  obtain ⟨U, hU, hunit, hcost, heval⟩ := h
  refine ⟨U, hU, hunit, hcost, ?_⟩
  simpa only [heval] using hgap

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_controlled_single_refiltered_reconstruction (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L κ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d) (w : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ w i}))
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (v₀ : κ → D.filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v₀) = W.toSubmodule) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v₀ i) j) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1)
          (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = D.filtration.gradedRefiltration W ∧
        E.lattice = D.lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := (D.filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl) ∧
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ n : ℕ, n ≤ finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W) ∧
          ∃ Q : RationalFilteredNilmanifold
              ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n,
            Q.filtration = E.filtration.quotientTop ∧
            Q.lattice = E.lattice.map
              (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
            Q.GeometryComplexityLE ((p + C) ^ C) ∧
            SingleRefilteredRecoveryFamily D W E Q p q k ((p + C) ^ C) := by
  obtain ⟨A, _, hmodels⟩ := exists_single_refiltered_models
  obtain ⟨B, _, hrec⟩ := exists_uniform_single_refilteredRecoveryFamily s k
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + Polynomial.C A) ^ A
  let P := R + (R + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L κ _ _ _ _ _ _ _ d D w hF W v₀ hspan p hp hD hκ hv q hq hqp
  obtain ⟨E, hEF, hEL, hE, hinc, n, hn, Q, hQF, hQL, hQ, hproj⟩ :=
    hmodels D w hF W v₀ hspan hp hD hκ hv
  let t := p + (p + A) ^ A
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (add_nonneg hp (Nat.cast_nonneg A)) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_left hp
  have hsum : t + (t + B) ^ B ≤ (p + C) ^ C := by
    simpa [P, R, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg B)) _)).trans hsum
  have hcost : (t + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  have hfamily := hrec D W E Q t hEF ht (hE.mono E hAt) (hD.mono D hpt)
    (hQ.mono Q hAt) (fun i j => (hinc i j).trans hAt) (fun i j => (hproj i j).trans hAt)
    q hq (hqp.trans (Real.exp_le_exp.mpr hpt))
  exact ⟨E, hEF, hEL, hE.mono E (hAt.trans htC), n, hn, Q, hQF, hQL,
    hQ.mono Q (hAt.trans htC), SingleRefilteredRecoveryFamily.mono D W E Q hfamily hp hpt hcost⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
