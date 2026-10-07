/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.NativeSquareRecovery
import OAI.Combinatorics.Progressions.Estimates.RecoveryPrecision
import OAI.Combinatorics.Progressions.Sampling.AnchoredObservationPartition

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_specified_square_recovery (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d dV : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      (V : RationalFilteredNilmanifold D.filtration.squareLieSubalgebra s dV) {p : ℝ},
      2 ≤ p → D.GeometryComplexityLE p → V.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight ((pi (fun _ : Bool => D)).basis.repr
        (D.filtration.squarePairMap (V.basis j)) i) ≤ p) →
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
        letI := V.metricSpace
        ∀ ε γ : D.RealGroup, γ ∈ D.realLattice →
          (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 2) ^ k)) →
          ∀ a b c d : D.RealGroup, ∀ u v : D.filtration.squareFiltration.realification.Group,
            D.filtration.realSquareFstHom u = ε⁻¹ * a * γ⁻¹ →
            D.filtration.realSquareSndHom u = b →
            D.filtration.realSquareFstHom v = ε⁻¹ * c * γ⁻¹ →
            D.filtration.realSquareSndHom v = d →
            ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ Real.exp (-((p + C) ^ C)) →
              dist (QuotientGroup.mk a : (E true).Space) (QuotientGroup.mk c) ≤ ρ →
              dist (QuotientGroup.mk b : (E false).Space) (QuotientGroup.mk d) ≤ ρ →
              dist (QuotientGroup.mk u : V.Space) (QuotientGroup.mk v) ≤
                Real.exp ((p + C) ^ C) * ρ := by
  obtain ⟨A, _, hrecovery⟩ := exists_factorwise_subgroup_recovery s k
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + 2) ^ 2 + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro L _ _ d dV _ _ _ _ D _ _ _ _ V p hp hD hV hmatrix
  have hp0 : 0 ≤ p := by linarith
  let D₂ := fun _ : Bool => D
  let : FiniteDimensional ℚ (Bool → L) := (productFinBasis D₂).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (Bool → L))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Bool → L)) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (Bool → L)) := realification_moduleTopology_t2 (productFinBasis D₂)
  let r := p + (p + 2) ^ 2 + 2
  have hpr : p ≤ r := by dsimp [r]; nlinarith [sq_nonneg (p + 2)]
  have hrr : (p + 2) ^ 2 ≤ r := by dsimp [r]; linarith
  have hr : 0 ≤ r := hp0.trans hpr
  have hbool : (Fintype.card Bool : ℝ) ≤ p := by
    simpa only [Fintype.card_bool, Nat.cast_ofNat] using hp
  have hprod := (pi_geometry D₂ hp0 hbool (fun _ => hD)).mono (pi D₂) hrr
  obtain ⟨Δ, l, hl, hlin, hlout, hindex, hE, _, hrecover⟩ :=
    hrecovery D₂ V D.filtration.squarePairMap D.filtration.squarePairMap_injective
      hr (hbool.trans hpr) (fun _ => hD.mono D hpr) hprod (hV.mono V hpr)
      (fun i j => (hmatrix i j).trans hpr)
      1 (by decide) (by simpa only [Nat.cast_one] using Real.one_le_exp hr)
  let E := fun i => D.withLattice (Δ i) (l i) (hl i) (hlin i) (hlout i)
  have hsum : r + (r + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, R, r, Polynomial.eval₂_pow] using hbudget p hp0
  have hAC : (r + A) ^ A ≤ (p + C) ^ C := (le_add_of_nonneg_left hr).trans hsum
  refine ⟨Δ, l, hl, hlin, hlout, ?_, fun i => (hE i).mono (E i) hAC, ?_⟩
  · intro i
    rcases hindex i with ⟨hle, hchar, hnormal, hfinite, hbound⟩
    exact ⟨hle, hchar, hnormal, hfinite, hbound.trans (Real.exp_le_exp.mpr hAC)⟩
  let : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
  let := V.metricSpace
  dsimp only
  intro ε γ hγ hε a b c d u v huf hus hvf hvs ρ hρ hsmall hfirst hsecond
  let e := realBCHPiEquiv (fun _ : Bool => D.filtration)
  let K := e.symm (fun flag => cond flag γ 1)
  let B := e.symm (fun flag => cond flag ε⁻¹ 1)
  let P := e.symm (fun flag => cond flag a b)
  let Q := e.symm (fun flag => cond flag c d)
  have hK : K ∈ (pi D₂).realLattice := by
    apply pi_symm_mem_realLattice D₂
    intro flag
    cases flag
    · exact D.realLattice.one_mem
    · exact hγ
  have hgrid : ((pi D₂).basis.baseChange ℝ).equivFun (1 : (pi D₂).RealGroup).coord ∈
      realDenominatorGrid 1 := by
    refine ⟨fun _ => 0, ?_⟩
    simp only [coord_one, map_zero, Nat.cast_one, one_smul, Int.cast_zero, Pi.zero_def]
  have hB : ∀ i, |((pi D₂).basis.baseChange ℝ).repr B.coord i| ≤ Real.exp ((r + 2) ^ k) := by
    intro i
    exact (D.squareNormalizer_coordinate_bound ε (Real.exp_pos _).le hε i).trans
      (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) k))
  have hu : B * P * (K⁻¹ * 1) = D.filtration.realSquarePairHom u := by
    simpa only [mul_one] using D.filtration.realSquarePairHom_normalization ε γ a b u huf hus
  have hv : B * Q * (K⁻¹ * 1) = D.filtration.realSquarePairHom v := by
    simpa only [mul_one] using D.filtration.realSquarePairHom_normalization ε γ c d v hvf hvs
  have hnear : ρ ≤ Real.exp (-((r + A) ^ A)) :=
    hsmall.trans (Real.exp_le_exp.mpr (neg_le_neg hAC))
  have hP (flag : Bool) : productProjectionHom D₂ flag P = cond flag a b :=
    productProjectionHom_pi_symm D₂ (fun flag => cond flag a b) flag
  have hQ (flag : Bool) : productProjectionHom D₂ flag Q = cond flag c d :=
    productProjectionHom_pi_symm D₂ (fun flag => cond flag c d) flag
  have hinput : ∀ i, dist (QuotientGroup.mk (productProjectionHom D₂ i P) : (E i).Space)
      (QuotientGroup.mk (productProjectionHom D₂ i Q)) ≤ ρ := by
    intro flag
    rw [hP, hQ]
    cases flag
    · exact hsecond
    · exact hfirst
  have hd := hrecover K hK 1 hgrid B B P Q u v hB hu hv ρ hρ hnear hinput
    (fun _ => by simpa only [dist_self] using hρ)
  exact hd.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hAC) hρ)

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

def SquareImageRecoverySpec (s t k C : ℕ) : Prop :=
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
        ∀ ε γ : D.RealGroup, γ ∈ D.realLattice →
          (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 2) ^ k)) →
          ∀ a b c d : D.RealGroup, ∀ u v : D.filtration.squareFiltration.realification.Group,
            D.filtration.realSquareFstHom u = ε⁻¹ * a * γ⁻¹ →
            D.filtration.realSquareSndHom u = b →
            D.filtration.realSquareFstHom v = ε⁻¹ * c * γ⁻¹ →
            D.filtration.realSquareSndHom v = d →
            ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ Real.exp (-((p + C) ^ C)) →
              dist (QuotientGroup.mk a : (E true).Space) (QuotientGroup.mk c) ≤ ρ →
              dist (QuotientGroup.mk b : (E false).Space) (QuotientGroup.mk d) ≤ ρ →
              dist (QuotientGroup.mk (ψ u) : Q.Space) (QuotientGroup.mk (ψ v)) ≤
                Real.exp ((p + C) ^ C) * ρ

theorem exists_square_image_recovery (s t k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ SquareImageRecoverySpec.{u, v} s t k C := by
  obtain ⟨A, _, hsource⟩ := exists_native_source_cover
  obtain ⟨B, _, hrecovery⟩ := exists_specified_square_recovery s k
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (R + (R + Polynomial.C B) ^ B + (R + 3) ^ 2)
  refine ⟨C, hC, ?_⟩
  dsimp only [SquareImageRecoverySpec]
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d dV dQ D _ _ _ _ V Q φ p hp hD hV hQ hpair hφ
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨Λ, _, _, _, _, _, m, hm, hin, hout, hVc, hmap⟩ := hsource V Q φ hp0 hV hQ hφ
  let V' := V.withLattice Λ m hm hin hout
  let r := p + (p + A) ^ A
  have hpr : p ≤ r := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hr : 0 ≤ r := hp0.trans hpr
  have hAr : (p + A) ^ A ≤ r := le_add_of_nonneg_left hp0
  have hVr : V'.GeometryComplexityLE r := hVc.mono V' hAr
  obtain ⟨Δ, l, hl, hlin, hlout, hindex, hE, hrecover⟩ :=
    hrecovery D V' (hp.trans hpr) (hD.mono D hpr) hVr (fun i j => (hpair i j).trans hpr)
  let E := fun i => D.withLattice (Δ i) (l i) (hl i) (hlin i) (hlout i)
  have htotal : r + (r + B) ^ B + (r + 3) ^ 2 ≤ (p + C) ^ C := by
    simpa [X, R, r, Polynomial.eval₂_pow] using hbudget p hp0
  have hBC : (r + B) ^ B ≤ (p + C) ^ C := by nlinarith [sq_nonneg (r + 3)]
  have hsum : (r + 3) ^ 2 + (r + B) ^ B ≤ (p + C) ^ C := by linarith
  refine ⟨Δ, l, hl, hlin, hlout, ?_, fun i => (hE i).mono (E i) hBC, ?_⟩
  · intro i
    obtain ⟨hle, hchar, hnormal, hfinite, hbound⟩ := hindex i
    exact ⟨hle, hchar, hnormal, hfinite, hbound.trans (Real.exp_le_exp.mpr hBC)⟩
  let : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
  let := Q.metricSpace
  let := V'.metricSpace
  intro ε γ hγ hε a b c d u v huf hus hvf hvs ρ hρ hsmall hfirst hsecond
  have hεr : ∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((r + 2) ^ k) := by
    intro i
    exact (hε i).trans (Real.exp_le_exp.mpr
      (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith : p + 2 ≤ r + 2) k))
  have hsquare := hrecover ε γ hγ hεr a b c d u v huf hus hvf hvs ρ hρ
    (hsmall.trans (Real.exp_le_exp.mpr (neg_le_neg hBC))) hfirst hsecond
  have hprojection := nativeMap_dist_le V' Q φ hmap hr hVr (hQ.mono Q hpr)
    (fun i j => (hφ i j).trans hpr) u v
  apply hprojection.trans
  calc
    _ ≤ Real.exp ((r + 3) ^ 2) * (Real.exp ((r + B) ^ B) * ρ) :=
      mul_le_mul_of_nonneg_left hsquare (Real.exp_pos _).le
    _ = Real.exp ((r + 3) ^ 2 + (r + B) ^ B) * ρ := by rw [← mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hsum) hρ

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

def PrescribedSquareImagePartitionSpec (s t k₀ a C : ℕ) : Prop :=
    ∀ {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
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
      (φ : D.filtration.squareLieSubalgebra →ₗ⁅ℚ⁆ M)
      (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (c : ℤ) (q N : ℕ) [NeZero q] [NeZero N] {p ε : ℝ},
      1 ≤ s → 2 ≤ p → D.GeometryComplexityLE p → V.GeometryComplexityLE p →
      Q.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight ((pi (fun _ : Bool => D)).basis.repr
        (D.filtration.squarePairMap (V.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (Q.basis.repr (φ (V.basis j)) i) ≤ p) →
      (q : ℝ) ≤ Real.exp p → 0 < ε → ε ≤ 1 → 1 / ε ≤ Real.exp ((p + 2) ^ a) →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ 1 / δ ≤ Real.exp ((p + C) ^ C) ∧
        ∃ n k : ℕ, 0 < n ∧ 0 < k ∧
          (Fintype.card ((Fin n × ZMod q) × Fin k) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ A : ((Fin n × ZMod q) × Fin k) → ZMod N → ℝ,
            (∀ j, PositiveCyclicNiltest.{0} s N ((p + C) ^ C) (A j)) ∧
            (∀ x, ∑ j, A j x = 1) ∧
            (∀ j x, 0 < A j x → (x.val : ZMod q) = j.1.2) ∧
            (∀ j x y, 0 < A j x → 0 < A j y →
              dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ δ) ∧
            (∀ h : ZMod N, ((cyclicWrapExceptional h δ).card : ℝ) / N ≤ 6 * δ + 3 / N) ∧
            letI := Q.metricSpace
            let ψ := realificationMap (hnil := D.filtration.squareFiltration.lowerCentralSeries_eq_bot)
              (hM := Q.filtration.lowerCentralSeries_eq_bot) φ
            ∀ (h : ZMod N) (branch : Fin 2) (η γ : D.RealGroup)
              (rSq : D.filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1)),
                γ ∈ D.realLattice →
                (∀ i, |(D.basis.baseChange ℝ).repr η.coord i| ≤ Real.exp ((p + 2) ^ k₀)) →
                (∀ z : Unit → ℤ,
                  D.filtration.realSquareFstHom
                    (D.filtration.squareFiltration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) z rSq) =
                      η⁻¹ * D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                        (z + fun _ => (h.val : ℤ) - (branch.val : ℤ) * N) g * γ⁻¹ ∧
                  D.filtration.realSquareSndHom
                    (D.filtration.squareFiltration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) z rSq) =
                      D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                        (z + fun _ => c) g) →
                ∀ i j x y,
                  x ∉ cyclicWrapExceptional h δ → y ∉ cyclicWrapExceptional h δ →
                  0 < A i x * A j (x + h) → 0 < A i y * A j (y + h) →
                  dist (QuotientGroup.mk (ψ
                      (D.filtration.squareFiltration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) rSq)) : Q.Space)
                    (QuotientGroup.mk (ψ
                      (D.filtration.squareFiltration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) (fun _ => (y.val : ℤ)) rSq))) ≤ ε

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_prescribed_square_image_partition (s t k₀ a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ PrescribedSquareImagePartitionSpec s t k₀ a C := by
  obtain ⟨R, _, hrec⟩ := exists_square_image_recovery.{0, 0} s t k₀
  let B : ℕ := Classical.choose (exists_anchored_observation_partition s 1)
  have hpartition := @(Classical.choose_spec (exists_anchored_observation_partition s 1)).2
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C R) ^ R
  let T := X + U + (X + 2) ^ a + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  dsimp only [PrescribedSquareImagePartitionSpec]
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d dV dQ D _ _ _ _ V Q φ g c q N _ _ p ε
    hs hp hD hV hQ hpair hφ hq hε hε1 hεinv
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨Δ, l, hl, hlin, hlout, _, hE, hrecover⟩ := hrec D V Q φ hp hD hV hQ hpair hφ
  let E := fun i => D.withLattice (Δ i) (l i) (hl i) (hlin i) (hlout i)
  let r := (p + R) ^ R
  let K := (p + 2) ^ a
  let u := p + r + K + 2
  let δ := ε * Real.exp (-r)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpu : p ≤ u := by dsimp [u]; linarith
  have hru : r ≤ u := by dsimp [u]; linarith
  have hku : K + r ≤ u := by dsimp [u]; linarith
  have hu : 0 ≤ u := hp0.trans hpu
  obtain ⟨hδ, hδε, hδsmall, hδerror, hδinv⟩ := recovery_precision_bounds hr hε hε1 hεinv
  have htotal : u + (u + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, U, T, r, K, u, Polynomial.eval₂_pow] using hbudget p hp0
  have hcost : (u + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left hu).trans htotal
  have huC : u ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) _)).trans htotal
  have hrC : r ≤ (p + C) ^ C := hru.trans huC
  let E' : Unit → Bool → RationalFilteredNilmanifold L s d := fun _ => E
  let g' : ∀ i b, (E' i b).filtration.realification.PolynomialOrbit (fun _ : Unit => 1) :=
    fun _ _ => g
  have hδinverse : 1 / δ ≤ Real.exp ((u + 2) ^ 1) := by
    apply hδinv.trans (Real.exp_le_exp.mpr _)
    rw [pow_one]
    linarith
  obtain ⟨n, k, hn, hk, hcount, A, hA, hsum, hres, hcircle, hexception, hanchor, hmove⟩ :=
    hpartition E' g' (fun _ => c) q N hs hu
      (by simpa only [Fintype.card_unit, Nat.cast_one] using
        ((by linarith : 1 ≤ p).trans hpu))
      (fun _ b => (hE b).mono (E b) hru)
      (hq.trans (Real.exp_le_exp.mpr hpu)) hδ hδinverse
  refine ⟨δ, hδ, hδε, hδinv.trans (Real.exp_le_exp.mpr (hku.trans huC)),
    n, k, hn, hk, hcount.trans (Real.exp_le_exp.mpr hcost), A,
    fun j => (hA j).mono le_rfl hcost, hsum, hres, hcircle, hexception, ?_⟩
  let : ∀ b, MetricSpace (E b).Space := fun b => (E b).metricSpace
  let := Q.metricSpace
  intro h branch η γ rSq hγ hη hnorm i j x y hx hy hxy hyy
  have hpositive (z : ZMod N) (hz : 0 < A i z * A j (z + h)) : 0 < A i z := by
    rcases mul_pos_iff.mp hz with hz | hz
    · exact hz.1
    · linarith [((hA i).unit_interval z).1]
  have hfirst := hmove h branch i j x y hx hy hxy hyy ()
  change dist ((E true).integerOrbitPoint g ((x.val : ℤ) + h.val - (branch.val : ℤ) * N))
    ((E true).integerOrbitPoint g ((y.val : ℤ) + h.val - (branch.val : ℤ) * N)) ≤ δ at hfirst
  have hsecond := hanchor i x y (hpositive x hxy) (hpositive y hyy) ()
  change dist ((E false).integerOrbitPoint g ((x.val : ℤ) + c))
    ((E false).integerOrbitPoint g ((y.val : ℤ) + c)) ≤ δ at hsecond
  have hbound := hrecover η γ hγ hη
    (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
      ((fun _ => (x.val : ℤ)) + fun _ => (h.val : ℤ) - (branch.val : ℤ) * N) g)
    (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
      ((fun _ => (x.val : ℤ)) + fun _ => c) g)
    (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
      ((fun _ => (y.val : ℤ)) + fun _ => (h.val : ℤ) - (branch.val : ℤ) * N) g)
    (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
      ((fun _ => (y.val : ℤ)) + fun _ => c) g)
    (D.filtration.squareFiltration.realification.polynomialOrbitEval
      (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) rSq)
    (D.filtration.squareFiltration.realification.polynomialOrbitEval
      (fun _ : Unit => 1) (fun _ => (y.val : ℤ)) rSq)
    (hnorm (fun _ => (x.val : ℤ))).1 (hnorm (fun _ => (x.val : ℤ))).2
    (hnorm (fun _ => (y.val : ℤ))).1 (hnorm (fun _ => (y.val : ℤ))).2 δ hδ.le hδsmall
    (by
      change dist ((E true).integerOrbitPoint g ((x.val : ℤ) + ((h.val : ℤ) - (branch.val : ℤ) * N)))
        ((E true).integerOrbitPoint g ((y.val : ℤ) + ((h.val : ℤ) - (branch.val : ℤ) * N))) ≤ δ
      simpa only [add_sub_assoc] using hfirst)
    hsecond
  exact hδerror ▸ hbound

end Erdos3.RationalFilteredNilmanifold

end

end OAI
