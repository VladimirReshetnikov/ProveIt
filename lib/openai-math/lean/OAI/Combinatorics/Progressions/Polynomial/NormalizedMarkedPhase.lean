import OAI.Combinatorics.Progressions.Estimates.MarkedShiftGeneratorBounds

namespace OAI

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t : ℕ)

noncomputable def markedShiftPhase :
    markedShiftSubalgebra F v w marked t →ₗ⁅ℚ⁆ RationalTorus.Algebra t where
  toFun x := x.val.right
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

theorem markedShiftPhase_apply (x : markedShiftSubalgebra F v w marked t) :
    markedShiftPhase F v w marked t x = x.val.right := rfl

noncomputable def markedQuotientPhase :
    MarkedShiftQuotient F v w marked t →ₗ⁅ℚ⁆ RationalTorus.Algebra t :=
  lieQuotientDescend (markedShiftSecondIdeal F v w marked t)
    (markedShiftPhase F v w marked t) (fun _ hx => hx.1)

theorem markedQuotientPhase_map (x : markedShiftSubalgebra F v w marked t) :
    markedQuotientPhase F v w marked t (lieQuotientMap (markedShiftSecondIdeal F v w marked t) x) =
      x.val.right := rfl

theorem markedQuotientPhase_direction (a : Fin t → ℚ) :
    markedQuotientPhase F v w marked t (markedQuotientDirection F v w marked t a) = a := rfl

noncomputable def markedQuotientPolynomialAlgebra :
    LieSubalgebra ℚ (MarkedShiftQuotient F v w marked t) :=
  (markedQuotientPhase F v w marked t).ker.toLieSubalgebra

theorem mem_markedQuotientPolynomialAlgebra (x : MarkedShiftQuotient F v w marked t) :
    x ∈ markedQuotientPolynomialAlgebra F v w marked t ↔ markedQuotientPhase F v w marked t x = 0 :=
  Iff.rfl

theorem exists_zero_phase_lift (x : MarkedShiftQuotient F v w marked t)
    (hx : markedQuotientPhase F v w marked t x = 0) :
    ∃ p : markedShiftSubalgebra F v w marked t,
      p.val.right = 0 ∧ lieQuotientMap (markedShiftSecondIdeal F v w marked t) p = x := by
  obtain ⟨p, rfl⟩ := lieQuotientMap_surjective (markedShiftSecondIdeal F v w marked t) x
  exact ⟨p, hx, rfl⟩

end Erdos3

end

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t : ℕ)
  (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)
  (hphase : ∀ z : D.filtration.Group, z ∈ D.lattice →
    IntegralVector (markedQuotientPhase F v w marked t z.coord))

include hphase in
theorem markedPhase_lattice_map :
    D.lattice ≤ (RationalTorus.nilmanifold t).lattice.comap
      (mapOfSteps (hL := D.filtration.lowerCentralSeries_eq_bot)
        (hM := (RationalTorus.nilmanifold t).filtration.lowerCentralSeries_eq_bot)
        (markedQuotientPhase F v w marked t)) := by
  intro z hz
  exact hphase z hz

noncomputable def markedPhaseProjection : D.Space → (Fin t → CircleFourier.Circle) :=
  (RationalTorus.phaseProjection t) ∘
    D.nativeSpaceMap (RationalTorus.nilmanifold t) (markedQuotientPhase F v w marked t)
      (markedPhase_lattice_map F v w marked t D hphase)

noncomputable def markedPhaseRealCoordinates
    (x : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) : Fin t → ℝ :=
  (((RationalTorus.basis t).baseChange ℝ).equivFun
    ((markedQuotientPhase F v w marked t).toLinearMap.baseChange ℝ x))

theorem markedPhaseProjection_mk (g : D.RealGroup) (i : Fin t) :
    markedPhaseProjection F v w marked t D hphase (QuotientGroup.mk g) i =
      (markedPhaseRealCoordinates F v w marked t g.coord i : CircleFourier.Circle) := rfl

noncomputable def markedPhaseLocalLift : D.Space → (Fin t → ℝ) :=
  centeredTorusLift ∘ markedPhaseProjection F v w marked t D hphase

theorem markedPhaseLocalLift_mk (g : D.RealGroup)
    (hg : ∀ i, |markedPhaseRealCoordinates F v w marked t g.coord i| ≤ 1 / 4) :
    markedPhaseLocalLift F v w marked t D hphase (QuotientGroup.mk g) =
      markedPhaseRealCoordinates F v w marked t g.coord := by
  funext i
  exact centeredCircleLift_coe (hg i)

include hphase in
theorem markedPhaseRealCoordinates_eq_of_small (g h : D.RealGroup)
    (hg : ∀ i, |markedPhaseRealCoordinates F v w marked t g.coord i| ≤ 1 / 4)
    (hh : ∀ i, |markedPhaseRealCoordinates F v w marked t h.coord i| ≤ 1 / 4)
    (heq : (QuotientGroup.mk g : D.Space) = QuotientGroup.mk h) :
    markedPhaseRealCoordinates F v w marked t g.coord =
      markedPhaseRealCoordinates F v w marked t h.coord := by
  rw [← markedPhaseLocalLift_mk F v w marked t D hphase g hg,
    ← markedPhaseLocalLift_mk F v w marked t D hphase h hh, heq]

variable [TopologicalSpace (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
  [T2Space (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]

theorem markedPhaseProjection_lipschitz {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (ht : (t : ℝ) ≤ p)
    (hcoords : ∀ i j, rationalLogHeight (markedQuotientPhase F v w marked t (D.basis j) i) ≤ p) :
    letI := D.metricSpace
    LipschitzWith ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩
      (markedPhaseProjection F v w marked t D hphase) := by
  let := D.metricSpace
  let := (RationalTorus.nilmanifold t).metricSpace
  have hmap := D.nativeSpaceMap_lipschitz (RationalTorus.nilmanifold t)
    (markedQuotientPhase F v w marked t) (markedPhase_lattice_map F v w marked t D hphase)
    hp hD (RationalTorus.nilmanifold_geometry t hp ht) (fun i j => by
      change rationalLogHeight ((RationalTorus.basis t).repr
        (markedQuotientPhase F v w marked t (D.basis j)) i) ≤ p
      rw [RationalTorus.basis_repr]
      exact hcoords i j)
  have h : LipschitzWith ((1 : ℝ≥0) * ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩)
      (markedPhaseProjection F v w marked t D hphase) :=
    (RationalTorus.phaseProjection_lipschitz t).comp hmap
  exact h.weaken (le_of_eq (_root_.one_mul
    (⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩ : ℝ≥0)))

theorem markedPhaseLocalLift_lipschitzOn {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (ht : (t : ℝ) ≤ p)
    (hcoords : ∀ i j, rationalLogHeight (markedQuotientPhase F v w marked t (D.basis j) i) ≤ p) :
    letI := D.metricSpace
    LipschitzOnWith ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩
      (markedPhaseLocalLift F v w marked t D hphase)
      {x | ∀ i, ‖markedPhaseProjection F v w marked t D hphase x i‖ ≤ 1 / 4} := by
  let := D.metricSpace
  have hmap := markedPhaseProjection_lipschitz F v w marked t D hphase hp hD ht hcoords
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have h := centeredTorusLift_lipschitzOn.dist_le_mul
    (markedPhaseProjection F v w marked t D hphase x) hx
    (markedPhaseProjection F v w marked t D hphase y) hy
  simp only [NNReal.coe_one, _root_.one_mul] at h
  exact h.trans (hmap.dist_le_mul x y)

end Erdos3

end

section

namespace Erdos3

theorem rationalLogHeight_nat_inv_mul_exp_bound (m : ℕ) (hm : 0 < m)
    {p : ℝ} (hp : 0 ≤ p) (hmp : (m : ℝ) ≤ Real.exp p) {x : ℚ}
    (hx : rationalLogHeight x ≤ p) :
    rationalLogHeight ((m : ℚ)⁻¹ * x) ≤ 2 * p + 1 := by
  have hmheight : RationalHeightLE (m : ℚ) m := by
    simp only [RationalHeightLE, Rat.num_natCast, Rat.den_natCast, Int.natAbs_natCast]
    exact ⟨le_rfl, hm⟩
  have hinv := hmheight.inv (by exact_mod_cast hm.ne')
  apply rationalLogHeight_le_of_height (hinv.mul (rationalHeightLE_ceil_exp hx))
  rw [Nat.cast_mul]
  calc
    (m : ℝ) * ⌈Real.exp p⌉₊ ≤ Real.exp p * Real.exp (p + 1) :=
      mul_le_mul hmp (ceil_exp_le_exp_add_one hp) (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (2 * p + 1) := by rw [← Real.exp_add]; congr 1; ring

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t m : ℕ)

noncomputable def normalizedMarkedPhase :
    MarkedShiftQuotient F v w marked t →ₗ⁅ℚ⁆ RationalTorus.Algebra t where
  toLinearMap := (m : ℚ)⁻¹ • (markedQuotientPhase F v w marked t).toLinearMap
  map_lie' {x y} := by
    change (m : ℚ)⁻¹ • markedQuotientPhase F v w marked t ⁅x, y⁆ = 0
    rw [(markedQuotientPhase F v w marked t).map_lie, RationalTorus.lie_eq_zero, smul_zero]

theorem normalizedMarkedPhase_apply (x : MarkedShiftQuotient F v w marked t) :
    normalizedMarkedPhase F v w marked t m x =
      (m : ℚ)⁻¹ • markedQuotientPhase F v w marked t x := rfl

theorem normalizedMarkedPhase_scaled_direction (hm : 0 < m) (a : Fin t → ℚ) :
    normalizedMarkedPhase F v w marked t m
      ((m : ℚ) • markedQuotientDirection F v w marked t a) = a := by
  rw [normalizedMarkedPhase_apply, map_smul, markedQuotientPhase_direction]
  change (m : ℚ)⁻¹ • ((m : ℚ) • a) = a
  rw [smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast hm.ne' : (m : ℚ) ≠ 0), one_smul]

theorem normalizedMarkedPhase_height {p : ℝ} (hm : 0 < m) (hp : 0 ≤ p)
    (hmp : (m : ℝ) ≤ Real.exp p) (x : MarkedShiftQuotient F v w marked t) (i : Fin t)
    (hx : rationalLogHeight (markedQuotientPhase F v w marked t x i) ≤ p) :
    rationalLogHeight (normalizedMarkedPhase F v w marked t m x i) ≤ 2 * p + 1 :=
  rationalLogHeight_nat_inv_mul_exp_bound m hm hp hmp hx

end Erdos3

end

end OAI
