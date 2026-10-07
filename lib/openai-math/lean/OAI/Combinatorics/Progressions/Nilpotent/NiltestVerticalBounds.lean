import OAI.Combinatorics.Progressions.Dynamics.VerticalDecompositionBudget
import OAI.Combinatorics.Progressions.Estimates.SquareRationalModel
import OAI.Combinatorics.Progressions.Estimates.UniformCommutingCircleDecomposition
import OAI.Combinatorics.Progressions.Fourier.RationalFrequencyHeight
import OAI.Combinatorics.Progressions.Fourier.VerticalFrequencyIdentification
import OAI.Combinatorics.Progressions.Linear.RealifiedCentralBasisAction

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem exists_controlled_adapted_basis {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ) (N : ℕ),
      Monotone w ∧ IsCentralLieBasis b ∧
      (∀ i, D.filtration.layer i = Submodule.span ℚ (b '' {j | i ≤ w j})) ∧
      (∀ j i, rationalLogHeight (D.basis.repr (b j) i) ≤ p + 1) ∧
      (∀ i j, rationalLogHeight (b.repr (D.basis i) j) ≤ (p + 3) ^ 5) ∧
      (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + 3) ^ 11) ∧
      0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 3) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b D.lattice ∧
      bchSubgroupCoordinates b D.lattice ⊆ denominatorGrid N := by
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHp : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hp1 : 0 ≤ p + 1 := by linarith
  have hdp : (Fintype.card (Fin d) : ℝ) ≤ p + 1 := by
    simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 1 by linarith)
  have hlp : (D.grid : ℝ) ≤ Real.exp (p + 1) :=
    hD.2.1.trans (Real.exp_le_exp.mpr (by linarith))
  obtain ⟨b, w, N, hw, hc, hlayers, hb, hbinv, hbracket, hN, hNp, hin, hout⟩ :=
    D.filtration.exists_adapted_basis_and_grid D.basis (fun i => D.layerBasis i)
      (fun i => (D.layerBasis i).span_eq) D.lattice hH D.grid_pos
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.2 i j k))
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
      D.inner_grid D.outer_grid hp1 hdp hHp hlp
  have hdr : (finrank ℚ L : ℝ) ≤ p + 1 := by
    simpa only [finrank_eq_card_basis D.basis] using hdp
  have hshift : p + 1 + 2 = p + 3 := by ring
  have hinvBudget : (rationalSolveHeight (finrank ℚ L) H : ℝ) ≤ Real.exp ((p + 3) ^ 5) := by
    simpa only [hshift] using rationalSolveHeight_le_budget (finrank ℚ L) H hp1 hdr hHp
  refine ⟨b, w, N, hw, hc, hlayers, ?_, ?_, ?_, hN, ?_, hin, hout⟩
  · exact fun j i => rationalLogHeight_le_of_height (hb j i) hHp
  · exact fun i j => rationalLogHeight_le_of_height (hbinv i j) hinvBudget
  · intro i j k
    apply (rationalLogHeight_le_iff _ _).mpr
    simpa only [hshift] using hbracket i j k
  · simpa only [hshift] using hNp

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_controlled_central_actions {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    letI := D.metricSpace
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ) (N : ℕ),
      (∀ i, D.filtration.layer i = Submodule.span ℚ (b '' {j | i ≤ w j})) ∧
      (∀ j i, rationalLogHeight (D.basis.repr (b j) i) ≤ p + 1) ∧
      (∀ i j, rationalLogHeight (b.repr (D.basis i) j) ≤ (p + 3) ^ 5) ∧
      0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 3) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b D.lattice ∧
      bchSubgroupCoordinates b D.lattice ⊆ denominatorGrid N ∧
      ∃ A : {j // s ≤ w j} → CircleFourier.IsometricCircleAction D.Space,
        (∀ i j, (A i).Commutes (A j)) ∧
        (∀ j (t : CircleFourier.Circle) x,
          dist ((A j).act t x) x ≤ Real.exp ((p + 3) ^ 9 + 2 * p + 2) * ‖t‖) ∧
        ∀ j (r : ℝ) x, (A j).act (r : CircleFourier.Circle) x =
          realBCHLine (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
            ((N : ℝ) • (b.baseChange ℝ) j) r • x := by
  let := D.metricSpace
  obtain ⟨b, w, N, _, _, hlayers, hb, hbinv, _, hN, hNb, hin, hout⟩ :=
    D.exists_controlled_adapted_basis hp hD
  have hcentral (j : {j // s ≤ w j}) (z : L) : ⁅b j, z⁆ = 0 := by
    apply D.filtration.top_layer_central
    rw [hlayers s]
    exact Submodule.subset_span ⟨j, j.property, rfl⟩
  let A : {j // s ≤ w j} → CircleFourier.IsometricCircleAction D.Space := fun j =>
    realifiedCentralBasisAction D.basis b D.lattice D.grid D.grid_pos D.outer_grid N hin j (hcentral j)
  have hbabs (j : Fin (finrank ℚ L)) (i : Fin d) :
      |(D.basis.repr (b j) i : ℝ)| ≤ Real.exp (p + 2) := by
    have hh := (rationalHeightLE_ceil_exp (hb j i)).abs_real_le
    have hceil := ceil_exp_le_exp_add_one (show 0 ≤ p + 1 by linarith)
    exact hh.trans (by simpa only [show p + 1 + 1 = p + 2 by ring] using hceil)
  have hcost : ((d : ℝ) + 1) * ((N : ℝ) * Real.exp (p + 2)) ≤
      Real.exp ((p + 3) ^ 9 + 2 * p + 2) := by
    have hd : (d : ℝ) + 1 ≤ Real.exp p :=
      (by linarith [hD.1] : (d : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)
    calc
      _ ≤ Real.exp p * (Real.exp ((p + 3) ^ 9) * Real.exp (p + 2)) := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  refine ⟨b, w, N, hlayers, hb, hbinv, hN, hNb, hin, hout, A, ?_, ?_, ?_⟩
  · intro i j
    exact realifiedCentralBasisAction_commutes D.basis b D.lattice D.grid D.grid_pos D.outer_grid
      N hin i j (hcentral i) (hcentral j)
  · intro j t x
    have hh := realifiedCentralBasisAction_displacement D.basis b D.lattice D.grid D.grid_pos D.outer_grid
      N hin j (hcentral j) (Real.exp_nonneg (p + 2)) (hbabs j) t x
    simp only [Fintype.card_fin] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hcost (norm_nonneg t))
  · intro j r x
    exact realifiedCentralBasisAction_act_coe D.basis b D.lattice D.grid D.grid_pos D.outer_grid
      N hin j (hcentral j) r x

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module

theorem exists_nilmanifold_integral_cover (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ)
        (B : ℕ) (Λ : Subgroup D.filtration.Group),
        Monotone w ∧ IsCentralLieBasis b ∧
        (∀ i, D.filtration.layer i = Submodule.span ℚ (b '' {j | i ≤ w j})) ∧
        (∀ j i, rationalLogHeight (D.basis.repr (b j) i) ≤ p + 1) ∧
        (∀ i j, rationalLogHeight (b.repr (D.basis i) j) ≤ (p + 3) ^ 5) ∧
        (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + 3) ^ 11) ∧
        0 < B ∧ (B : ℝ) ≤ Real.exp (((p + 3) ^ 11 + 1 + C) ^ C) ∧
        Λ ≤ D.lattice ∧ (Λ.subgroupOf D.lattice).FiniteIndex ∧
        bchSubgroupCoordinates b Λ = scaledIntegerGrid B ∧
        ∀ g ∈ Λ, ∃! z : Fin (finrank ℚ L) → ℤ,
          integralOrderedBasisProduct b D.filtration.lowerCentralSeries_eq_bot B z = g := by
  obtain ⟨C, hC, hcover⟩ := exists_controlled_integral_coordinates s
  refine ⟨C, hC, ?_⟩
  intro L _ _ d D p hp hD
  obtain ⟨b, w, N, hw, hc, hlayer, hb, hbinv, hbracket, hN, hNp, hin, hout⟩ :=
    D.exists_controlled_adapted_basis hp hD
  let q : ℝ := (p + 3) ^ 11
  let H := ⌈Real.exp q⌉₊
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hbase : 1 ≤ p + 3 := by linarith
  have hpq : p ≤ q := by
    calc
      p ≤ p + 3 := by linarith
      _ ≤ (p + 3) ^ 11 := by
        simpa only [pow_one] using pow_le_pow_right₀ hbase (by decide : 1 ≤ 11)
  have hdq : (finrank ℚ L : ℝ) ≤ q + 1 := by
    have hd : (finrank ℚ L : ℝ) ≤ p := by
      simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using hD.1
    exact (hd.trans hpq).trans (le_add_of_nonneg_right zero_le_one)
  have hH : (H : ℝ) ≤ Real.exp (q + 1) := ceil_exp_le_exp_add_one hq
  have hNq : (N : ℝ) ≤ Real.exp (q + 1) := by
    apply hNp.trans (Real.exp_le_exp.mpr ?_)
    exact (pow_le_pow_right₀ hbase (by decide : 9 ≤ 11)).trans
      (le_add_of_nonneg_right zero_le_one)
  obtain ⟨B, Λ, hB, _, hBp, hΛ, hfinite, hcoords, hnormal⟩ :=
    hcover b hc D.filtration.lowerCentralSeries_eq_bot D.lattice N H (q + 1) hN
      (fun i j k => rationalHeightLE_ceil_exp (hbracket i j k))
      hin hout (by linarith) hdq hH hNq
  exact ⟨b, w, B, Λ, hw, hc, hlayer, hb, hbinv, hbracket, hB, hBp, hΛ, hfinite, hcoords, hnormal⟩

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct BigOperators NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_controlled_vertical_decomposition {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) :
    letI := D.metricSpace
    ∀ (f : D.Space → ℂ) (K B : ℝ≥0), LipschitzWith K f → (∀ x, ‖f x‖ ≤ B) →
      (K : ℝ) ≤ Real.exp p → ∀ δ : ℝ, 0 < δ → δ⁻¹ ≤ Real.exp p →
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (η : J → L →ₗ[ℚ] ℚ) (v : J → D.Space → ℂ),
      (Fintype.card J : ℝ) ≤ Real.exp (verticalDecompositionBudget p) ∧
      (∀ j i, rationalLogHeight (η j (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ j, LipschitzWith K (v j) ∧ (∀ x, ‖v j x‖ ≤ B)) ∧
      (∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
        v j (z • x) = character ((realifyFunctional (η j) z.coord : ℝ) : CircleFourier.Circle) * v j x) ∧
      (∀ (z : D.RealGroup) (c : ℂ), (∀ x, f (z • x) = c * f x) →
        ∀ j x, v j (z • x) = c * v j x) ∧
      ∀ x, ‖(∑ j, v j x) - f x‖ ≤ δ := by
  classical
  let := D.metricSpace
  intro f K B hf hb hK δ hδ hδp
  obtain ⟨b, w, N, hlayers, _, hbinv, hN, hNp, _, _, A, hcomm, horbit, hact⟩ :=
    D.exists_controlled_central_actions hp hD
  let S : Set (Fin (finrank ℚ L)) := {j | s ≤ w j}
  let q := centralActionBudget p
  have hq : 0 ≤ q := centralActionBudget_nonneg hp
  have hpq : p ≤ q := le_centralActionBudget hp
  have hd : (Fintype.card S : ℝ) ≤ p := by
    apply (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans
    simpa only [Fintype.card_fin, finrank_eq_card_basis D.basis] using hD.1
  let O : ℝ≥0 := ⟨Real.exp q, (Real.exp_pos q).le⟩
  obtain ⟨J, inst, ν, v, hcard, hν, hv, hchar, hpres, herr⟩ :=
    exists_controlled_commuting_circle_decomposition A hcomm f K B O hf hb horbit δ q hδ hq
      (hd.trans hpq) (hK.trans (Real.exp_le_exp.mpr hpq)) le_rfl
      (hδp.trans (Real.exp_le_exp.mpr hpq))
  let η : J → L →ₗ[ℚ] ℚ := fun j => basisFrequency b S N (ν j)
  let R : ℝ := (2 * q + 2) ^ 4 + q + (p + 3) ^ 5
  have hpow : 0 ≤ (p + 3) ^ 5 := by positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hqR : q ≤ R := by dsimp [R]; nlinarith [sq_nonneg ((2 * q + 2) ^ 2)]
  have hfreq : (2 * q + 2) ^ 4 ≤ R := by dsimp [R]; linarith
  have hbas : (p + 3) ^ 5 ≤ R := by dsimp [R]; nlinarith [sq_nonneg ((2 * q + 2) ^ 2)]
  have hNq : (p + 3) ^ 9 ≤ q := by dsimp [q, centralActionBudget]; linarith
  have hterm : 2 * q * (2 * q + 2) ^ 4 ≤ verticalDecompositionBudget p := by
    change _ ≤ _ + (R + 2) ^ 4
    exact le_add_of_nonneg_right (by positivity)
  have hheight : (R + 2) ^ 4 ≤ verticalDecompositionBudget p := by
    change _ ≤ 2 * q * (2 * q + 2) ^ 4 + _
    have h : 0 ≤ 2 * q * (2 * q + 2) ^ 4 := by positivity
    linarith
  have hcentral (i : S) (z : L) : ⁅b i, z⁆ = 0 := by
    apply D.filtration.top_layer_central
    rw [hlayers s]
    exact Submodule.subset_span ⟨i, i.property, rfl⟩
  have hucentral (i : S) (z : ℝ ⊗[ℚ] L) : ⁅(N : ℝ) • b.baseChange ℝ i, z⁆ = 0 :=
    scaled_real_basis_central b i (hcentral i) N z
  refine ⟨J, inst, η, v, hcard.trans (Real.exp_le_exp.mpr hterm), ?_, hv, ?_, ?_, herr⟩
  · intro j i
    exact (basisFrequency_logHeight_le D.basis b S N hN (ν j) hR (hd.trans (hpq.trans hqR))
      (hNp.trans (Real.exp_le_exp.mpr (hNq.trans hqR)))
      (fun a => (hν j a).trans (Real.exp_le_exp.mpr hfreq))
      (fun a c => (hbinv a c).trans hbas) i).trans hheight
  · intro j z hz x
    apply central_span_character (fun i : S => (N : ℝ) • b.baseChange ℝ i) hucentral
      (realifyFunctional (η j)) (v j) ?_ ?_ x
    · intro i r y
      have h := hchar j i (r : CircleFourier.Circle) y
      rw [hact] at h
      change _ = character ((r * realifyFunctional (basisFrequency b S N (ν j))
        ((N : ℝ) • b.baseChange ℝ i) : ℝ) : CircleFourier.Circle) * _
      rw [realify_basisFrequency_direction b S N hN (ν j) i]
      simpa only [← AddCircle.coe_zsmul, zsmul_eq_mul, mul_comm] using h
    · exact D.filtration.realLayer_le_span_scaled_basis b s S (hlayers s) N hN hz
  · intro z c hc
    apply hpres (fun x => z • x) c ?_ hc
    intro i t x
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
    rw [hact, hact, ← mul_smul, ← mul_smul]
    rw [(realBCHLine_commute _ (hucentral i) r z).eq]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieFiltration

noncomputable def squareGeometryBudget (p : ℝ) : ℝ :=
  ((p + 3) ^ 11 + 2 * p + 5) ^ 11

theorem squareGeometryBudget_nonneg {p : ℝ} (hp : 0 ≤ p) : 0 ≤ squareGeometryBudget p := by
  unfold squareGeometryBudget
  positivity

theorem squareGeometryBudget_polynomial :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → squareGeometryBudget p ≤ (p + C) ^ C := by
  refine ⟨132, by decide, ?_⟩
  intro p hp
  have ht : 1 ≤ p + 5 := by linarith
  have hsmall : 2 * p + 5 ≤ (p + 5) ^ 2 := by nlinarith [sq_nonneg p]
  have htwo : (p + 5) ^ 2 ≤ (p + 5) ^ 11 := pow_le_pow_right₀ ht (by decide)
  have hbig : (p + 3) ^ 11 ≤ (p + 5) ^ 11 :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hinner : (p + 3) ^ 11 + 2 * p + 5 ≤ (p + 5) ^ 12 := by
    calc
      _ ≤ 2 * (p + 5) ^ 11 := by linarith
      _ ≤ (p + 5) * (p + 5) ^ 11 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  calc
    squareGeometryBudget p ≤ ((p + 5) ^ 12) ^ 11 :=
      pow_le_pow_left₀ (by positivity) hinner _
    _ = (p + 5) ^ 132 := by rw [← pow_mul]
    _ ≤ (p + (132 : ℕ)) ^ (132 : ℕ) :=
      pow_le_pow_left₀ (by linarith) (by norm_num) _

namespace RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem exists_controlled_square_geometry {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ)
      (hlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis b w (hlayers 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b w (hlayers 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p + 1) ∧
      (D.filtration.squareFiltration.ofAdaptedBasis
        (D.filtration.squareFinBasis b w (hlayers 2)) (squareFinWeight w)
        (D.filtration.squareFinBasis_layers b w hlayers)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE
          (squareGeometryBudget p) := by
  obtain ⟨b, w, l, _, _, hlayers, hb, _, hc, hl, hlp, hin, hout⟩ :=
    D.exists_controlled_adapted_basis hp hD
  let q : ℝ := (p + 3) ^ 11 + 2 * p + 3
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqbr : (p + 3) ^ 11 + 1 ≤ q := by dsimp [q]; linarith
  have hdim : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ p := by
    simpa only [Fintype.card_fin, finrank_eq_card_basis D.basis] using hD.1
  have h2dim : 2 * (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ q := by
    have hpow : 0 ≤ (p + 3) ^ 11 := by positivity
    dsimp [q]
    linarith
  have hH : (⌈Real.exp ((p + 3) ^ 11)⌉₊ : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one (by positivity)).trans (Real.exp_le_exp.mpr hqbr)
  have hgrid : (l : ℝ) ≤ Real.exp q := by
    apply hlp.trans (Real.exp_le_exp.mpr _)
    have hpow := pow_le_pow_right₀ (by linarith : 1 ≤ p + 3) (by decide : 9 ≤ 11)
    dsimp [q]
    linarith
  obtain ⟨N, hN, hinner, houter, hgeom⟩ := D.filtration.exists_square_rational_model
    b w hlayers D.lattice hl (one_le_ceil_exp _)
    (fun i j k => rationalHeightLE_ceil_exp (hc i j k)) hin hout hq h2dim hH hgrid
  refine ⟨b, w, hlayers, N, hN, hinner, houter, hb, ?_⟩
  have he : q + 2 = (p + 3) ^ 11 + 2 * p + 5 := by dsimp [q]; ring
  simpa only [he, squareGeometryBudget] using hgeom

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_controlled_vertical_decomposition (T : D.Niltest w)
    {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p)
    (δ : ℝ) (hδ : 0 < δ) (hδp : δ⁻¹ ≤ Real.exp p) :
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (η : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest w),
      (Fintype.card J : ℝ) ≤ Real.exp (verticalDecompositionBudget p) ∧
      (∀ j i, rationalLogHeight (η j (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ j, (U j).ComplexityLE p ∧ (U j).orbit = T.orbit) ∧
      (∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
        (U j).observable (z • x) =
          character ((realifyFunctional (η j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x) ∧
      (∀ j, (∃ x, (U j).observable x ≠ 0) → ∀ z : D.RealGroup,
        z ∈ D.filtration.realification.subgroup s → z ∈ D.realLattice →
          ∃ n : ℤ, realifyFunctional (η j) z.coord = n) ∧
      (∀ (z : D.RealGroup) (c : ℂ), (∀ x, T.observable (z • x) = c * T.observable x) →
        ∀ j x, (U j).observable (z • x) = c * (U j).observable x) ∧
      (∀ x, ‖(∑ j, (U j).observable x) - T.observable x‖ ≤ δ) ∧
      ∀ x : σ → ℤ, ‖(∑ j, (U j).eval x) - T.eval x‖ ≤ δ := by
  let := D.metricSpace
  have hK : (T.lipBound : ℝ) ≤ Real.exp p := by
    have h := observable_budget hT
    have hB := T.normBound.coe_nonneg
    linarith
  obtain ⟨J, inst, η, v, hcard, hheight, hv, hchar, hpres, herr⟩ :=
    D.exists_controlled_vertical_decomposition hp hT.1 T.observable T.lipBound T.normBound
      T.lipschitz T.norm_le hK δ hδ hδp
  let U : J → D.Niltest w := fun j =>
    { orbit := T.orbit
      observable := v j
      normBound := T.normBound
      lipBound := T.lipBound
      norm_le := (hv j).2
      lipschitz := (hv j).1 }
  refine ⟨J, inst, η, U, hcard, hheight, fun j => ⟨hT, rfl⟩, hchar, ?_, hpres, herr, ?_⟩
  · intro j hne z hz hΓ
    exact vertical_frequency_integral_on_lattice D.filtration D.realLattice (η j) (v j)
      (hchar j) hne z hz hΓ
  · intro x
    exact herr (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x T.orbit))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_vertical_decomposition_preserving_bounds (T : D.Niltest w)
    {p rho : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p) (hrho : 0 < rho)
    (hrhop : rho⁻¹ ≤ Real.exp p) :
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (eta : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest w),
      (Fintype.card J : ℝ) ≤ Real.exp (verticalDecompositionBudget p) ∧
      (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ j, (U j).ComplexityLE p ∧ (U j).orbit = T.orbit ∧
        (U j).normBound = T.normBound ∧ (U j).lipBound = T.lipBound) ∧
      (∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
        (U j).observable (z • x) =
          character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x) ∧
      (∀ j, (∃ x, (U j).observable x ≠ 0) → ∀ z : D.RealGroup,
        z ∈ D.filtration.realification.subgroup s → z ∈ D.realLattice →
          ∃ n : ℤ, realifyFunctional (eta j) z.coord = n) ∧
      (∀ x, ‖(∑ j, (U j).observable x) - T.observable x‖ ≤ rho) ∧
      ∀ x : σ → ℤ, ‖(∑ j, (U j).eval x) - T.eval x‖ ≤ rho := by
  let := D.metricSpace
  have hK : (T.lipBound : ℝ) ≤ Real.exp p := by
    have h := observable_budget hT
    have hB := T.normBound.coe_nonneg
    linarith
  obtain ⟨J, inst, eta, v, hcard, hheight, hv, hchar, _, herr⟩ :=
    D.exists_controlled_vertical_decomposition hp hT.1 T.observable T.lipBound T.normBound
      T.lipschitz T.norm_le hK rho hrho hrhop
  let U : J → D.Niltest w := fun j =>
    { orbit := T.orbit
      observable := v j
      normBound := T.normBound
      lipBound := T.lipBound
      norm_le := (hv j).2
      lipschitz := (hv j).1 }
  refine ⟨J, inst, eta, U, hcard, hheight, fun _ => ⟨hT, rfl, rfl, rfl⟩, hchar, ?_, herr, ?_⟩
  · intro j hne z hz hGamma
    exact vertical_frequency_integral_on_lattice D.filtration D.realLattice (eta j) (v j)
      (hchar j) hne z hz hGamma
  · intro x
    exact herr (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x T.orbit))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
