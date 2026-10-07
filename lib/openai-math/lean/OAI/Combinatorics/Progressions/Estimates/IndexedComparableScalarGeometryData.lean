import OAI.Combinatorics.Progressions.Geometry.CanonicalScalarParameterBox
import OAI.Combinatorics.Progressions.Geometry.IndexedComparableScalarParameterBox
import OAI.Combinatorics.Progressions.Lattices.AffineCommonReferenceBudget
import OAI.Combinatorics.Progressions.Sampling.SelectedPhysicalGridBudget

namespace OAI

section

namespace Erdos3

noncomputable def scalarTransferCapLog (b : ℕ) (Z : ℝ) : ℝ := (b : ℝ) * (Z + 2) + 1

noncomputable def scalarTransferAccuracyLog (b : ℕ) (p Z : ℝ) : ℝ :=
  3 * p + scalarTransferCapLog b Z + 10

noncomputable def scalarTransferCellLog (common : ℝ) (b : ℕ) (p Z U : ℝ) : ℝ :=
  65536 * (common + 3) ^ 4 + Z * b + scalarTransferAccuracyLog b p Z + U + 1

theorem scalarTransferAllocatedLogs_bounds (b : ℕ) {common p Z U : ℝ}
    (hcommon : 0 ≤ common) (hp : 0 ≤ p) (hZ : 0 ≤ Z) (hU : 0 ≤ U) :
    0 ≤ scalarTransferCapLog b Z ∧ 0 ≤ scalarTransferAccuracyLog b p Z ∧
    0 ≤ scalarTransferCellLog common b p Z U ∧
    65536 * (common + 3) ^ 4 ≤ scalarTransferCellLog common b p Z U ∧
    Z * b + scalarTransferAccuracyLog b p Z + U + 1 ≤ scalarTransferCellLog common b p Z U ∧
    Z * b + U + 1 ≤ scalarTransferCellLog common b p Z U := by
  have hc : 0 ≤ scalarTransferCapLog b Z := by unfold scalarTransferCapLog; positivity
  have ha : 0 ≤ scalarTransferAccuracyLog b p Z := by unfold scalarTransferAccuracyLog; positivity
  have hside : 0 ≤ 65536 * (common + 3) ^ 4 := by positivity
  have hb : 0 ≤ Z * (b : ℝ) := mul_nonneg hZ (Nat.cast_nonneg b)
  unfold scalarTransferCellLog
  exact ⟨hc, ha, by positivity, by linarith, by linarith, by linarith⟩

theorem scalarTransferMarginalAccuracy_eq_exp (b : ℕ) (p Z : ℝ) :
    scalarTransferMarginalAccuracy (3 * p) (scalarTransferCapLog b Z) =
      Real.exp (-scalarTransferAccuracyLog b p Z) := rfl

end Erdos3

end

section

namespace Erdos3

noncomputable def scalarInitialReferenceInput (m n d : ℕ) (p P0 : ℝ) : ℝ :=
  let Z := replacementCommonInputLog m n d P0
  let G := 2 * physicalPairCoefficientLog n d Z + 2
  G + Z + P0 + m + n + d + scalarTransferTail (3 * p) + p + 20

theorem scalarInitialReferenceInput_bounds (m n d : ℕ) {p P0 : ℝ} (hp : 0 ≤ p) (hP0 : 0 ≤ P0) :
    let Z := replacementCommonInputLog m n d P0
    let G := 2 * physicalPairCoefficientLog n d Z + 2
    let U := scalarInitialReferenceInput m n d p P0
    0 ≤ U ∧ Z ≤ U ∧ G + P0 + 2 ≤ U ∧ P0 ≤ U ∧
      (m : ℝ) ≤ U ∧ (n : ℝ) ≤ U ∧ (d : ℝ) ≤ U ∧ scalarTransferTail (3 * p) ≤ U ∧ p ≤ U := by
  intro Z G U
  have hZ : 0 ≤ Z := (replacementCommonInputLog_bounds m n d hP0).1
  have hG : 0 ≤ G := by
    have h := (physicalPairCoefficientLog_bounds n d hZ).1
    dsimp only [G]
    linarith
  have hT : 0 ≤ scalarTransferTail (3 * p) := by unfold scalarTransferTail; positivity
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  dsimp only [U, scalarInitialReferenceInput]
  dsimp only [G, Z] at hG hZ ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem physicalPairCoefficientLog_mono_dimension (n : ℕ) {d e : ℕ} {P : ℝ}
    (hde : d ≤ e) (hP : 0 ≤ P) : physicalPairCoefficientLog n d P ≤ physicalPairCoefficientLog n e P := by
  have hde' : (d : ℝ) ≤ e := by exact_mod_cast hde
  unfold physicalPairCoefficientLog smoothPairErrorLog smoothPairRowErrorLog
  gcongr

end Erdos3

end

section

namespace Erdos3

noncomputable def scalarCombinedLogThreshold (n d b : ℕ)
    (p P0 Z G refCost cellLog meshLog : ℝ) : ℝ :=
  refCost + p + scalarTransferTail (3 * p) + 2 * physicalReplacementThresholdLog n d b Z +
    G + P0 + 4 * meshLog + 2 * cellLog + 2 * Z + 100

theorem physicalReplacementThresholdLog_mono_dimension (n b : ℕ) {d e : ℕ} {Z : ℝ}
    (hde : d ≤ e) (hZ : 0 ≤ Z) :
    physicalReplacementThresholdLog n d b Z ≤ physicalReplacementThresholdLog n e b Z := by
  have h := physicalPairCoefficientLog_mono_dimension n hde hZ
  unfold physicalReplacementThresholdLog
  linarith

theorem scalarCombinedLogThreshold_bounds (n d b : ℕ)
    {p P0 Z G refCost cellLog meshLog : ℝ}
    (hp : 0 ≤ p) (hP0 : 0 ≤ P0) (hZ : 0 ≤ Z) (hG : 0 ≤ G)
    (href : 0 ≤ refCost) (hcell : 0 ≤ cellLog) (hmesh : 0 ≤ meshLog) :
    let S := scalarCombinedLogThreshold n d b p P0 Z G refCost cellLog meshLog
    0 ≤ S ∧ refCost ≤ S ∧ p + scalarTransferTail (3 * p) + 4 ≤ S ∧
      Z + P0 ≤ S ∧ 2 * physicalReplacementThresholdLog n d b Z + 16 ≤ S ∧
      G + max refCost cellLog + 2 ≤ S ∧ 4 * meshLog + 18 + cellLog + Z + 2 ≤ S := by
  intro S
  have hT : 0 ≤ scalarTransferTail (3 * p) := by unfold scalarTransferTail; positivity
  have hR := (physicalReplacementThresholdLog_bounds n d b hZ).1
  have hmax : max refCost cellLog ≤ refCost + cellLog := max_le (by linarith) (by linarith)
  dsimp only [S, scalarCombinedLogThreshold]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem four_mul_exp_le_exp_add_two (x : ℝ) : 4 * Real.exp x ≤ Real.exp (x + 2) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      4 = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) htwo 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  calc
    _ ≤ Real.exp 2 * Real.exp x := mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

theorem scalarCombinedLogThreshold_size_conditions {I : Type*} (n d b exponent : ℕ)
    {p P0 Z G refCost cellLog meshLog budget L : ℝ} (H : I → ℝ)
    (hp : 0 ≤ p) (hP0 : 0 ≤ P0) (hZ : 0 ≤ Z) (hG : 0 ≤ G)
    (href : 0 ≤ refCost) (hcell : 0 ≤ cellLog) (hmesh : 0 ≤ meshLog)
    (hbudget : scalarCombinedLogThreshold n d b p P0 Z G refCost cellLog meshLog ≤ budget)
    (hL : Real.exp budget ≤ L) (hH : ∀ i, Real.exp budget * L ^ exponent ≤ H i) :
    1 ≤ L ∧ Real.exp (Z + P0) ≤ L ∧
    (∀ i, Real.exp (2 * physicalReplacementThresholdLog n d b Z + 16) * L ^ exponent ≤ H i) ∧
    (∀ i, 4 * Real.exp (G + max refCost cellLog) ≤ H i) ∧
    4 * Real.exp (4 * meshLog + 18 + cellLog + Z) ≤ L ∧
    (∀ i, 4 * Real.exp (4 * meshLog + 18 + cellLog) * L ^ exponent ≤ H i) := by
  obtain ⟨hS, _, _, hLP, hRP, hFP, hMP⟩ := scalarCombinedLogThreshold_bounds n d b hp hP0 hZ hG href hcell hmesh
  have hLone : 1 ≤ L := (Real.one_le_exp_iff.mpr (hS.trans hbudget)).trans hL
  have hpow : 1 ≤ L ^ exponent := one_le_pow₀ hLone
  have hHbase (i) : Real.exp budget ≤ H i := by
    have hf : Real.exp budget ≤ Real.exp budget * L ^ exponent := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg budget)
    exact hf.trans (hH i)
  refine ⟨hLone, (Real.exp_le_exp.mpr (hLP.trans hbudget)).trans hL, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hRP.trans hbudget))
      (pow_nonneg (zero_le_one.trans hLone) exponent)).trans (hH i)
  · intro i
    exact ((four_mul_exp_le_exp_add_two _).trans (Real.exp_le_exp.mpr (hFP.trans hbudget))).trans (hHbase i)
  · exact ((four_mul_exp_le_exp_add_two _).trans (Real.exp_le_exp.mpr (hMP.trans hbudget))).trans hL
  · intro i
    have hm : 4 * meshLog + 18 + cellLog + 2 ≤ budget := by linarith [hMP.trans hbudget]
    exact (mul_le_mul_of_nonneg_right ((four_mul_exp_le_exp_add_two _).trans (Real.exp_le_exp.mpr hm))
      (pow_nonneg (zero_le_one.trans hLone) exponent)).trans (hH i)

end Erdos3

end

section

namespace Erdos3

noncomputable def scalarInitialPowerInputPolynomial (d A : ℕ) : Polynomial ℕ :=
  let X := Polynomial.X
  let P := (X + 2) ^ A
  let M := Polynomial.C (d + 1) * X
  let D := Polynomial.C d
  let input := M * (P + 3) + X * P + 2 * (X + 1) + P + 1
  let Z := 4 * (6 * input + P + 3 * D + 10) + 2 * P + 10
  let row := (16 + 4 * D) * Z + 16 * D + 48
  let error := Z + row + X * (row + 6 * Z + 12)
  let G := 2 * (30 + 2 * X * Z + 2 * X + error + X * (5 * Z + 11) + 10 * Z + 4 * (2 + D)) + 2
  G + Z + P + M + X + D + 2 * (3 * X + 10) + X + 20

theorem scalarInitialReferenceInput_le_powerInputPolynomial (m n d A : ℕ) {p P₀ : ℝ}
    (hp : 0 ≤ p) (hP₀ : 0 ≤ P₀) (hm : (m : ℝ) ≤ (d + 1 : ℝ) * p) (hn : (n : ℝ) ≤ p) (hP : P₀ ≤ (p + 2) ^ A) :
    scalarInitialReferenceInput m n d p P₀ ≤
      (scalarInitialPowerInputPolynomial d A).eval₂ (Nat.castRingHom ℝ) p := by
  simp [scalarInitialReferenceInput, scalarInitialPowerInputPolynomial,
    replacementCommonInputLog, replacementCutoffInputLog, physicalReplacementInputLog,
    physicalPairCoefficientLog, smoothPairErrorLog, smoothPairRowErrorLog, scalarTransferTail, Polynomial.eval₂_pow]
  gcongr

theorem exists_scalarInitialReferenceInput_polynomial_input_power (d A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (m n : ℕ) (p P₀ : ℝ), 0 ≤ p → 0 ≤ P₀ →
      (m : ℝ) ≤ (d + 1 : ℝ) * p → (n : ℝ) ≤ p → P₀ ≤ (p + 2) ^ A →
      scalarInitialReferenceInput m n d p P₀ ≤ (p + 2) ^ C := by
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget (scalarInitialPowerInputPolynomial d A)
  refine ⟨C, hC, ?_⟩
  intro m n p P₀ hp hP₀ hm hn hP
  exact (scalarInitialReferenceInput_le_powerInputPolynomial m n d A hp hP₀ hm hn hP).trans (hbound p hp)

end Erdos3

end

section

namespace Erdos3

theorem unconditionedSpatialWidthCutoff_le_exp {P Q W τ : ℝ}
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hW : W ≤ Real.exp Q)
    (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    unconditionedSpatialWidthCutoff W τ 1 ≤ Real.exp (Q + 2 * P + 16) := by
  have heP : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have heQ : 1 ≤ Real.exp Q := Real.one_le_exp_iff.mpr hQ
  have hfour : (4 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h128 : (128 : ℝ) ≤ Real.exp 16 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 7
    have hp' : (128 : ℝ) ≤ Real.exp 7 := by
      norm_num [← Real.exp_nat_mul] at hp
      exact hp
    exact hp'.trans (Real.exp_le_exp.mpr (by norm_num))
  have hmax : max (8 * (probabilityProfileLipschitz : ℝ)) 1 ≤ 8 * Real.exp P :=
    max_le (mul_le_mul_of_nonneg_left hprofile (by norm_num)) (by linarith)
  unfold unconditionedSpatialWidthCutoff
  apply max_le
  · calc
      4 / τ ≤ Real.exp 16 * Real.exp P := by
        rw [div_eq_mul_inv]
        exact mul_le_mul hfour hτP (inv_nonneg.mpr hτ.le) (Real.exp_nonneg _)
      _ = Real.exp (P + 16) := by rw [← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · calc
      8 * (1 + W) * max (8 * (probabilityProfileLipschitz : ℝ)) 1 / τ ≤
          8 * (2 * Real.exp Q) * (8 * Real.exp P) * Real.exp P := by
        rw [div_eq_mul_inv]
        gcongr
        linarith
      _ = 128 * Real.exp (Q + 2 * P) := by rw [Real.exp_add, two_mul P, Real.exp_add]; ring
      _ ≤ Real.exp 16 * Real.exp (Q + 2 * P) :=
        mul_le_mul_of_nonneg_right h128 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem canonicalScalarPhysicalSize {X : Type*} (d : ℕ) {P budget W τ : ℝ}
    (hP : 0 ≤ P) (hbudget : 0 ≤ budget)
    (hd : (d : ℝ) ≤ Real.exp P) (hW : W ≤ 2 * d * Real.exp budget)
    (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (N : X → ℕ)
    (hN : ∀ i, Real.exp ((d + 4 : ℝ) * (budget + P + 20)) ≤ (N i : ℝ)) :
    (∀ i, unconditionedSpatialWidthCutoff W τ 1 ≤ (N i : ℝ)) ∧
      ∀ i, Real.exp budget * (Real.exp budget) ^ (d + 1) ≤ 2 * (N i : ℝ) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hWexp : W ≤ Real.exp (budget + P + 1) := by
    calc
      W ≤ 2 * d * Real.exp budget := hW
      _ ≤ Real.exp 1 * Real.exp P * Real.exp budget := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hcut := unconditionedSpatialWidthCutoff_le_exp hP
    (show 0 ≤ budget + P + 1 by positivity) hWexp hτ hτP hprofile
  constructor
  · intro i
    apply hcut.trans
    apply (Real.exp_le_exp.mpr ?_).trans (hN i)
    nlinarith [mul_nonneg hd0 hbudget, mul_nonneg hd0 hP]
  · intro i
    calc
      _ = Real.exp (((d : ℝ) + 2) * budget) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        push_cast
        ring
      _ ≤ Real.exp (((d : ℝ) + 4) * (budget + P + 20)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hd0 hP]
      _ ≤ (N i : ℝ) := hN i
      _ ≤ 2 * (N i : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) (N i)]

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

structure CanonicalScalarGeometryData (d : ℕ) {I : Type*} [Fintype I]
    (L W τ : ℝ) (parameters : Fin d → ℕ) (N : I → ℕ) : Prop where
  hτ : 0 < τ
  hτ1 : τ ≤ 1
  hL : 1 ≤ L
  hwidth : ∀ z : Option (Fin d) × I, 0 < trimmedSpatialWidths W τ N z
  hmargin : ∀ i, 2 * spatialTrimMargin τ N i < N i
  hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0}
    (trimmedSpatialWidths (K := Fin d) W τ N) z
  hparam : ∀ j, (0 : ℤ) < (parameters j : ℤ)
  sourceGeometry :
    (∀ t : Option (Fin d) × I, smoothPairCoefficientScale (2 * (N t.2 : ℝ)) L t.1 ≤
      canonicalJointFrameWindowConstant d τ *
        ((jointFrameSourceHi N (trimmedSpatialWidths W τ N) t -
          jointFrameSourceLo (trimmedSpatialWidths W τ N) t : ℤ) : ℝ)) ∧
    (∀ z ∈ Fintype.piFinset (fun t : Option (Fin d) × I =>
        Finset.Ico (jointFrameSourceLo (trimmedSpatialWidths W τ N) t)
          (jointFrameSourceHi N (trimmedSpatialWidths W τ N) t)), ∀ t,
      |(z t : ℝ) - (0 : ℤ)| ≤ smoothPairCoefficientScale (2 * (N t.2 : ℝ)) L t.1 / 2) ∧
    (∀ k : Fin d, ∀ i,
      |(jointFrameSourceLo (trimmedSpatialWidths W τ N) (some k, i) : ℝ)| ≤
        2 * (N i : ℝ) / L) ∧
    (∀ k : Fin d, ∀ i,
      |(jointFrameSourceHi N (trimmedSpatialWidths W τ N) (some k, i) : ℝ)| ≤
        2 * (N i : ℝ) / L)
  hroot : ∀ i, trimmedSpatialWidths (K := Fin d) W τ N (none, i) ≤
    (spatialTrimMargin τ N i : ℝ)
  hloss : (∑ i, 2 * (spatialTrimMargin τ N i : ℝ) / N i) ≤ 1 / 2
  hscale : ∀ z : Option (Fin d) × I, 8 * (probabilityProfileLipschitz : ℝ) ≤
    residueProfileWidth (fun _ : I => 1) (trimmedSpatialWidths W τ N) z
  physicalSize : ∀ i, L * L ^ (d + 1) ≤ 2 * (N i : ℝ)
  parameterBox :
    (∀ j, (0 : ℤ) < (parameters j : ℤ)) ∧
    0 < L ∧
    (∀ j, L ≤ (((parameters j : ℤ) - 0 : ℤ) : ℝ)) ∧
    (∀ j, (parameters j : ℤ) - 0 ≤ (canonicalScalarParameterRadius L : ℤ)) ∧
    (canonicalScalarParameterRadius L : ℝ) ≤ 3 * L ∧
    1 * L ≤ L ∧
    |(0 : ℝ) / L| ≤ 2 ∧
    (∀ j, |(((parameters j : ℤ) : ℝ)) / L| ≤ 2) ∧
    0 ≤ W ∧ L ≤ W ∧ W ≤ 2 * (d : ℝ) * L

theorem canonicalScalarGeometryData {I : Type*} [Fintype I]
    (d : ℕ) (hd : 2 ≤ d) {P0 budget σ : ℝ}
    (hP0 : 0 ≤ P0) (hbudget0 : 0 ≤ budget)
    (hdP0 : (d : ℝ) ≤ Real.exp P0)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hτP0 : (unconditionedSpatialTrimFraction (Fintype.card I) σ)⁻¹ ≤ Real.exp P0)
    (parameters : Fin d → ℕ)
    (hlo : ∀ j, Real.exp budget ≤ (parameters j : ℝ))
    (hhi : ∀ j, (parameters j : ℝ) ≤ 2 * Real.exp budget)
    (N : I → ℕ)
    (hN : ∀ i, Real.exp (((d : ℝ) + 4) * (budget + P0 + 20)) ≤ (N i : ℝ)) :
    CanonicalScalarGeometryData d (Real.exp budget) (∑ j, (parameters j : ℝ))
      (unconditionedSpatialTrimFraction (Fintype.card I) σ) parameters N := by
  let τ := unconditionedSpatialTrimFraction (Fintype.card I) σ
  let L := Real.exp budget
  let W := ∑ j, (parameters j : ℝ)
  have hτ : 0 < τ := (unconditionedSpatialTrimFraction_bounds (Fintype.card I) hσ hσ1).1
  have hτ1 : τ ≤ 1 :=
    ((unconditionedSpatialTrimFraction_bounds (Fintype.card I) hσ hσ1).2.1).trans (by norm_num)
  have hL : 1 ≤ L := Real.one_le_exp_iff.mpr hbudget0
  have hbox := canonicalScalarParameterBox_bounds hd hL parameters hlo hhi
  obtain ⟨hparam, hLpos, hparSide, hparRadius, hrad, hrelative, hleft, hright,
    hW0, hWL, hWbound⟩ := hbox
  have hphysical := canonicalScalarPhysicalSize d hP0 hbudget0 hdP0 hWbound hτ hτP0 hprofile N hN
  obtain ⟨_, _, hwidth, hscale, hwide, hmargin, hboundary⟩ :=
    unconditionedSpatialWidthBudget (K := Fin d) hW0 hσ hσ1 N hphysical.1
  obtain ⟨hZ, _⟩ := exists_selectedResidue_physical_cap (0 : Fin d → ℤ)
    (fun _ : I => 1) (fun _ => by decide) {0} (Finset.singleton_nonempty _)
    (trimmedSpatialWidths W τ N) hwidth hscale
  have hgeometry := canonicalJointFrame_source_geometry (K := Fin d) d N hL hWL hWbound hτ hτ1
    (fun i => by simpa only [trimmedSpatialWidths, centeredSpatialWidths, one_mul]
      using hwide (some (⟨0, by omega⟩ : Fin d), i))
  have hroot (i : I) : trimmedSpatialWidths (K := Fin d) W τ N (none, i) ≤
      (spatialTrimMargin τ N i : ℝ) := by
    have hceil := Nat.le_ceil (τ * (N i : ℝ) / 4)
    change τ * ((N i : ℝ) / 8) ≤ (⌈τ * (N i : ℝ) / 4⌉₊ : ℝ)
    nlinarith [mul_nonneg hτ.le (Nat.cast_nonneg (α := ℝ) (N i))]
  have hloss : (∑ i, 2 * (spatialTrimMargin τ N i : ℝ) / N i) ≤ 1 / 2 := by
    linarith
  exact {
    hτ := hτ
    hτ1 := hτ1
    hL := hL
    hwidth := hwidth
    hmargin := hmargin
    hZ := hZ
    hparam := hparam
    sourceGeometry := by simpa only [Fintype.mem_piFinset, L, τ] using hgeometry
    hroot := hroot
    hloss := hloss
    hscale := hscale
    physicalSize := hphysical.2
    parameterBox := ⟨hparam, hLpos, hparSide, hparRadius, hrad, hrelative, hleft,
      hright, hW0, hWL, hWbound⟩ }

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

structure ComparableScalarGeometryData (d r : ℕ) {I : Type*} [Fintype I]
    (L W τ : ℝ) (parameters : Fin d → ℕ) (N : I → ℕ) : Prop where
  hτ : 0 < τ
  hτ1 : τ ≤ 1
  hL : 1 ≤ L
  hwidth : ∀ z : Option (Fin d) × I, 0 < trimmedSpatialWidths W τ N z
  hmargin : ∀ i, 2 * spatialTrimMargin τ N i < N i
  hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0}
    (trimmedSpatialWidths (K := Fin d) W τ N) z
  hparam : ∀ j, (0 : ℤ) < (parameters j : ℤ)
  sourceGeometry :
    (∀ t : Option (Fin d) × I, smoothPairCoefficientScale (2 * (N t.2 : ℝ)) L t.1 ≤
      canonicalJointFrameWindowConstant (r*d) τ *
        ((jointFrameSourceHi N (trimmedSpatialWidths W τ N) t -
          jointFrameSourceLo (trimmedSpatialWidths W τ N) t : ℤ) : ℝ)) ∧
    (∀ z ∈ Fintype.piFinset (fun t : Option (Fin d) × I =>
        Finset.Ico (jointFrameSourceLo (trimmedSpatialWidths W τ N) t)
          (jointFrameSourceHi N (trimmedSpatialWidths W τ N) t)), ∀ t,
      |(z t : ℝ) - (0 : ℤ)| ≤ smoothPairCoefficientScale (2 * (N t.2 : ℝ)) L t.1 / 2) ∧
    (∀ k : Fin d, ∀ i,
      |(jointFrameSourceLo (trimmedSpatialWidths W τ N) (some k, i) : ℝ)| ≤
        2 * (N i : ℝ) / L) ∧
    (∀ k : Fin d, ∀ i,
      |(jointFrameSourceHi N (trimmedSpatialWidths W τ N) (some k, i) : ℝ)| ≤
        2 * (N i : ℝ) / L)
  hroot : ∀ i, trimmedSpatialWidths (K := Fin d) W τ N (none, i) ≤
    (spatialTrimMargin τ N i : ℝ)
  hloss : (∑ i, 2 * (spatialTrimMargin τ N i : ℝ) / N i) ≤ 1 / 2
  hscale : ∀ z : Option (Fin d) × I, 8 * (probabilityProfileLipschitz : ℝ) ≤
    residueProfileWidth (fun _ : I => 1) (trimmedSpatialWidths W τ N) z
  physicalSize : ∀ i, L * L ^ (d + 1) ≤ 2 * (N i : ℝ)
  parameterBox :
    (∀ j, (0 : ℤ) < (parameters j : ℤ)) ∧
    0 < L ∧
    (∀ j, L ≤ (((parameters j : ℤ) - 0 : ℤ) : ℝ)) ∧
    (∀ j, (parameters j : ℤ) - 0 ≤ (comparableScalarParameterRadius (r : ℝ) L : ℤ)) ∧
    (comparableScalarParameterRadius (r : ℝ) L : ℝ) ≤ ((r : ℝ) + 1) * L ∧
    1 * L ≤ L ∧
    |(0 : ℝ) / L| ≤ r ∧
    (∀ j, |(((parameters j : ℤ) : ℝ)) / L| ≤ r) ∧
    0 ≤ W ∧ L ≤ W ∧ W ≤ (r : ℝ) * d * L

theorem comparableScalarGeometryData {I : Type*} [Fintype I]
    (d r : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r) {P0 budget σ : ℝ}
    (hP0 : 0 ≤ P0) (hbudget0 : 0 ≤ budget)
    (hDP0 : ((r*d : ℕ) : ℝ) ≤ Real.exp P0)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hτP0 : (unconditionedSpatialTrimFraction (Fintype.card I) σ)⁻¹ ≤ Real.exp P0)
    (parameters : Fin d → ℕ)
    (hlo : ∀ j, Real.exp budget ≤ (parameters j : ℝ))
    (hhi : ∀ j, (parameters j : ℝ) ≤ (r : ℝ) * Real.exp budget)
    (N : I → ℕ)
    (hN : ∀ i, Real.exp ((((r*d : ℕ) : ℝ) + 4) * (budget + P0 + 20)) ≤ (N i : ℝ)) :
    ComparableScalarGeometryData d r (Real.exp budget) (∑ j, (parameters j : ℝ))
      (unconditionedSpatialTrimFraction (Fintype.card I) σ) parameters N := by
  let τ := unconditionedSpatialTrimFraction (Fintype.card I) σ
  let L := Real.exp budget
  let W := ∑ j, (parameters j : ℝ)
  have hτ : 0 < τ := (unconditionedSpatialTrimFraction_bounds (Fintype.card I) hσ hσ1).1
  have hτ1 : τ ≤ 1 :=
    ((unconditionedSpatialTrimFraction_bounds (Fintype.card I) hσ hσ1).2.1).trans (by norm_num)
  have hL : 1 ≤ L := Real.one_le_exp_iff.mpr hbudget0
  have hbox := comparableScalarParameterBox_bounds hd (by exact_mod_cast hr) hL parameters hlo hhi
  obtain ⟨hparam, hLpos, hparSide, hparRadius, hrad, hrelative, hleft, hright,
    hW0, hWL, hWbound⟩ := hbox
  have hWgeometry : W ≤ 2 * ((r*d : ℕ) : ℝ) * L := by
    have hh : W ≤ ((r*d : ℕ) : ℝ) * L := by
      simpa only [Nat.cast_mul] using hWbound
    have hp : 0 ≤ ((r*d : ℕ) : ℝ) * L := mul_nonneg (Nat.cast_nonneg _) hLpos.le
    nlinarith
  have hphysical := canonicalScalarPhysicalSize (r*d) hP0 hbudget0 hDP0
    hWgeometry hτ hτP0 hprofile N hN
  have hdD : d ≤ r*d := by
    have hh := Nat.mul_le_mul_right d hr
    omega
  have hphysicalActual (i : I) : L * L^(d+1) ≤ 2*(N i : ℝ) :=
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (Nat.add_le_add_right hdD 1)) hLpos.le).trans (hphysical.2 i)
  obtain ⟨_, _, hwidth, hscale, hwide, hmargin, hboundary⟩ :=
    unconditionedSpatialWidthBudget (K := Fin d) hW0 hσ hσ1 N hphysical.1
  obtain ⟨hZ, _⟩ := exists_selectedResidue_physical_cap (0 : Fin d → ℤ)
    (fun _ : I => 1) (fun _ => by decide) {0} (Finset.singleton_nonempty _)
    (trimmedSpatialWidths W τ N) hwidth hscale
  have hgeometry := canonicalJointFrame_source_geometry (K := Fin d) (r*d) N hL hWL hWgeometry hτ hτ1
    (fun i => by simpa only [trimmedSpatialWidths, centeredSpatialWidths, one_mul]
      using hwide (some (⟨0, by omega⟩ : Fin d), i))
  have hroot (i : I) : trimmedSpatialWidths (K := Fin d) W τ N (none, i) ≤
      (spatialTrimMargin τ N i : ℝ) := by
    have hceil := Nat.le_ceil (τ * (N i : ℝ) / 4)
    change τ * ((N i : ℝ) / 8) ≤ (⌈τ * (N i : ℝ) / 4⌉₊ : ℝ)
    nlinarith [mul_nonneg hτ.le (Nat.cast_nonneg (α := ℝ) (N i))]
  have hloss : (∑ i, 2 * (spatialTrimMargin τ N i : ℝ) / N i) ≤ 1 / 2 := by
    linarith
  exact {
    hτ := hτ
    hτ1 := hτ1
    hL := hL
    hwidth := hwidth
    hmargin := hmargin
    hZ := hZ
    hparam := hparam
    sourceGeometry := by simpa only [Fintype.mem_piFinset, L, τ] using hgeometry
    hroot := hroot
    hloss := hloss
    hscale := hscale
    physicalSize := hphysicalActual
    parameterBox := ⟨hparam, hLpos, hparSide, hparRadius, hrad, hrelative, hleft,
      hright, hW0, hWL, hWbound⟩ }

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

structure IndexedComparableScalarGeometryData (d r : ℕ)
    {K I : Type*} [Fintype K] [Fintype I]
    (L W τ : ℝ) (parameters : K → ℕ) (N : I → ℕ) : Prop where
  hτ : 0 < τ
  hτ1 : τ ≤ 1
  hL : 1 ≤ L
  hwidth : ∀ z : Option K × I, 0 < trimmedSpatialWidths W τ N z
  hmargin : ∀ i, 2 * spatialTrimMargin τ N i < N i
  hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0}
    (trimmedSpatialWidths (K := K) W τ N) z
  hparam : ∀ j, (0 : ℤ) < (parameters j : ℤ)
  sourceGeometry :
    (∀ t : Option K × I, smoothPairCoefficientScale (2 * (N t.2 : ℝ)) L t.1 ≤
      canonicalJointFrameWindowConstant (r*d) τ *
        ((jointFrameSourceHi N (trimmedSpatialWidths W τ N) t -
          jointFrameSourceLo (trimmedSpatialWidths W τ N) t : ℤ) : ℝ)) ∧
    (∀ z ∈ Fintype.piFinset (fun t : Option K × I =>
        Finset.Ico (jointFrameSourceLo (trimmedSpatialWidths W τ N) t)
          (jointFrameSourceHi N (trimmedSpatialWidths W τ N) t)), ∀ t,
      |(z t : ℝ) - (0 : ℤ)| ≤ smoothPairCoefficientScale (2 * (N t.2 : ℝ)) L t.1 / 2) ∧
    (∀ k : K, ∀ i,
      |(jointFrameSourceLo (trimmedSpatialWidths W τ N) (some k, i) : ℝ)| ≤
        2 * (N i : ℝ) / L) ∧
    (∀ k : K, ∀ i,
      |(jointFrameSourceHi N (trimmedSpatialWidths W τ N) (some k, i) : ℝ)| ≤
        2 * (N i : ℝ) / L)
  hroot : ∀ i, trimmedSpatialWidths (K := K) W τ N (none, i) ≤
    (spatialTrimMargin τ N i : ℝ)
  hloss : (∑ i, 2 * (spatialTrimMargin τ N i : ℝ) / N i) ≤ 1 / 2
  hscale : ∀ z : Option K × I, 8 * (probabilityProfileLipschitz : ℝ) ≤
    residueProfileWidth (fun _ : I => 1) (trimmedSpatialWidths W τ N) z
  physicalSize : ∀ i, L * L ^ (d + 1) ≤ 2 * (N i : ℝ)
  parameterBox :
    (∀ j, (0 : ℤ) < (parameters j : ℤ)) ∧
    0 < L ∧
    (∀ j, L ≤ (((parameters j : ℤ) - 0 : ℤ) : ℝ)) ∧
    (∀ j, (parameters j : ℤ) - 0 ≤ (comparableScalarParameterRadius (r : ℝ) L : ℤ)) ∧
    (comparableScalarParameterRadius (r : ℝ) L : ℝ) ≤ ((r : ℝ) + 1) * L ∧
    1 * L ≤ L ∧
    |(0 : ℝ) / L| ≤ r ∧
    (∀ j, |(((parameters j : ℤ) : ℝ)) / L| ≤ r) ∧
    0 ≤ W ∧ L ≤ W ∧ W ≤ (r : ℝ) * d * L

theorem indexedComparableScalarGeometryData
    (d r : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    {K I : Type*} [Fintype K] [Fintype I]
    (hK : Fintype.card K = d) {P0 budget σ : ℝ}
    (hP0 : 0 ≤ P0) (hbudget0 : 0 ≤ budget)
    (hDP0 : ((r*d : ℕ) : ℝ) ≤ Real.exp P0)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hτP0 : (unconditionedSpatialTrimFraction (Fintype.card I) σ)⁻¹ ≤ Real.exp P0)
    (parameters : K → ℕ)
    (hlo : ∀ j, Real.exp budget ≤ (parameters j : ℝ))
    (hhi : ∀ j, (parameters j : ℝ) ≤ (r : ℝ) * Real.exp budget)
    (N : I → ℕ)
    (hN : ∀ i, Real.exp ((((r*d : ℕ) : ℝ) + 4) * (budget + P0 + 20)) ≤ (N i : ℝ)) :
    IndexedComparableScalarGeometryData d r (Real.exp budget) (∑ j, (parameters j : ℝ))
      (unconditionedSpatialTrimFraction (Fintype.card I) σ) parameters N := by
  let τ := unconditionedSpatialTrimFraction (Fintype.card I) σ
  let L := Real.exp budget
  let W := ∑ j, (parameters j : ℝ)
  have hτ : 0 < τ := (unconditionedSpatialTrimFraction_bounds (Fintype.card I) hσ hσ1).1
  have hτ1 : τ ≤ 1 :=
    ((unconditionedSpatialTrimFraction_bounds (Fintype.card I) hσ hσ1).2.1).trans (by norm_num)
  have hL : 1 ≤ L := Real.one_le_exp_iff.mpr hbudget0
  have hbox := indexedComparableScalarParameterBox_bounds hd hK (by exact_mod_cast hr) hL parameters hlo hhi
  obtain ⟨hparam, hLpos, hparSide, hparRadius, hrad, hrelative, hleft, hright,
    hW0, hWL, hWbound⟩ := hbox
  have hWgeometry : W ≤ 2 * ((r*d : ℕ) : ℝ) * L := by
    have hh : W ≤ ((r*d : ℕ) : ℝ) * L := by
      simpa only [Nat.cast_mul] using hWbound
    have hp : 0 ≤ ((r*d : ℕ) : ℝ) * L := mul_nonneg (Nat.cast_nonneg _) hLpos.le
    nlinarith
  have hphysical := canonicalScalarPhysicalSize (r*d) hP0 hbudget0 hDP0
    hWgeometry hτ hτP0 hprofile N hN
  have hdD : d ≤ r*d := by
    have hh := Nat.mul_le_mul_right d hr
    omega
  have hphysicalActual (i : I) : L * L^(d+1) ≤ 2*(N i : ℝ) :=
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (Nat.add_le_add_right hdD 1)) hLpos.le).trans (hphysical.2 i)
  obtain ⟨_, _, hwidth, hscale, hwide, hmargin, hboundary⟩ :=
    unconditionedSpatialWidthBudget (K := K) hW0 hσ hσ1 N hphysical.1
  obtain ⟨hZ, _⟩ := exists_selectedResidue_physical_cap (0 : K → ℤ)
    (fun _ : I => 1) (fun _ => by decide) {0} (Finset.singleton_nonempty _)
    (trimmedSpatialWidths W τ N) hwidth hscale
  have hKpos : 0 < Fintype.card K := by omega
  let k₀ : K := Classical.choice (Fintype.card_pos_iff.mp hKpos)
  have hgeometry := canonicalJointFrame_source_geometry (K := K) (r*d) N hL hWL hWgeometry hτ hτ1
    (fun i => by simpa only [trimmedSpatialWidths, centeredSpatialWidths, one_mul]
      using hwide (some k₀, i))
  have hroot (i : I) : trimmedSpatialWidths (K := K) W τ N (none, i) ≤
      (spatialTrimMargin τ N i : ℝ) := by
    have hceil := Nat.le_ceil (τ * (N i : ℝ) / 4)
    change τ * ((N i : ℝ) / 8) ≤ (⌈τ * (N i : ℝ) / 4⌉₊ : ℝ)
    nlinarith [mul_nonneg hτ.le (Nat.cast_nonneg (α := ℝ) (N i))]
  have hloss : (∑ i, 2 * (spatialTrimMargin τ N i : ℝ) / N i) ≤ 1 / 2 := by
    linarith
  exact {
    hτ := hτ
    hτ1 := hτ1
    hL := hL
    hwidth := hwidth
    hmargin := hmargin
    hZ := hZ
    hparam := hparam
    sourceGeometry := by simpa only [Fintype.mem_piFinset, L, τ] using hgeometry
    hroot := hroot
    hloss := hloss
    hscale := hscale
    physicalSize := hphysicalActual
    parameterBox := ⟨hparam, hLpos, hparSide, hparRadius, hrad, hrelative, hleft,
      hright, hW0, hWL, hWbound⟩ }

end Erdos3

end

end OAI
