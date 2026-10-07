import OAI.Combinatorics.Progressions.Estimates.RebasedUnitVerticalObservable

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module
open scoped TensorProduct NNReal

theorem exists_controlled_rank_rebase :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure r) {p : ℝ},
      0 ≤ p → R.ComplexityLE p → ∃ (F : R.AdaptedData) (H : ℕ)
        (_hH : ∀ i j, RationalHeightLE (D.basis.repr (F.basis i) j) H),
        p ≤ (p + C) ^ C ∧ F.rank.ComplexityLE ((p + C) ^ C) ∧
        (∀ K : ℝ≥0, (K : ℝ) ≤ Real.exp p →
          (K * coordinateLipschitzBound d (finrank ℚ L) H : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        ∀ eta : L →ₗ[ℚ] ℚ, (∀ i, rationalLogHeight (eta (D.basis i)) ≤ p) →
          ∀ j, rationalLogHeight (eta (F.basis j)) ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + 3) ^ 11 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + (P + 2) ^ 2 + (X + 3) ^ 4 + X)
  refine ⟨C, hC, ?_⟩
  intro L _ _ s d r _ _ _ _ D R p hp hR
  obtain ⟨F, hF, hb, _⟩ := R.exists_rank_adapted_data hp hR
  let H := ⌈Real.exp (p + 1)⌉₊
  have hH (i j) : RationalHeightLE (D.basis.repr (F.basis i) j) H :=
    rationalHeightLE_ceil_exp (hb i j)
  let q := (p + 3) ^ 11 + p + 2
  have hpow : 0 ≤ (p + 3) ^ 11 := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hfq : (p + 3) ^ 11 ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hHq : (H : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)).trans
      (Real.exp_le_exp.mpr (by dsimp [q]; linarith))
  have hcost : q + (q + 2) ^ 2 + (p + 3) ^ 4 + p ≤ (p + C) ^ C := by
    simpa [P, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hfreq0 : 0 ≤ (p + 3) ^ 4 := by positivity
  have hcomp : q + (q + 2) ^ 2 ≤ (p + C) ^ C := by linarith
  have hqC : q ≤ (p + C) ^ C := (le_add_of_nonneg_right (sq_nonneg _)).trans hcomp
  have hfreq : (p + 3) ^ 4 ≤ (p + C) ^ C := by nlinarith [sq_nonneg (q + 2)]
  have hgeom : F.model.GeometryComplexityLE q := hF.1.mono F.model hfq
  refine ⟨F, H, hH, hpq.trans hqC, hF.mono F.rank (hfq.trans hqC), ?_, ?_⟩
  · intro K hK
    have hcoord := coordinateLipschitzBound_le_exp d (finrank ℚ L) (H : ℝ≥0) hq
      (hR.1.1.trans hpq) hgeom.1 hHq
    calc
      (K * coordinateLipschitzBound d (finrank ℚ L) H : ℝ) ≤
          Real.exp q * Real.exp ((q + 2) ^ 2) :=
        mul_le_mul (hK.trans (Real.exp_le_exp.mpr hpq)) hcoord (by positivity) (Real.exp_nonneg _)
      _ = Real.exp (q + (q + 2) ^ 2) := (Real.exp_add _ _).symm
      _ ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr hcomp
  · intro eta heta j
    have hdim : (Fintype.card (Fin d) : ℝ) ≤ p + 1 := by
      simpa only [Fintype.card_fin] using hR.1.1.trans (show p ≤ p + 1 by linarith)
    have hval := rational_functional_value_logHeight D.basis eta
      (by linarith : 0 ≤ p + 1) hdim (fun i => (heta i).trans (by linarith : p ≤ p + 1))
      (F.basis j) (hb j)
    apply le_trans _ hfreq
    simpa only [show p + 1 + 2 = p + 3 by ring] using hval

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.NativeDegreeRankFamily

open Module
open scoped NNReal

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {s r : ℕ} {A : Type*} {p q : ℝ} (W : NativeDegreeRankFamily s r A p)

def AdaptedCoordinates : Prop := IsCentralLieBasis W.model.basis ∧
  ∀ i j, ∃ c ≤ W.dim, W.rank.filtration.layer i j = basisTail W.model.basis c

noncomputable def rebase (F : W.rank.AdaptedData) (H : ℕ)
    (hH : ∀ i j, RationalHeightLE (W.model.basis.repr (F.basis i) j) H)
    (hpq : p ≤ q) (hRank : F.rank.ComplexityLE q)
    (hLip : (W.vertical.lipBound * coordinateLipschitzBound W.dim (finrank ℚ W.L) H : ℝ) ≤ Real.exp q)
    (hFreq : ∀ i, rationalLogHeight (W.vertical.frequency (F.basis i)) ≤ q) :
    NativeDegreeRankFamily s r A q where
  L := W.L
  dim := finrank ℚ W.L
  model := F.model
  rank := F.rank
  complexity := hRank
  orbit := W.orbit
  normalized := W.normalized
  outputDim := W.outputDim
  output_pos := W.output_pos
  output_bound := W.output_bound.trans (Real.exp_le_exp.mpr hpq)
  vertical := W.vertical.rebase F.toAdaptedModelData H hH hLip hFreq

theorem rebase_eval (F : W.rank.AdaptedData) (H : ℕ)
    (hH : ∀ i j, RationalHeightLE (W.model.basis.repr (F.basis i) j) H)
    (hpq : p ≤ q) (hRank : F.rank.ComplexityLE q)
    (hLip : (W.vertical.lipBound * coordinateLipschitzBound W.dim (finrank ℚ W.L) H : ℝ) ≤ Real.exp q)
    (hFreq : ∀ i, rationalLogHeight (W.vertical.frequency (F.basis i)) ≤ q)
    (i : Fin W.outputDim) (a : A) (n : ℤ) :
    (W.rebase F H hH hpq hRank hLip hFreq).eval i a n = W.eval i a n := rfl

theorem rebase_adapted (F : W.rank.AdaptedData) (H : ℕ)
    (hH : ∀ i j, RationalHeightLE (W.model.basis.repr (F.basis i) j) H)
    (hpq : p ≤ q) (hRank : F.rank.ComplexityLE q)
    (hLip : (W.vertical.lipBound * coordinateLipschitzBound W.dim (finrank ℚ W.L) H : ℝ) ≤ Real.exp q)
    (hFreq : ∀ i, rationalLogHeight (W.vertical.frequency (F.basis i)) ≤ q) :
    (W.rebase F H hH hpq hRank hLip hFreq).AdaptedCoordinates :=
  ⟨F.central, F.rank_layers⟩

end Erdos3.NativeDegreeRankFamily

end

section

namespace Erdos3

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

theorem exists_adapted_rank_family :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {s r : ℕ} {A : Type*} {p : ℝ} (W : NativeDegreeRankFamily s r A p),
      ∃ (V : NativeDegreeRankFamily s r A ((p + C) ^ C)) (hdim : V.outputDim = W.outputDim),
        V.AdaptedCoordinates ∧
        ∀ i a n, V.eval i a n = W.eval (Fin.cast hdim i) a n := by
  obtain ⟨C, hC, hbase⟩ := RationalFilteredNilmanifold.DegreeRankStructure.exists_controlled_rank_rebase
  refine ⟨C, hC, ?_⟩
  intro s r A p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨F, H, hH, hpq, hRank, hLip, hFreq⟩ := hbase W.rank hp W.complexity
  let V := W.rebase F H hH hpq hRank (hLip W.vertical.lipBound W.vertical.lip_bound)
    (hFreq W.vertical.frequency W.vertical.height)
  refine ⟨V, rfl, ?_, ?_⟩
  · exact W.rebase_adapted F H hH hpq hRank _ _
  · intro i a n
    rfl

theorem exists_adapted_correlation_structure :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f),
      ∃ V : NativeCorrelationStructure s r N ((p + C) ^ C) f,
        V.family.AdaptedCoordinates ∧ V.shifts = W.shifts := by
  obtain ⟨C, hC, hbase⟩ := RationalFilteredNilmanifold.DegreeRankStructure.exists_controlled_rank_rebase
  refine ⟨C, hC, ?_⟩
  intro s r N _ p f W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  obtain ⟨F, H, hH, hpq, hRank, hLip, hFreq⟩ := hbase W.family.rank hp W.family.complexity
  let family := W.family.rebase F H hH hpq hRank
    (hLip W.family.vertical.lipBound W.family.vertical.lip_bound)
    (hFreq W.family.vertical.frequency W.family.vertical.height)
  let V : NativeCorrelationStructure s r N ((p + C) ^ C) f := {
    shifts := W.shifts
    nonempty := W.nonempty
    density := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq))
      (Nat.cast_nonneg _)).trans W.density
    mixed := W.mixed.mono hpq
    family := family
    correlation := by
      intro h hh
      obtain ⟨U⟩ := W.correlation h hh
      exact ⟨U.mono hpq⟩
  }
  exact ⟨V, W.family.rebase_adapted F H hH hpq hRank _ _, rfl⟩

end Erdos3

end

end OAI
