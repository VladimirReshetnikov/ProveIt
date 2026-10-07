import OAI.Combinatorics.Progressions.Estimates.CanonicalScalarSourceEnvelope

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def fixedPositiveCoefficientSource (k : ℕ) : NormalizedScalarCubeSource Empty :=
  normalizedUniformCubeSource Empty (k + 1) (k + 1) (Nat.succ_pos k)
    (fun _ => k + 1) (fun _ => (k : ZMod (k + 1)))
    (fun _ => Nat.succ_pos k) (fun _ => le_rfl) (by simp)

@[simp] theorem fixedPositiveCoefficientSource_length (k : ℕ) :
    (fixedPositiveCoefficientSource k).length = k + 1 := rfl

@[simp] theorem fixedPositiveCoefficientSource_weightBound (k : ℕ) :
    (fixedPositiveCoefficientSource k).weightBound = 1 := rfl

@[simp] theorem fixedPositiveCoefficientSource_weightLipschitz (k : ℕ) :
    (fixedPositiveCoefficientSource k).weightLipschitz = 0 := rfl

theorem fixedPositiveCoefficientSource_residueSet (k : ℕ) :
    coefficientResidueSet (k + 1) (k + 1) (k : ZMod (k + 1)) = {(k : ℤ)} := by
  ext z
  simp only [coefficientResidueSet, Finset.mem_filter, Finset.mem_Ico,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hz, he⟩
    have he' : (z : ZMod (k + 1)) = ((k : ℤ) : ZMod (k + 1)) := by
      simpa only [Int.cast_natCast] using he
    rw [ZMod.intCast_eq_intCast_iff', Int.emod_eq_of_lt hz.1 hz.2,
      Int.emod_eq_of_lt (Int.natCast_nonneg k) (by omega)] at he'
    exact he'
  · rintro rfl
    exact ⟨⟨by omega, by omega⟩, by simp⟩

theorem fixedPositiveCoefficientSource_mean (k : ℕ) (f : ℤ → ℝ) :
    (fixedPositiveCoefficientSource k).source.mean (fun x => f (x none : ℤ)) = f k := by
  rw [NormalizedScalarCubeSource.source_coefficient_mean,
    NormalizedScalarCubeSource.coefficientWeights, FiniteProbabilityWeights.ofDensity_mean]
  change (𝔼 z : coefficientResidueSet (k + 1) (k + 1) (k : ZMod (k + 1)),
    (1 : ℝ) * f z.val) = f k
  rw [fixedPositiveCoefficientSource_residueSet]
  simp

theorem fixedPositiveCoefficientSource_complexMean (k : ℕ) (f : ℤ → ℂ) :
    (fixedPositiveCoefficientSource k).source.complexMean (fun x => f (x none : ℤ)) =
      f k := by
  apply Complex.ext
  · rw [FiniteProbabilityWeights.complexMean_re]
    exact fixedPositiveCoefficientSource_mean k (fun x => (f x).re)
  · rw [FiniteProbabilityWeights.complexMean_im]
    exact fixedPositiveCoefficientSource_mean k (fun x => (f x).im)

theorem fixedPositiveCoefficientSource_law (k : ℕ) :
    (fixedPositiveCoefficientSource k).source.toPMF.map (fun x => (x none : ℤ)) =
      PMF.pure (k : ℤ) := by
  ext z
  apply ENNReal.ofReal_toReal (PMF.apply_ne_top _ _) |>.symm.trans
  apply Eq.trans _ (ENNReal.ofReal_toReal (PMF.apply_ne_top _ _))
  congr 1
  rw [FiniteProbabilityWeights.toPMF_map_toReal,
    fixedPositiveCoefficientSource_mean k
      (fun a => @ite ℝ (a = z) (Classical.propDecidable _) 1 0)]
  by_cases h : (k : ℤ) = z
  · simp [h]
  · simp [h, Ne.symm h, PMF.pure_apply]

theorem fixedPositiveCoefficientSource_support (k : ℕ)
    (x : IntegerScalarCubeBox Empty (fixedPositiveCoefficientSource k).length)
    (hx : (fixedPositiveCoefficientSource k).source.weight x ≠ 0) :
    (x none : ℤ) = k := by
  have hx' : x ∈ (fixedPositiveCoefficientSource k).source.toPMF.support := by
    change ENNReal.ofReal ((fixedPositiveCoefficientSource k).source.weight x) ≠ 0
    exact ENNReal.ofReal_ne_zero_iff.mpr
      (lt_of_le_of_ne ((fixedPositiveCoefficientSource k).source.nonneg x) (Ne.symm hx))
  have hy : (x none : ℤ) ∈
      ((fixedPositiveCoefficientSource k).source.toPMF.map (fun y => (y none : ℤ))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨x, hx', rfl⟩
  rw [fixedPositiveCoefficientSource_law] at hy
  simpa using hy

theorem fixedPositiveCoefficientSource_positive (k : ℕ) (hk : 0 < k)
    (x : IntegerScalarCubeBox Empty (fixedPositiveCoefficientSource k).length)
    (hx : (fixedPositiveCoefficientSource k).source.weight x ≠ 0) :
    ((fixedPositiveCoefficientSource k).length : ℝ) / 4 ≤ (x none : ℝ) := by
  have he := fixedPositiveCoefficientSource_support k x hx
  have heR : (x none : ℝ) = (k : ℝ) := by exact_mod_cast he
  rw [heR, fixedPositiveCoefficientSource_length]
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  push_cast
  linarith

theorem fixedPositiveCoefficientSource_primitive (k : ℕ) (A : ℝ≥0) :
    ScalarCubePrimitiveBudget (fixedPositiveCoefficientSource k) A
      (scalarCubePrimitiveEnvelope Empty A 1 0 (k + 1)) :=
  scalarCubePrimitiveBudget_of_raw_bounds _ A 1 0 (k + 1) le_rfl le_rfl le_rfl

theorem fixedPositiveCoefficientSource_primitive_of_le {k K : ℕ} (hk : k ≤ K)
    (A : ℝ≥0) :
    ScalarCubePrimitiveBudget (fixedPositiveCoefficientSource k) A
      (scalarCubePrimitiveEnvelope Empty A 1 0 (K + 1)) :=
  scalarCubePrimitiveBudget_of_raw_bounds _ A 1 0 (K + 1)
    (Nat.add_le_add_right hk 1) le_rfl le_rfl

end Erdos3

end

end OAI
