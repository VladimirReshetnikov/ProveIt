import OAI.Combinatorics.Progressions.Lattices.CubeResidueSupport

namespace OAI


namespace Erdos3

open scoped Matrix

theorem integerMatrix_scaled_period {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℤ) (m a : ℤ)
    (hperiod : integerScalarLattice I a ≤ A.mulVecLin.range) :
    integerScalarLattice I (m * a) ≤ (m • A).mulVecLin.range := by
  rintro y ⟨z, rfl⟩
  change (m * a) • z ∈ (m • A).mulVecLin.range
  obtain ⟨u, hu⟩ := hperiod ((integerScalarLattice_mem a _).mpr ⟨z, rfl⟩)
  refine ⟨u, ?_⟩
  change (m • A) *ᵥ u = (m * a) • z
  change A *ᵥ u = a • z at hu
  rw [Matrix.smul_mulVec, hu, smul_smul]

theorem integerCokernelExponent_scaled_le {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℤ) (m : ℕ) (hm : 0 < m)
    (hA : 0 < integerCokernelExponent A.mulVecLin.range) :
    integerCokernelExponent ((m : ℤ) • A).mulVecLin.range ≤
      m * integerCokernelExponent A.mulVecLin.range := by
  have hp := integerMatrix_scaled_period A (m : ℤ) (integerCokernelExponent A.mulVecLin.range : ℤ)
    (integerCokernelExponent_period A.mulVecLin.range)
  have hp' : integerScalarLattice I ((m * integerCokernelExponent A.mulVecLin.range : ℕ) : ℤ) ≤
      ((m : ℤ) • A).mulVecLin.range := by simpa only [Nat.cast_mul] using hp
  exact Nat.le_of_dvd (Nat.mul_pos hm hA)
    (integerCokernelExponent_dvd_period _ _ hp')

theorem scaled_nonzeroMinor {I J : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I J ℤ) (m : ℤ) (s : I → J)
    (h : (((m • A).submatrix id s).det) ≠ 0) :
    (A.submatrix id s).det ≠ 0 := by
  intro hz
  apply h
  change (m • A.submatrix id s).det = 0
  rw [Matrix.det_smul, hz, mul_zero]

theorem scaled_largeCokernel_implies {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I J ℤ) (m B : ℕ) (hm : 0 < m)
    (hminor : ∃ s : I → J, (((m : ℤ) • A).submatrix id s).det ≠ 0)
    (hB : m * B < integerCokernelExponent ((m : ℤ) • A).mulVecLin.range) :
    (∃ s : I → J, (A.submatrix id s).det ≠ 0) ∧
      B < integerCokernelExponent A.mulVecLin.range := by
  obtain ⟨s, hs⟩ := hminor
  have hs' := scaled_nonzeroMinor A (m : ℤ) s hs
  have hpos := (integerCokernelExponent_le_det A.mulVecLin.range (A.submatrix id s) hs'
    (integerColumnMinor_range_le A s)).1
  have hle := integerCokernelExponent_scaled_le A m hm hpos
  exact ⟨⟨s, hs'⟩, (Nat.mul_lt_mul_left hm).mp (hB.trans_le hle)⟩

end Erdos3


namespace Erdos3

def HasBoundedScalarPeriod {I : Type*} [Fintype I] (L : Submodule ℤ (I → ℤ)) (B : ℕ) : Prop :=
  ∃ a : ℕ, 0 < a ∧ a ≤ B ∧ integerScalarLattice I (a : ℤ) ≤ L

theorem hasBoundedScalarPeriod_iff {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (hL : 0 < integerCokernelExponent L) (B : ℕ) :
    HasBoundedScalarPeriod L B ↔ integerCokernelExponent L ≤ B := by
  constructor
  · rintro ⟨a, ha, haB, hperiod⟩
    exact (Nat.le_of_dvd ha (integerCokernelExponent_dvd_period L a hperiod)).trans haB
  · intro hB
    exact ⟨integerCokernelExponent L, hL, hB, integerCokernelExponent_period L⟩

theorem scalarCube_no_bounded_period_iff {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] {L : ℕ}
    (B : ℕ) (x : J → IntegerScalarCubeBox I L) :
    ((∃ s : I → J, ((scalarCubeDifferenceMatrix x).submatrix id s).det ≠ 0) ∧
      ¬ HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range B) ↔
        scalarCubeLargeCokernelEvent B x := by
  have hpos (h : ∃ s : I → J, ((scalarCubeDifferenceMatrix x).submatrix id s).det ≠ 0) :
      0 < integerCokernelExponent (scalarCubeDifferenceMatrix x).mulVecLin.range := by
    obtain ⟨s, hs⟩ := h
    exact (integerCokernelExponent_le_det _ _ hs (integerColumnMinor_range_le _ s)).1
  constructor
  · rintro ⟨hminor, hperiod⟩
    exact ⟨hminor, Nat.lt_of_not_ge (hperiod ∘ (hasBoundedScalarPeriod_iff _ (hpos hminor) B).mpr)⟩
  · rintro ⟨hminor, hB⟩
    exact ⟨hminor, fun hp => (Nat.not_le_of_lt hB) ((hasBoundedScalarPeriod_iff _ (hpos hminor) B).mp hp)⟩


def stridedScalarCubeLargeCokernelEvent {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] {L : ℕ}
    (m B : ℕ) (x : J → IntegerScalarCubeBox I L) : Prop :=
  (∃ s : I → J, (((m : ℤ) • scalarCubeDifferenceMatrix x).submatrix id s).det ≠ 0) ∧
    B < integerCokernelExponent ((m : ℤ) • scalarCubeDifferenceMatrix x).mulVecLin.range

theorem stridedScalarCube_largeCokernel_probability_le {I J : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    (L m B : ℕ) (hL : 0 < L) (hsize : Fintype.card I + 1 ≤ L) (hm : 0 < m) (hB : 0 < B)
    (hJ : Fintype.card J = Fintype.card I * (Fintype.card I + 2)) :
    (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability
        (stridedScalarCubeLargeCokernelEvent m (m * B)) ≤
      (integerScalarCubeDensityCap I * (1 + ((Fintype.card I).factorial : ℝ))) ^
        Fintype.card J / (B : ℝ) := by
  apply (FiniteProbabilityWeights.eventProbability_mono _ _ (scalarCubeLargeCokernelEvent B) ?_).trans
    (scalarCube_largeCokernel_probability_le L B hL hsize hB hJ)
  intro x hx
  exact scaled_largeCokernel_implies (scalarCubeDifferenceMatrix x) m B hm hx.1 hx.2


theorem exists_scalarCube_cokernel_cutoff (I J : Type*)
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    (hJ : Fintype.card J = Fintype.card I * (Fintype.card I + 2))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℕ, 0 < B ∧ ∀ (L m : ℕ) (hL : 0 < L), Fintype.card I + 1 ≤ L → 0 < m →
      (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability
        (stridedScalarCubeLargeCokernelEvent m (m * B)) ≤ ε := by
  let C := (integerScalarCubeDensityCap I * (1 + ((Fintype.card I).factorial : ℝ))) ^ Fintype.card J
  obtain ⟨B, hB⟩ := exists_nat_gt (max 1 (C / ε))
  have hBpos : 0 < B := by
    have h : (1 : ℝ) < B := (le_max_left _ _).trans_lt hB
    exact_mod_cast (zero_lt_one.trans h)
  have hbound : C / (B : ℝ) ≤ ε := by
    apply (div_le_iff₀ (by exact_mod_cast hBpos)).mpr
    have h := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hB)
    linarith
  refine ⟨B, hBpos, fun L m hL hsize hm => ?_⟩
  exact (stridedScalarCube_largeCokernel_probability_le L m B hL hsize hm hBpos hJ).trans hbound

end Erdos3

end OAI
