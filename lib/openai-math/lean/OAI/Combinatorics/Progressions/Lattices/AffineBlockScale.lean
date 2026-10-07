/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Geometry.WeightedBlockSupportScale

namespace OAI

section

namespace Erdos3

def centeredFundamentalBox {J : Type*} (Q K : ℕ) (center z : J → ℤ) : Prop :=
  ∀ j, center j - (Q : ℤ) * K ≤ z j ∧ z j < center j + ((Q : ℤ) + 1) * K

theorem centeredFundamentalBox_of_support {J : Type*} {Q K : ℕ} (center y : J → ℤ)
    {H : ℝ} (hK : 0 < K) (hH : H ≤ Q)
    (hy : ∀ j, |(y j : ℝ) - center j| ≤ H * K) : centeredFundamentalBox Q K center y := by
  intro j
  have hbound : |y j - center j| ≤ (Q : ℤ) * K := by
    have hh := (hy j).trans (mul_le_mul_of_nonneg_right hH (Nat.cast_nonneg K))
    exact_mod_cast hh
  have hh := abs_le.mp hbound
  have hK' : (0 : ℤ) < K := by exact_mod_cast hK
  constructor <;> nlinarith only [hh.1, hh.2, hK']

theorem centeredFundamentalBox_iff {J : Type*} (Q K : ℕ) (center z : J → ℤ) :
    centeredFundamentalBox Q K center z ↔
      ∀ j, center j - (Q : ℤ) * K ≤ z j ∧
        z j < (center j - (Q : ℤ) * K) + (((2 * Q + 1) * K : ℕ) : ℤ) := by
  have he (j) : (center j - (Q : ℤ) * K) + (((2 * Q + 1) * K : ℕ) : ℤ) =
      center j + ((Q : ℤ) + 1) * K := by push_cast; ring
  simp only [centeredFundamentalBox, he]

theorem integerGridMass_eq_imageMass_on_centered_box {X J : Type*}
    [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (center z : J → ℤ)
    {Q K : ℕ} {H : ℝ} (hK : 0 < K) (hH : H ≤ Q)
    (hY : ∀ x, p.weight x ≠ 0 → ∀ j, |(Y x j : ℝ) - center j| ≤ H * K)
    (hz : centeredFundamentalBox Q K center z) :
    integerGridMass p Y ((2 * Q + 1) * K) z = finiteImageMass p Y z := by
  apply integerGridMass_eq_imageMass_on_box p Y _ (fun j => center j - (Q : ℤ) * K) z
  · intro x hx
    exact (centeredFundamentalBox_iff Q K center (Y x)).mp
      (centeredFundamentalBox_of_support center (Y x) hK hH (hY x hx))
  · exact (centeredFundamentalBox_iff Q K center z).mp hz

theorem integerGridDensity_eq_imageMass_on_centered_box {X J : Type*}
    [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (center z : J → ℤ)
    {Q K : ℕ} {H : ℝ} (hK : 0 < K) (hH : H ≤ Q)
    (hY : ∀ x, p.weight x ≠ 0 → ∀ j, |(Y x j : ℝ) - center j| ≤ H * K)
    (hz : centeredFundamentalBox Q K center z) :
    integerGridDensity p Y K ((2 * Q + 1) * K) z =
      (K : ℝ) ^ Fintype.card J * finiteImageMass p Y z := by
  unfold integerGridDensity
  rw [integerGridMass_eq_imageMass_on_centered_box p Y center z hK hH hY hz]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finiteImageMass_total {X Z : Type*} [Fintype X] [Fintype Z] [DecidableEq Z]
    (p : FiniteProbabilityWeights X) (Y : X → Z) : ∑ z, finiteImageMass p Y z = 1 := by
  unfold finiteImageMass FiniteProbabilityWeights.mean
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_one]
  exact p.total

theorem integerGridMass_total {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (M : ℕ) [NeZero M] (lower : J → ℤ) :
    (∑ r : J → ZMod M, integerGridMass p Y M (rectangularGridRepresentative M lower r)) = 1 := by
  simp only [integerGridMass_representative]
  exact finiteImageMass_total p _

theorem integerImageMass_total_on_box {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (M : ℕ) [NeZero M] (lower : J → ℤ)
    (hY : ∀ x, p.weight x ≠ 0 → ∀ j, lower j ≤ Y x j ∧ Y x j < lower j + M) :
    (∑ r : J → ZMod M, finiteImageMass p Y (rectangularGridRepresentative M lower r)) = 1 := by
  have h (r : J → ZMod M) := integerGridMass_eq_imageMass_on_box p Y M lower
    (rectangularGridRepresentative M lower r) hY
      (rectangularGridRepresentative_bounds (Nat.pos_of_ne_zero (NeZero.ne M)) lower r)
  simpa only [h] using integerGridMass_total p Y M lower

theorem integerGridDensity_total {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (K M : ℕ) [NeZero M] (lower : J → ℤ) :
    (∑ r : J → ZMod M, integerGridDensity p Y K M (rectangularGridRepresentative M lower r)) =
      (K : ℝ) ^ Fintype.card J := by
  simp only [integerGridDensity, ← Finset.mul_sum, integerGridMass_total, mul_one]

def centeredGridRepresentative {J : Type*} (Q K : ℕ) (center : J → ℤ)
    (r : J → ZMod ((2 * Q + 1) * K)) : J → ℤ :=
  rectangularGridRepresentative ((2 * Q + 1) * K) (fun j => center j - (Q : ℤ) * K) r

theorem centeredGridRepresentative_mem {J : Type*} (Q K : ℕ) (hK : 0 < K)
    (center : J → ℤ) (r : J → ZMod ((2 * Q + 1) * K)) :
    centeredFundamentalBox Q K center (centeredGridRepresentative Q K center r) := by
  apply (centeredFundamentalBox_iff Q K center _).mpr
  exact rectangularGridRepresentative_bounds (Nat.mul_pos (by omega) hK) _ r

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

noncomputable def affineWeightedCubeGridCoefficient {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : Fin (n + 1) → Option I → ℝ) (v : Fin (n + 1) → Option I → ℕ)
    (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) : ℂ :=
  (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean (fun z => character
    ((booleanBlockPhase (gridJetFrequency M J k)
      (fun j => affineCubeCoordinates (u j) (v j) (fun i => (z j i : ℝ))) : ℝ) : CircleFourier.Circle))

noncomputable def affineWeightedModerateGridCoefficient {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (shift : ℝ) (t : ℕ) (u : Fin n → Option I → ℝ) (v : Fin n → Option I → ℕ)
    (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) : ℂ :=
  c.source.complexMean (fun z => (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
    (fun x => character (((shift + (t : ℝ) * (z none : ℝ)) * booleanBlockPhase (gridJetFrequency M J k)
      (fun j => affineCubeCoordinates (u j) (v j) (fun i => (x j i : ℝ))) : ℝ) : CircleFourier.Circle)))

theorem affineWeightedCubeGridCoefficient_norm_le_one {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : Fin (n + 1) → Option I → ℝ) (v : Fin (n + 1) → Option I → ℕ)
    (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) :
    ‖affineWeightedCubeGridCoefficient s u v M J k‖ ≤ 1 := by
  let p := FiniteProbabilityWeights.pi (fun j => (s j).source)
  exact (p.norm_complexMean_le_mean_norm _).trans_eq (by simp only [norm_character, p.mean_const])

theorem affineWeightedModerateGridCoefficient_norm_le_one {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (shift : ℝ) (t : ℕ) (u : Fin n → Option I → ℝ) (v : Fin n → Option I → ℕ)
    (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) :
    ‖affineWeightedModerateGridCoefficient c s shift t u v M J k‖ ≤ 1 := by
  let p := FiniteProbabilityWeights.pi (fun j => (s j).source)
  apply (c.source.norm_complexMean_le_mean_norm _).trans
  apply (c.source.mean_mono (fun z => ?_)).trans_eq (c.source.mean_const 1)
  exact (p.norm_complexMean_le_mean_norm _).trans_eq (by simp only [norm_character, p.mean_const])

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem affineWeightedCubeGridCoefficient_mem_cover {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V ζ : ℝ}
    (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U) (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hlen : ∀ j, majorArcLengthConstant n U / ζ ^ majorArcLengthExponent n ≤ (s j).length)
    (u : Fin (n + 1) → Option I → ℝ) (v : Fin (n + 1) → Option I → ℕ)
    (hv : ∀ j i, 0 < v j i) (hstride : ∀ j i, ((v j i * (s j).modulus i : ℕ) : ℝ) ≤ U)
    {M : ℕ} (hM : 0 < M) (hscale : (M : ℝ) / ∏ j, ((s j).length : ℝ) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (k : J → Fin M) (hk : ζ ≤ ‖affineWeightedCubeGridCoefficient s u v M J k‖) :
    k ∈ polynomialGridCover J M (majorArcCoverConstant n J.card U V) (majorArcCoverExponent n J.card) ζ := by
  have hU := (h 0).one_le
  obtain ⟨D, hD, hDb, a, ha⟩ := polynomial_affine_weightedCubeBlock_major_arc s A hA h hζ hζ1
    (fun j => (localizedMajorArcLengthBudget_le_power n hU hζ hζ1).trans (hlen j))
    u v hv hstride (gridJetFrequency M J k) J hJ hk
  have hQ := (majorArc_denominator_le_cover n J.card hU hV hζ hζ1).trans (Nat.le_ceil _)
  have hH := (majorArc_scaled_error_le_cover n J.card hU hV hζ hζ1 hscale).trans (Nat.le_ceil _)
  apply mem_rationalGridMajorBox hM k hD (by exact_mod_cast hDb.trans hQ) a _ hH
  intro S
  simpa only [gridJetFrequency_apply] using ha S

theorem affineWeightedModerateGridCoefficient_mem_cover {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V ζ : ℝ}
    (hc : ScalarCubePrimitiveBudget c A U) (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U)
    (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hclen : majorArcLengthConstant n U / ζ ^ majorArcLengthExponent n ≤ c.length)
    (hlen : ∀ j, majorArcLengthConstant n U / ζ ^ majorArcLengthExponent n ≤ (s j).length)
    (shift : ℝ) (t : ℕ) (ht : 0 < t) (u : Fin n → Option I → ℝ) (v : Fin n → Option I → ℕ)
    (hv : ∀ j i, 0 < v j i) (hstride : ∀ j i, ((v j i * (s j).modulus i : ℕ) : ℝ) ≤ U)
    (hcoeff : ((t * c.modulus none : ℕ) : ℝ) ≤ U)
    {M : ℕ} (hM : 0 < M)
    (hscale : (M : ℝ) / ((((t * c.modulus none : ℕ) : ℝ) * c.length) * ∏ j, ((s j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n)
    (k : J → Fin M) (hk : ζ ≤ ‖affineWeightedModerateGridCoefficient c s shift t u v M J k‖) :
    k ∈ polynomialGridCover J M (majorArcCoverConstant n J.card U V) (majorArcCoverExponent n J.card) ζ := by
  have hU := hc.one_le
  have hU0 : 0 ≤ U := le_trans (by norm_num) hU
  obtain ⟨D, hD, hDb, a, ha⟩ := polynomial_affine_weightedModerateBlock_major_arc c s A hA hc h hζ hζ1
    ((localizedMajorArcLengthBudget_le_power n hU hζ hζ1).trans hclen)
    (fun j => (localizedMajorArcLengthBudget_le_power n hU hζ hζ1).trans (hlen j))
    shift t ht u v hv hstride (gridJetFrequency M J k) J hJ hk
  have hden : (localizedMajorArcBudget n U ζ * (((t * c.modulus none : ℕ) : ℝ) * U ^ n)) ^ J.card ≤
      (localizedMajorArcBudget n U ζ * U ^ (n + 1)) ^ J.card := by
    apply pow_le_pow_left₀ (by positivity [localizedMajorArcBudget_pos n hU hζ])
    apply mul_le_mul_of_nonneg_left _ (localizedMajorArcBudget_pos n hU hζ).le
    rw [pow_succ']
    exact mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hU0 n)
  have hQ := (hden.trans (majorArc_denominator_le_cover n J.card hU hV hζ hζ1)).trans (Nat.le_ceil _)
  have hH := (majorArc_scaled_error_le_cover n J.card hU hV hζ hζ1 hscale).trans (Nat.le_ceil _)
  apply mem_rationalGridMajorBox hM k hD (by exact_mod_cast hDb.trans hQ) a _ hH
  intro S
  simpa only [gridJetFrequency_apply] using ha S

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def affineWeightedCubeIntegerBlock {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Fin (n + 1) → NormalizedScalarCubeSource I) (u : Fin (n + 1) → Option I → ℤ)
    (v : Fin (n + 1) → Option I → ℕ) (J : Finset (Finset I))
    (x : ∀ j, IntegerScalarCubeBox I (s j).length) : J → ℤ :=
  fun S => integerBooleanBlockJet (fun j => affineIntegerCubeCoordinates (u j) (v j) (fun i => (x j i : ℤ))) S

theorem affineWeightedCubeGridCoefficient_eq_image {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Fin (n + 1) → NormalizedScalarCubeSource I) (u : Fin (n + 1) → Option I → ℤ)
    (v : Fin (n + 1) → Option I → ℕ) (M : ℕ) [NeZero M] (J : Finset (Finset I)) (k : J → Fin M) :
    integerGridCoefficient (FiniteProbabilityWeights.pi (fun j => (s j).source))
      (affineWeightedCubeIntegerBlock s u v J) M k =
        affineWeightedCubeGridCoefficient s (fun j i => (u j i : ℝ)) v M J k := by
  unfold integerGridCoefficient affineWeightedCubeGridCoefficient
  congr 1
  funext x
  rw [rectangularGridCharacter_eq]
  unfold affineWeightedCubeIntegerBlock
  rw [integerBooleanBlockJet_pairing]
  unfold affineIntegerCubeCoordinates affineCubeCoordinates
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]

noncomputable def affineWeightedCubeIntegerSum {B : Type*} [Fintype B] {n : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)
    (J : Finset (Finset I)) (shift : J → ℤ)
    (x : ∀ b j, IntegerScalarCubeBox I (s b j).length) : J → ℤ :=
  shift + ∑ b, affineWeightedCubeIntegerBlock (s b) (u b) (v b) J (x b)

theorem affineWeightedCubeIntegerSum_coefficient {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)
    (M : ℕ) [NeZero M] (J : Finset (Finset I)) (shift : J → ℤ) (k : J → Fin M) :
    integerGridCoefficient (weightedCubeIntegerSource s) (affineWeightedCubeIntegerSum s u v J shift) M k =
      rectangularGridCharacter M k shift *
        ∏ b, affineWeightedCubeGridCoefficient (s b) (fun j i => (u b j i : ℝ)) (v b) M J k := by
  have h := independent_integerGridCoefficient
    (fun b => FiniteProbabilityWeights.pi (fun j => (s b j).source))
    (fun b => affineWeightedCubeIntegerBlock (s b) (u b) (v b) J) shift M k
  unfold weightedCubeIntegerSource affineWeightedCubeIntegerSum
  simpa only [affineWeightedCubeGridCoefficient_eq_image] using h

noncomputable def affineWeightedModerateIntegerBlock {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (offset : ℤ) (stride : ℕ) (u : Fin n → Option I → ℤ) (v : Fin n → Option I → ℕ)
    (J : Finset (Finset I))
    (x : IntegerScalarCubeBox Empty c.length × (∀ j, IntegerScalarCubeBox I (s j).length)) : J → ℤ :=
  fun S => (offset + (stride : ℤ) * (x.1 none : ℤ)) *
    integerBooleanBlockJet (fun j => affineIntegerCubeCoordinates (u j) (v j) (fun i => (x.2 j i : ℤ))) S

theorem affineWeightedModerateGridCoefficient_eq_image {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (offset : ℤ) (stride : ℕ) (u : Fin n → Option I → ℤ) (v : Fin n → Option I → ℕ)
    (M : ℕ) [NeZero M] (J : Finset (Finset I)) (k : J → Fin M) :
    integerGridCoefficient (weightedModerateIntegerSource c s)
      (affineWeightedModerateIntegerBlock c s offset stride u v J) M k =
        affineWeightedModerateGridCoefficient c s (offset : ℝ) stride (fun j i => (u j i : ℝ)) v M J k := by
  unfold integerGridCoefficient weightedModerateIntegerSource
  rw [FiniteProbabilityWeights.complexMean_prod]
  change c.source.complexMean _ = c.source.complexMean _
  congr 1
  funext z
  congr 1
  funext x
  rw [rectangularGridCharacter_eq]
  unfold affineWeightedModerateIntegerBlock
  rw [integerBooleanBlockJet_scaled_pairing]
  unfold affineIntegerCubeCoordinates affineCubeCoordinates
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]

noncomputable def affineWeightedModerateIntegerSum {B : Type*} [Fintype B] {n : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin n → NormalizedScalarCubeSource I) (offset : B → ℤ) (stride : B → ℕ)
    (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    (J : Finset (Finset I)) (shift : J → ℤ)
    (x : ∀ b, IntegerScalarCubeBox Empty (c b).length × (∀ j, IntegerScalarCubeBox I (s b j).length)) : J → ℤ :=
  shift + ∑ b, affineWeightedModerateIntegerBlock (c b) (s b) (offset b) (stride b) (u b) (v b) J (x b)

theorem affineWeightedModerateIntegerSum_coefficient {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (offset : B → ℤ) (stride : B → ℕ) (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    (M : ℕ) [NeZero M] (J : Finset (Finset I)) (shift : J → ℤ) (k : J → Fin M) :
    integerGridCoefficient (weightedModerateIntegerProductSource c s)
      (affineWeightedModerateIntegerSum c s offset stride u v J shift) M k =
        rectangularGridCharacter M k shift * ∏ b, affineWeightedModerateGridCoefficient (c b) (s b)
          (offset b : ℝ) (stride b) (fun j i => (u b j i : ℝ)) (v b) M J k := by
  have h := independent_integerGridCoefficient (fun b => weightedModerateIntegerSource (c b) (s b))
    (fun b => affineWeightedModerateIntegerBlock (c b) (s b) (offset b) (stride b) (u b) (v b) J) shift M k
  unfold weightedModerateIntegerProductSource affineWeightedModerateIntegerSum
  simpa only [affineWeightedModerateGridCoefficient_eq_image] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def affineCubeCoordinateRadius {I : Type*} [Fintype I] (L : ℕ)
    (u : Option I → ℤ) (v : Option I → ℕ) : ℕ :=
  ∑ i, ((u i).natAbs + v i * L)

theorem affineIntegerCubeCoordinates_bound {I : Type*} [Fintype I] {L : ℕ}
    (u : Option I → ℤ) (v : Option I → ℕ) (x : IntegerScalarCubeBox I L) (i : Option I) :
    |affineIntegerCubeCoordinates u v (fun r => (x r : ℤ)) i| ≤
      (affineCubeCoordinateRadius L u v : ℤ) := by
  classical
  have hi : (u i).natAbs + v i * L ≤ affineCubeCoordinateRadius L u v :=
    Finset.single_le_sum (fun j _ => Nat.zero_le ((u j).natAbs + v j * L)) (Finset.mem_univ i)
  calc
    _ ≤ |u i| + (v i : ℤ) * L := by
      unfold affineIntegerCubeCoordinates
      apply (abs_add_le _ _).trans
      rw [abs_mul, abs_of_nonneg (show (0 : ℤ) ≤ (v i : ℤ) from Nat.cast_nonneg (v i))]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (integerScalarCubeBox_coordinate_abs x i) (Nat.cast_nonneg (v i)))
    _ ≤ _ := by
      have hic : ((u i).natAbs : ℤ) + (v i : ℤ) * L ≤ (affineCubeCoordinateRadius L u v : ℤ) := by
        exact_mod_cast hi
      simpa only [Int.natCast_natAbs] using hic

def affineWeightedCubeJetBound {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I] {n : ℕ}
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)
    (S : Finset I) : ℤ :=
  ∑ b, (2 : ℤ) ^ S.card * ∏ j, ((Fintype.card I + 1 : ℕ) : ℤ) *
    affineCubeCoordinateRadius (s b j).length (u b j) (v b j)

theorem affineWeightedCubeIntegerSum_bound {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)
    (J : Finset (Finset I)) (shift : J → ℤ)
    (x : ∀ b j, IntegerScalarCubeBox I (s b j).length) (S : J) :
    |affineWeightedCubeIntegerSum s u v J shift x S - shift S| ≤ affineWeightedCubeJetBound s u v S := by
  classical
  simp only [affineWeightedCubeIntegerSum, Pi.add_apply, Finset.sum_apply, add_sub_cancel_left]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro b _
  exact integerBooleanBlockJet_bound _
    (fun j => affineCubeCoordinateRadius (s b j).length (u b j) (v b j))
    (fun j i => affineIntegerCubeCoordinates_bound (u b j) (v b j) (x b j) i) S

def affineWeightedModerateJetBound {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I] {n : ℕ}
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (offset : B → ℤ) (stride : B → ℕ) (u : B → Fin n → Option I → ℤ)
    (v : B → Fin n → Option I → ℕ) (S : Finset I) : ℤ :=
  ∑ b, (|offset b| + (stride b : ℤ) * (c b).length) *
    ((2 : ℤ) ^ S.card * ∏ j, ((Fintype.card I + 1 : ℕ) : ℤ) *
      affineCubeCoordinateRadius (s b j).length (u b j) (v b j))

theorem affineWeightedModerateIntegerBlock_bound {I : Type*} [Fintype I] [DecidableEq I]
    {n : ℕ} (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (offset : ℤ) (stride : ℕ) (u : Fin n → Option I → ℤ) (v : Fin n → Option I → ℕ)
    (J : Finset (Finset I))
    (x : IntegerScalarCubeBox Empty c.length × (∀ j, IntegerScalarCubeBox I (s j).length)) (S : J) :
    |affineWeightedModerateIntegerBlock c s offset stride u v J x S| ≤
      (|offset| + (stride : ℤ) * c.length) * ((2 : ℤ) ^ S.val.card *
        ∏ j, ((Fintype.card I + 1 : ℕ) : ℤ) * affineCubeCoordinateRadius (s j).length (u j) (v j)) := by
  have hc : |offset + (stride : ℤ) * (x.1 none : ℤ)| ≤ |offset| + (stride : ℤ) * c.length := by
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_of_nonneg (show (0 : ℤ) ≤ (stride : ℤ) from Nat.cast_nonneg stride)]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (integerScalarCubeBox_coordinate_abs x.1 none) (Nat.cast_nonneg stride))
  have hj := integerBooleanBlockJet_bound _
    (fun j => affineCubeCoordinateRadius (s j).length (u j) (v j))
    (fun j i => affineIntegerCubeCoordinates_bound (u j) (v j) (x.2 j) i) S.val
  unfold affineWeightedModerateIntegerBlock
  rw [abs_mul]
  exact mul_le_mul hc hj (abs_nonneg _) (by positivity)

theorem affineWeightedModerateIntegerSum_bound {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (offset : B → ℤ) (stride : B → ℕ) (u : B → Fin n → Option I → ℤ)
    (v : B → Fin n → Option I → ℕ) (J : Finset (Finset I)) (shift : J → ℤ)
    (x : ∀ b, IntegerScalarCubeBox Empty (c b).length × (∀ j, IntegerScalarCubeBox I (s b j).length)) (S : J) :
    |affineWeightedModerateIntegerSum c s offset stride u v J shift x S - shift S| ≤
      affineWeightedModerateJetBound c s offset stride u v S := by
  classical
  simp only [affineWeightedModerateIntegerSum, Pi.add_apply, Finset.sum_apply, add_sub_cancel_left]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum (fun b _ =>
    affineWeightedModerateIntegerBlock_bound (c b) (s b) (offset b) (stride b) (u b) (v b) J (x b) S)

theorem affineWeightedCube_mass_on_fundamental_box {B I : Type*}
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I] {n K Q : ℕ}
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)
    (hK : 0 < K) (J : Finset (Finset I))
    (hQ : ∀ S : J, affineWeightedCubeJetBound s u v S ≤ (Q : ℤ) * K)
    (center z : J → ℤ) (hz : centeredFundamentalBox Q K center z) :
    integerGridMass (weightedCubeIntegerSource s) (affineWeightedCubeIntegerSum s u v J center)
      ((2 * Q + 1) * K) z =
        finiteImageMass (weightedCubeIntegerSource s) (affineWeightedCubeIntegerSum s u v J center) z := by
  apply integerGridMass_eq_imageMass_on_centered_box _ _ center z hK (H := (Q : ℝ)) le_rfl _ hz
  intro x _ S
  exact_mod_cast (affineWeightedCubeIntegerSum_bound s u v J center x S).trans (hQ S)

theorem affineWeightedModerate_mass_on_fundamental_box {B I : Type*}
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I] {n K Q : ℕ}
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (offset : B → ℤ) (stride : B → ℕ) (u : B → Fin n → Option I → ℤ)
    (v : B → Fin n → Option I → ℕ) (hK : 0 < K) (J : Finset (Finset I))
    (hQ : ∀ S : J, affineWeightedModerateJetBound c s offset stride u v S ≤ (Q : ℤ) * K)
    (center z : J → ℤ) (hz : centeredFundamentalBox Q K center z) :
    integerGridMass (weightedModerateIntegerProductSource c s)
      (affineWeightedModerateIntegerSum c s offset stride u v J center) ((2 * Q + 1) * K) z =
        finiteImageMass (weightedModerateIntegerProductSource c s)
          (affineWeightedModerateIntegerSum c s offset stride u v J center) z := by
  apply integerGridMass_eq_imageMass_on_centered_box _ _ center z hK (H := (Q : ℝ)) le_rfl _ hz
  intro x _ S
  exact_mod_cast (affineWeightedModerateIntegerSum_bound c s offset stride u v J center x S).trans (hQ S)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem affineCubeCoordinateRadius_le {I : Type*} [Fintype I]
    (L : ℕ) (u : Option I → ℤ) (v : Option I → ℕ) {C : ℝ}
    (h : ∀ i, |(u i : ℝ)| + (v i : ℝ) * L ≤ C * L) :
    (affineCubeCoordinateRadius L u v : ℝ) ≤ ((Fintype.card I + 1 : ℕ) : ℝ) * C * L := by
  classical
  simp only [affineCubeCoordinateRadius, Nat.cast_sum, Nat.cast_add, Nat.cast_mul,
    Nat.cast_natAbs, Int.cast_abs]
  calc
    _ ≤ ∑ _i : Option I, C * L := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_option, nsmul_eq_mul]
      push_cast
      ring

theorem affine_coordinate_relative_bound {L V : ℕ} {O : ℝ} (u : ℤ) (v : ℕ)
    (hu : |(u : ℝ)| ≤ O * L) (hv : v ≤ V) :
    |(u : ℝ)| + (v : ℝ) * L ≤ (O + V) * L := by
  have hv' : (v : ℝ) ≤ V := by exact_mod_cast hv
  have h := add_le_add hu (mul_le_mul_of_nonneg_right hv' (Nat.cast_nonneg L))
  simpa only [add_mul] using h

noncomputable def affineBlockScaleBound (q g b : ℕ) (C V : ℝ) : ℝ :=
  blockJetScaleBound q g b ((((q + 1 : ℕ) : ℝ) * C) ^ g * V)

theorem affineBlockScaleBound_nonneg (q g b : ℕ) {C V : ℝ} (hC : 0 ≤ C) (hV : 0 ≤ V) :
    0 ≤ affineBlockScaleBound q g b C V :=
  blockJetScaleBound_nonneg q g b (by positivity)

theorem affineCube_radius_product_le {G I : Type*} [Fintype G] [Fintype I]
    (L : G → ℕ) (u : G → Option I → ℤ) (v : G → Option I → ℕ) {C : ℝ}
    (h : ∀ j i, |(u j i : ℝ)| + (v j i : ℝ) * L j ≤ C * L j) :
    (∏ j, (affineCubeCoordinateRadius (L j) (u j) (v j) : ℝ)) ≤
      (((Fintype.card I + 1 : ℕ) : ℝ) * C) ^ Fintype.card G * ∏ j, (L j : ℝ) := by
  classical
  calc
    _ ≤ ∏ j, (((Fintype.card I + 1 : ℕ) : ℝ) * C) * L j := by
      exact Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        (fun j _ => affineCubeCoordinateRadius_le (L j) (u j) (v j) (h j))
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

theorem affineWeightedCubeJetBound_le_scale {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)
    {C V K : ℝ} (hC : 0 ≤ C)
    (hcoord : ∀ b j i, |(u b j i : ℝ)| + (v b j i : ℝ) * (s b j).length ≤ C * (s b j).length)
    (hvol : ∀ b, (∏ j, ((s b j).length : ℝ)) ≤ V * K)
    (S : Finset I) (hS : S.card ≤ n + 1) :
    (affineWeightedCubeJetBound s u v S : ℝ) ≤
      affineBlockScaleBound (Fintype.card I) (n + 1) (Fintype.card B) C V * K := by
  classical
  simp only [affineWeightedCubeJetBound, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    Int.cast_prod, Int.cast_natCast, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  calc
    _ ≤ ∑ _b : B, (2 : ℝ) ^ (n + 1) * ((Fintype.card I + 1 : ℕ) : ℝ) ^ (n + 1) *
        ((((Fintype.card I + 1 : ℕ) : ℝ) * C) ^ (n + 1) * (V * K)) := by
      apply Finset.sum_le_sum
      intro b _
      have hp := (affineCube_radius_product_le (fun j => (s b j).length) (u b) (v b) (hcoord b)).trans
        (mul_le_mul_of_nonneg_left (hvol b) (by positivity))
      simp only [Fintype.card_fin] at hp
      have htwo := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hS
      have htwo' := mul_le_mul_of_nonneg_right htwo
        (show 0 ≤ ((Fintype.card I + 1 : ℕ) : ℝ) ^ (n + 1) by positivity)
      simpa only [mul_assoc] using mul_le_mul htwo' hp (by positivity) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, affineBlockScaleBound, blockJetScaleBound]
      ring

theorem affineWeightedModerateJetBound_le_scale {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (offset : B → ℤ) (stride : B → ℕ) (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    {C V K : ℝ} (hC : 0 ≤ C)
    (hcoord : ∀ b j i, |(u b j i : ℝ)| + (v b j i : ℝ) * (s b j).length ≤ C * (s b j).length)
    (hvol : ∀ b, (|(offset b : ℝ)| + (stride b : ℝ) * (c b).length) *
      (∏ j, ((s b j).length : ℝ)) ≤ V * K)
    (S : Finset I) (hS : S.card ≤ n) :
    (affineWeightedModerateJetBound c s offset stride u v S : ℝ) ≤
      affineBlockScaleBound (Fintype.card I) n (Fintype.card B) C V * K := by
  classical
  simp only [affineWeightedModerateJetBound, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    Int.cast_prod, Int.cast_natCast, Int.cast_add, Int.cast_abs, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    _ = ∑ b : B, (2 : ℝ) ^ S.card * ((Fintype.card I + 1 : ℕ) : ℝ) ^ n *
        ((|(offset b : ℝ)| + (stride b : ℝ) * (c b).length) *
          ∏ j, (affineCubeCoordinateRadius (s b j).length (u b j) (v b j) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ ≤ ∑ _b : B, (2 : ℝ) ^ n * ((Fintype.card I + 1 : ℕ) : ℝ) ^ n *
        ((((Fintype.card I + 1 : ℕ) : ℝ) * C) ^ n * (V * K)) := by
      apply Finset.sum_le_sum
      intro b _
      have hrad := affineCube_radius_product_le (fun j => (s b j).length) (u b) (v b) (hcoord b)
      simp only [Fintype.card_fin] at hrad
      have hp : (|(offset b : ℝ)| + (stride b : ℝ) * (c b).length) *
          (∏ j, (affineCubeCoordinateRadius (s b j).length (u b j) (v b j) : ℝ)) ≤
            (((Fintype.card I + 1 : ℕ) : ℝ) * C) ^ n * (V * K) := by
        calc
          _ ≤ (|(offset b : ℝ)| + (stride b : ℝ) * (c b).length) *
              ((((Fintype.card I + 1 : ℕ) : ℝ) * C) ^ n * ∏ j, ((s b j).length : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hrad (by positivity)
          _ = (((Fintype.card I + 1 : ℕ) : ℝ) * C) ^ n *
              ((|(offset b : ℝ)| + (stride b : ℝ) * (c b).length) * ∏ j, ((s b j).length : ℝ)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hvol b) (by positivity)
      have htwo := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hS
      have htwo' := mul_le_mul_of_nonneg_right htwo
        (show 0 ≤ ((Fintype.card I + 1 : ℕ) : ℝ) ^ n by positivity)
      exact mul_le_mul htwo' hp (by positivity) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, affineBlockScaleBound, blockJetScaleBound]
      ring

end Erdos3

end

end OAI
