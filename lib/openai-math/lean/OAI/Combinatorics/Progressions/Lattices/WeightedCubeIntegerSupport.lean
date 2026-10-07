/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Fourier.UniformSpectrumAbsoluteCap

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerGridMass {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (M : ℕ) (z : J → ℤ) : ℝ :=
  finiteImageMass p (fun x => integerGridResidue M (Y x)) (integerGridResidue M z)

noncomputable def integerGridCoefficient {X J : Type*} [Fintype X] [Fintype J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (M : ℕ) [NeZero M] (k : J → Fin M) : ℂ :=
  p.complexMean (fun x => rectangularGridCharacter M k (Y x))

theorem integerGridMass_nonneg {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (M : ℕ) (z : J → ℤ) :
    0 ≤ integerGridMass p Y M z :=
  p.mean_nonneg (fun _ => by split_ifs <;> norm_num)

theorem integerGridFourier_inversion {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (M : ℕ) [NeZero M] (z : J → ℤ) :
    (∑ k : J → Fin M, integerGridCoefficient p Y M k * star (rectangularGridCharacter M k z)) =
      (M : ℂ) ^ Fintype.card J * integerGridMass p Y M z := by
  classical
  calc
    _ = ∑ x, (p.weight x : ℂ) *
        (∑ k : J → Fin M, rectangularGridCharacter M k (Y x) * star (rectangularGridCharacter M k z)) := by
      simp only [integerGridCoefficient, FiniteProbabilityWeights.complexMean, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      simp only [rectangularGridCharacter_orthogonality, integerGridMass, finiteImageMass,
        FiniteProbabilityWeights.mean, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : integerGridResidue M (Y x) = integerGridResidue M z <;> simp [hx, mul_comm]

theorem independent_integerGridCoefficient {B J : Type*} [Fintype B] [DecidableEq B] [Fintype J]
    {X : B → Type*} [∀ b, Fintype (X b)] (p : ∀ b, FiniteProbabilityWeights (X b))
    (Y : ∀ b, X b → J → ℤ) (shift : J → ℤ) (M : ℕ) [NeZero M] (k : J → Fin M) :
    integerGridCoefficient (FiniteProbabilityWeights.pi p) (fun x => shift + ∑ b, Y b (x b)) M k =
      rectangularGridCharacter M k shift * ∏ b, integerGridCoefficient (p b) (Y b) M k := by
  simp only [integerGridCoefficient, rectangularGridCharacter_add, rectangularGridCharacter_fintype_sum]
  rw [FiniteProbabilityWeights.complexMean_mul_left]
  congr 1
  exact FiniteProbabilityWeights.complexMean_pi_product p
    (fun b x => rectangularGridCharacter M k (Y b x))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerGridDensity {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (K M : ℕ) (z : J → ℤ) : ℝ :=
  (K : ℝ) ^ Fintype.card J * integerGridMass p Y M z

theorem integerGridDensity_nonneg {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (K M : ℕ) (z : J → ℤ) :
    0 ≤ integerGridDensity p Y K M z :=
  mul_nonneg (by positivity) (integerGridMass_nonneg p Y M z)

theorem integerGridDensity_fourier {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (K M : ℕ) [NeZero M] (z : J → ℤ) :
    (integerGridDensity p Y K M z : ℂ) =
      ((K : ℂ) / M) ^ Fintype.card J *
        ∑ k : J → Fin M, integerGridCoefficient p Y M k * star (rectangularGridCharacter M k z) := by
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  rw [integerGridFourier_inversion, div_pow]
  simp only [integerGridDensity, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast]
  field_simp

theorem integerGridDensity_truncation {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (K M : ℕ) [NeZero M]
    (S : Finset (J → Fin M)) (z : J → ℤ) :
    ‖(integerGridDensity p Y K M z : ℂ) - ((K : ℂ) / M) ^ Fintype.card J *
        ∑ k ∈ S, integerGridCoefficient p Y M k * star (rectangularGridCharacter M k z)‖ ≤
      ((K : ℝ) / M) ^ Fintype.card J * spectrumTail S (fun k => ‖integerGridCoefficient p Y M k‖) := by
  rw [integerGridDensity_fourier, ← mul_sub, norm_mul, norm_pow, norm_div,
    Complex.norm_natCast, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact finite_series_truncation_le S _ _
    (fun k => by rw [norm_star, rectangularGridCharacter_norm])

theorem integerGridDensity_absolute_cap {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (K M : ℕ) [NeZero M] (z : J → ℤ) :
    integerGridDensity p Y K M z ≤ ((K : ℝ) / M) ^ Fintype.card J *
      ∑ k : J → Fin M, ‖integerGridCoefficient p Y M k‖ := by
  have h := congrArg norm (integerGridDensity_fourier p Y K M z)
  rw [Complex.norm_real, Real.norm_of_nonneg (integerGridDensity_nonneg p Y K M z),
    norm_mul, norm_pow, norm_div, Complex.norm_natCast, Complex.norm_natCast] at h
  rw [h]
  exact mul_le_mul_of_nonneg_left
    (finite_series_norm_le _ _ (fun k => by rw [norm_star, rectangularGridCharacter_norm])) (by positivity)

theorem gridVolume_torus_factor {R K : ℕ} [NeZero R] [NeZero K] (j : ℕ) :
    ((K : ℝ) / (R * K)) ^ j = ((R : ℝ) ^ j)⁻¹ := by
  have hK : (K : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne K
  have he : (K : ℝ) / (R * K) = 1 / R := by field_simp
  rw [he, one_div_pow, one_div]

end Erdos3

end

section

namespace Erdos3

theorem integerGridResidue_eq_iff_of_close {J : Type*} (M : ℕ) (y z : J → ℤ)
    (hclose : ∀ j, |y j - z j| < (M : ℤ)) :
    integerGridResidue M y = integerGridResidue M z ↔ y = z := by
  constructor
  · intro h
    funext j
    have hd : (M : ℤ) ∣ y j - z j := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      rw [Int.cast_sub, show (y j : ZMod M) = (z j : ZMod M) from congrFun h j, sub_self]
    have ha : (y j - z j).natAbs < (M : ℤ).natAbs := by
      have hj := hclose j
      rw [Int.abs_eq_natAbs] at hj
      exact_mod_cast hj
    exact sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd ha)
  · rintro rfl
    rfl

theorem integerGridMass_eq_imageMass {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (M : ℕ) (z : J → ℤ)
    (hclose : ∀ x, p.weight x ≠ 0 → ∀ j, |Y x j - z j| < (M : ℤ)) :
    integerGridMass p Y M z = finiteImageMass p Y z := by
  classical
  unfold integerGridMass finiteImageMass FiniteProbabilityWeights.mean
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : p.weight x = 0
  · simp only [hx, zero_mul]
  · simp only [integerGridResidue_eq_iff_of_close M (Y x) z (hclose x hx)]

theorem integerGridMass_eq_imageMass_on_box {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (M : ℕ) (lower z : J → ℤ)
    (hY : ∀ x, p.weight x ≠ 0 → ∀ j, lower j ≤ Y x j ∧ Y x j < lower j + M)
    (hz : ∀ j, lower j ≤ z j ∧ z j < lower j + M) :
    integerGridMass p Y M z = finiteImageMass p Y z := by
  apply integerGridMass_eq_imageMass
  intro x hx j
  have hy := hY x hx j
  have hz' := hz j
  rw [abs_lt]
  constructor <;> omega

theorem integerGridDensity_eq_imageMass_on_box {X J : Type*}
    [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (K M : ℕ) (lower z : J → ℤ)
    (hY : ∀ x, p.weight x ≠ 0 → ∀ j, lower j ≤ Y x j ∧ Y x j < lower j + M)
    (hz : ∀ j, lower j ≤ z j ∧ z j < lower j + M) :
    integerGridDensity p Y K M z = (K : ℝ) ^ Fintype.card J * finiteImageMass p Y z := by
  unfold integerGridDensity
  rw [integerGridMass_eq_imageMass_on_box p Y M lower z hY hz]

end Erdos3

end

section

namespace Erdos3

def intervalGridRepresentative (M : ℕ) (lower : ℤ) (r : ZMod M) : ℤ :=
  lower + ((r.val : ℤ) - lower) % M

theorem intervalGridRepresentative_bounds {M : ℕ} (hM : 0 < M) (lower : ℤ) (r : ZMod M) :
    lower ≤ intervalGridRepresentative M lower r ∧ intervalGridRepresentative M lower r < lower + M := by
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  have hlo := Int.emod_nonneg ((r.val : ℤ) - lower) hM'.ne'
  have hhi := Int.emod_lt_of_pos ((r.val : ℤ) - lower) hM'
  unfold intervalGridRepresentative
  omega

theorem intervalGridRepresentative_residue (M : ℕ) [NeZero M] (lower : ℤ) (r : ZMod M) :
    (intervalGridRepresentative M lower r : ZMod M) = r := by
  simp only [intervalGridRepresentative, Int.cast_add, ZMod.intCast_mod, Int.cast_sub,
    Int.cast_natCast, ZMod.natCast_zmod_val, add_sub_cancel]

def rectangularGridRepresentative {J : Type*} (M : ℕ) (lower : J → ℤ) (r : J → ZMod M) : J → ℤ :=
  fun j => intervalGridRepresentative M (lower j) (r j)

theorem rectangularGridRepresentative_bounds {J : Type*} {M : ℕ} (hM : 0 < M)
    (lower : J → ℤ) (r : J → ZMod M) :
    ∀ j, lower j ≤ rectangularGridRepresentative M lower r j ∧
      rectangularGridRepresentative M lower r j < lower j + M :=
  fun j => intervalGridRepresentative_bounds hM (lower j) (r j)

theorem rectangularGridRepresentative_residue {J : Type*} (M : ℕ) [NeZero M]
    (lower : J → ℤ) (r : J → ZMod M) :
    integerGridResidue M (rectangularGridRepresentative M lower r) = r := by
  funext j
  exact intervalGridRepresentative_residue M (lower j) (r j)

theorem rectangularGridRepresentative_eq {J : Type*} {M : ℕ} [NeZero M]
    (lower z : J → ℤ) (hz : ∀ j, lower j ≤ z j ∧ z j < lower j + M) :
    rectangularGridRepresentative M lower (integerGridResidue M z) = z := by
  have hb := rectangularGridRepresentative_bounds (Nat.pos_of_ne_zero (NeZero.ne M)) lower
    (integerGridResidue M z)
  apply (integerGridResidue_eq_iff_of_close M _ z (fun j => ?_)).mp
    (rectangularGridRepresentative_residue M lower _)
  have h1 := hb j
  have h2 := hz j
  rw [abs_lt]
  constructor <;> omega

theorem integerGridMass_representative {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (M : ℕ) [NeZero M]
    (lower : J → ℤ) (r : J → ZMod M) :
    integerGridMass p Y M (rectangularGridRepresentative M lower r) =
      finiteImageMass p (integerGridResidue M ∘ Y) r := by
  simp only [integerGridMass, rectangularGridRepresentative_residue, Function.comp_def]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def integerBooleanBlockValue {G I : Type*} [Fintype G] [Fintype I] [DecidableEq I]
    (x : G → Option I → ℤ) (t : Finset I) : ℤ :=
  ∏ g, ∑ r, (booleanFeature r t : ℤ) * x g r

noncomputable def integerBooleanBlockJet {G I : Type*} [Fintype G] [Fintype I] [DecidableEq I]
    (x : G → Option I → ℤ) (S : Finset I) : ℤ :=
  booleanCoefficient (integerBooleanBlockValue x) S

theorem integerBooleanBlockValue_cast {G I : Type*} [Fintype G] [Fintype I] [DecidableEq I]
    (x : G → Option I → ℤ) (t : Finset I) :
    (integerBooleanBlockValue x t : ℝ) = booleanBlockValue (fun g r => (x g r : ℝ)) t := by
  have hf (r : Option I) : ((booleanFeature r t : ℤ) : ℝ) = (booleanFeature r t : ℝ) := by
    cases r with
    | none => simp only [booleanFeature, Int.cast_one]
    | some i =>
        by_cases hi : i ∈ t <;> simp only [booleanFeature, hi, ite_true, ite_false, Int.cast_one, Int.cast_zero]
  simp only [integerBooleanBlockValue, booleanBlockValue, Int.cast_prod, Int.cast_sum, Int.cast_mul, hf]

theorem integerBooleanBlockJet_cast {G I : Type*} [Fintype G] [Fintype I] [DecidableEq I]
    (x : G → Option I → ℤ) (S : Finset I) :
    (integerBooleanBlockJet x S : ℝ) =
      booleanCoefficient (booleanBlockValue (fun g r => (x g r : ℝ))) S := by
  have h := booleanCoefficient_map (Int.castRingHom ℝ) (integerBooleanBlockValue x) S
  change (integerBooleanBlockJet x S : ℝ) =
    booleanCoefficient (fun t => (integerBooleanBlockValue x t : ℝ)) S at h
  simpa only [integerBooleanBlockValue_cast] using h

theorem gridJetFrequency_pairing {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) (v : Finset I → ℝ) :
    (∑ S, gridJetFrequency M J k S * v S) = ∑ S : J, (((k S).val : ℝ) / M) * v S := by
  classical
  calc
    _ = ∑ S ∈ J, gridJetFrequency M J k S * v S := by
      symm
      apply Finset.sum_subset (Finset.subset_univ J)
      intro S _ hS
      simp only [gridJetFrequency, dite_eq_right hS, zero_mul]
    _ = ∑ S : J, gridJetFrequency M J k S * v S := (Finset.sum_coe_sort J _).symm
    _ = _ := Finset.sum_congr rfl (fun S _ => by rw [gridJetFrequency_apply])

theorem integerBooleanBlockJet_pairing {G I : Type*} [Fintype G] [Fintype I] [DecidableEq I]
    (x : G → Option I → ℤ) (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) :
    (∑ S : J, (((k S).val : ℝ) / M) * (integerBooleanBlockJet x S : ℝ)) =
      booleanBlockPhase (gridJetFrequency M J k) (fun g r => (x g r : ℝ)) := by
  simp only [integerBooleanBlockJet_cast, booleanBlockPhase, gridJetFrequency_pairing]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerBooleanBlockValue_bound {G I : Type*} [Fintype G] [Fintype I] [DecidableEq I]
    (x : G → Option I → ℤ) (L : G → ℕ) (hx : ∀ g r, |x g r| ≤ (L g : ℤ)) (t : Finset I) :
    |integerBooleanBlockValue x t| ≤ ∏ g, ((Fintype.card I + 1 : ℕ) : ℤ) * L g := by
  classical
  unfold integerBooleanBlockValue
  rw [Finset.abs_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
  intro g _
  calc
    _ ≤ ∑ r : Option I, |(booleanFeature r t : ℤ) * x g r| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : Option I, (L g : ℤ) := by
      apply Finset.sum_le_sum
      intro r _
      cases r with
      | none => simpa only [booleanFeature, one_mul] using hx g none
      | some i =>
          by_cases hi : i ∈ t
          · simpa only [booleanFeature, hi, ite_true, one_mul] using hx g (some i)
          · simp only [booleanFeature, hi, ite_false, zero_mul, abs_zero]
            exact Nat.cast_nonneg _
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_option, nsmul_eq_mul]

theorem integerBooleanBlockJet_bound {G I : Type*} [Fintype G] [Fintype I] [DecidableEq I]
    (x : G → Option I → ℤ) (L : G → ℕ) (hx : ∀ g r, |x g r| ≤ (L g : ℤ)) (S : Finset I) :
    |integerBooleanBlockJet x S| ≤ (2 : ℤ) ^ S.card *
      ∏ g, ((Fintype.card I + 1 : ℕ) : ℤ) * L g := by
  classical
  unfold integerBooleanBlockJet booleanCoefficient
  calc
    _ ≤ ∑ t ∈ S.powerset, |(-1 : ℤ) ^ (S \ t).card * integerBooleanBlockValue x t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ S.powerset, ∏ g, ((Fintype.card I + 1 : ℕ) : ℤ) * L g := by
      apply Finset.sum_le_sum
      intro t _
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
        integerBooleanBlockValue_bound x L hx t
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem integerScalarCubeBox_coordinate_abs {I : Type*} {L : ℕ}
    (x : IntegerScalarCubeBox I L) (r : Option I) : |(x r : ℤ)| ≤ L := by
  have h := Finset.mem_Ico.mp (x r).property
  rw [abs_le]
  constructor <;> omega

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def weightedCubeIntegerSource {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I) :
    FiniteProbabilityWeights (∀ b j, IntegerScalarCubeBox I (s b j).length) :=
  FiniteProbabilityWeights.pi (fun b => FiniteProbabilityWeights.pi (fun j => (s b j).source))

noncomputable def weightedCubeIntegerJetSum {B : Type*} [Fintype B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I) (J : Finset (Finset I)) (shift : J → ℤ)
    (x : ∀ b j, IntegerScalarCubeBox I (s b j).length) : J → ℤ :=
  shift + ∑ b, fun S : J => integerBooleanBlockJet (fun j r => (x b j r : ℤ)) S

theorem weightedCubeGridCoefficient_eq_image {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (M : ℕ) [NeZero M] (J : Finset (Finset I)) (k : J → Fin M) :
    integerGridCoefficient (FiniteProbabilityWeights.pi (fun j => (s j).source))
      (fun x (S : J) => integerBooleanBlockJet (fun j r => (x j r : ℤ)) S) M k =
        weightedCubeGridCoefficient s M J k := by
  unfold integerGridCoefficient weightedCubeGridCoefficient
  congr 1
  funext x
  rw [rectangularGridCharacter_eq, integerBooleanBlockJet_pairing]

theorem weightedCubeIntegerJetSum_coefficient {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (M : ℕ) [NeZero M] (J : Finset (Finset I)) (shift : J → ℤ) (k : J → Fin M) :
    integerGridCoefficient (weightedCubeIntegerSource s) (weightedCubeIntegerJetSum s J shift) M k =
      rectangularGridCharacter M k shift * ∏ b, weightedCubeGridCoefficient (s b) M J k := by
  have h := independent_integerGridCoefficient
    (fun b => FiniteProbabilityWeights.pi (fun j => (s b j).source))
    (fun b x (S : J) => integerBooleanBlockJet (fun j r => (x j r : ℤ)) S) shift M k
  unfold weightedCubeIntegerSource weightedCubeIntegerJetSum
  simpa only [weightedCubeGridCoefficient_eq_image] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

noncomputable def weightedModerateIntegerSource {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I) :
    FiniteProbabilityWeights (IntegerScalarCubeBox Empty c.length ×
      (∀ j, IntegerScalarCubeBox I (s j).length)) :=
  c.source.prod (FiniteProbabilityWeights.pi (fun j => (s j).source))

noncomputable def weightedModerateIntegerBlock {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (J : Finset (Finset I)) (offset : ℤ)
    (x : IntegerScalarCubeBox Empty c.length × (∀ j, IntegerScalarCubeBox I (s j).length)) : J → ℤ :=
  fun S => (offset + (x.1 none : ℤ)) * integerBooleanBlockJet (fun j r => (x.2 j r : ℤ)) S

theorem integerBooleanBlockJet_scaled_pairing {G I : Type*} [Fintype G] [Fintype I] [DecidableEq I]
    (x : G → Option I → ℤ) (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) (c : ℤ) :
    (∑ S : J, (((k S).val : ℝ) / M) * ((c * integerBooleanBlockJet x S : ℤ) : ℝ)) =
      (c : ℝ) * booleanBlockPhase (gridJetFrequency M J k) (fun j r => (x j r : ℝ)) := by
  rw [← integerBooleanBlockJet_pairing x M J k, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [Int.cast_mul]
  ring

theorem weightedModerateGridCoefficient_eq_image {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (M : ℕ) [NeZero M] (J : Finset (Finset I)) (offset : ℤ) (k : J → Fin M) :
    integerGridCoefficient (weightedModerateIntegerSource c s) (weightedModerateIntegerBlock c s J offset) M k =
      weightedModerateGridCoefficient c s (offset : ℝ) M J k := by
  unfold integerGridCoefficient weightedModerateIntegerSource
  rw [FiniteProbabilityWeights.complexMean_prod]
  change c.source.complexMean _ = c.source.complexMean _
  congr 1
  funext z
  congr 1
  funext x
  rw [rectangularGridCharacter_eq]
  simp only [weightedModerateIntegerBlock, integerBooleanBlockJet_scaled_pairing, Int.cast_add]

noncomputable def weightedModerateIntegerProductSource {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I) :
    FiniteProbabilityWeights (∀ b, IntegerScalarCubeBox Empty (c b).length ×
      (∀ j, IntegerScalarCubeBox I (s b j).length)) :=
  FiniteProbabilityWeights.pi (fun b => weightedModerateIntegerSource (c b) (s b))

noncomputable def weightedModerateIntegerJetSum {B : Type*} [Fintype B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (J : Finset (Finset I)) (offset : B → ℤ) (shift : J → ℤ)
    (x : ∀ b, IntegerScalarCubeBox Empty (c b).length × (∀ j, IntegerScalarCubeBox I (s b j).length)) : J → ℤ :=
  shift + ∑ b, weightedModerateIntegerBlock (c b) (s b) J (offset b) (x b)

theorem weightedModerateIntegerJetSum_coefficient {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (M : ℕ) [NeZero M] (J : Finset (Finset I)) (offset : B → ℤ) (shift : J → ℤ) (k : J → Fin M) :
    integerGridCoefficient (weightedModerateIntegerProductSource c s)
      (weightedModerateIntegerJetSum c s J offset shift) M k =
        rectangularGridCharacter M k shift * ∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b : ℝ) M J k := by
  have h := independent_integerGridCoefficient (fun b => weightedModerateIntegerSource (c b) (s b))
    (fun b => weightedModerateIntegerBlock (c b) (s b) J (offset b)) shift M k
  unfold weightedModerateIntegerProductSource weightedModerateIntegerJetSum
  simpa only [weightedModerateGridCoefficient_eq_image] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def weightedCubeJetBound {B : Type*} [Fintype B] {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I) (S : Finset I) : ℤ :=
  ∑ b, (2 : ℤ) ^ S.card * ∏ j, ((Fintype.card I + 1 : ℕ) : ℤ) * (s b j).length

theorem weightedCubeIntegerJetSum_bound {B : Type*} [Fintype B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I) (J : Finset (Finset I)) (shift : J → ℤ)
    (x : ∀ b j, IntegerScalarCubeBox I (s b j).length) (S : J) :
    |weightedCubeIntegerJetSum s J shift x S - shift S| ≤ weightedCubeJetBound s S := by
  classical
  simp only [weightedCubeIntegerJetSum, Pi.add_apply, Finset.sum_apply, add_sub_cancel_left]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro b _
  exact integerBooleanBlockJet_bound _ (fun j => (s b j).length)
    (fun j r => integerScalarCubeBox_coordinate_abs (x b j) r) S

theorem weightedCubeIntegerGridMass_eq {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I) (J : Finset (Finset I)) (shift z : J → ℤ)
    (M : ℕ) (hM : ∀ S : J, 2 * weightedCubeJetBound s S < (M : ℤ))
    (hz : ∀ S : J, |z S - shift S| ≤ weightedCubeJetBound s S) :
    integerGridMass (weightedCubeIntegerSource s) (weightedCubeIntegerJetSum s J shift) M z =
      finiteImageMass (weightedCubeIntegerSource s) (weightedCubeIntegerJetSum s J shift) z := by
  apply integerGridMass_eq_imageMass
  intro x _ S
  have hy := abs_le.mp (weightedCubeIntegerJetSum_bound s J shift x S)
  have hz' := abs_le.mp (hz S)
  have hM' := hM S
  rw [abs_lt]
  constructor <;> omega

end Erdos3

end

end OAI
