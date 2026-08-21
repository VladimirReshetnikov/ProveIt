import ExponentialIdentities.TwoBaseIntegerExponent.KernelDichotomy
import ExponentialIdentities.TwoBaseIntegerExponent.SecondIterateKernel

/-!
# Four-type classification of counterexamples by external valuation rank

This file formalizes the *four-type classification of counterexamples by external valuation
rank* recorded in the status matrix of the unified Alaoglu--Erdős report and proved in its
second-iterate-kernel section.

Let `x` be a hypothetical nonintegral solution, with integral outputs `M = 2 ^ x` and
`A = 3 ^ x`.  The report attaches to it the two *external valuation vectors*
`m_ext = (v_p M)_{p ≠ 2, 3}` and `a_ext = (v_p A)_{p ≠ 2, 3}`, and classifies `x` by the rank
of the pair.  Since membership of `M ^ r * A ^ s` in the saturated group `{2^u 3^v}` is exactly
the vanishing of every prime valuation outside `{2, 3}`, that rank is `2` minus the dimension of
the second-iterate kernel

  `K_x = ker ((r, s) ↦ r • m_ext + s • a_ext)`.

The kernel is already available in Lean, as the integral subgroup `kernelPairs M A` of
`SecondIterateKernel`, so this file expresses the rank through *kernel membership* rather than
through an abstract matrix rank.  The dictionary is:

* `ExternalRankZero`: both coordinate directions `(1, 0)` and `(0, 1)` lie in the kernel.  The
  kernel is an additive subgroup of `ℤ × ℤ` (`kernelAddSubgroup`), so this says the kernel is
  everything, that is, both external vectors vanish.
* `ExternalRankLeOne`: the kernel contains some nonzero vector.
* `ExternalRankOne`: `ExternalRankLeOne` but not `ExternalRankZero`.
* `ExternalRankTwo`: the kernel is trivial.

The classification itself is carried by the enumeration `ExternalRankType` together with the
predicate `HasExternalRankType`:

* `smoothFirst` --- rank one with `M` three-smooth (and then `A` rough);
* `smoothSecond` --- rank one with `A` three-smooth (and then `M` rough);
* `proportional` --- rank one with both outputs rough: the external vectors are nonzero and
  proportional, and the kernel line has one strictly positive and one strictly negative
  coordinate;
* `independent` --- rank two: both outputs rough and the external vectors independent.

The main results are:

* `not_externalRankZero`, the impossibility of the degenerate rank-zero case, which is
  immediate from `integer_of_threeSmooth_outputs` of `SmoothOutputs`;
* `existsUnique_hasExternalRankType`, the exhaustive and mutually exclusive four-way split;
* `hasExternalRankType_independent_iff_not_multiplicativelyDependentOutputs` together with
  `multiplicativelyDependentOutputs_iff_hasExternalRankType_rank_one`, identifying the
  dependent/independent branching of `KernelDichotomy` with the last of the four types.

The rank bound `kernelPairs_det_eq_zero` of `kernelPairs_prop_dim` enters where the report uses
it: it pins the kernel of the two smooth types to the corresponding coordinate axis
(`kernelPairs_snd_eq_zero_of_smoothFirst`, `kernelPairs_fst_eq_zero_of_smoothSecond`) and makes
the proportional type a genuine line (`exists_generator_of_proportional`).
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-! ### Three-smoothness of a natural output -/

/-- A natural output of a real power of a positive base is nonzero. -/
private theorem nat_ne_zero_of_natCast_eq_rpow {b y : ℝ} {M : ℕ} (hb : 0 < b)
    (h : (M : ℝ) = b ^ y) : M ≠ 0 := by
  have hpos : (0 : ℝ) < (M : ℝ) := by
    rw [h]
    exact Real.rpow_pos_of_pos hb y
  exact Nat.cast_ne_zero.mp hpos.ne'

/-- For a natural number, three-smoothness in the real sense of `IsThreeSmoothReal` is the
ordinary arithmetic statement that it is a product of a power of two and a power of three. -/
theorem isThreeSmoothReal_natCast_iff {n : ℕ} :
    IsThreeSmoothReal (n : ℝ) ↔ ∃ u v : ℕ, n = 2 ^ u * 3 ^ v := by
  constructor
  · rintro ⟨u, v, huv⟩
    refine ⟨u, v, ?_⟩
    have hcast : ((n : ℕ) : ℝ) = ((2 ^ u * 3 ^ v : ℕ) : ℝ) := by
      rw [huv]
      push_cast
      ring
    exact_mod_cast hcast
  · rintro ⟨u, v, huv⟩
    refine ⟨u, v, ?_⟩
    rw [huv]
    push_cast
    ring

/-! ### The external valuation rank, expressed through the kernel -/

/-- **External rank zero.**  Both coordinate directions lie in the second-iterate kernel.
Because the kernel is an additive subgroup of `ℤ × ℤ` (`kernelAddSubgroup`), this says that the
kernel is the whole of `ℤ × ℤ`, that is, that both external valuation vectors vanish. -/
def ExternalRankZero (M A : ℕ) : Prop :=
  ((1 : ℤ), (0 : ℤ)) ∈ kernelPairs M A ∧ ((0 : ℤ), (1 : ℤ)) ∈ kernelPairs M A

/-- **External rank at most one.**  The kernel contains a nonzero vector, so the linear map
`(r, s) ↦ r • m_ext + s • a_ext` has rank at most one. -/
def ExternalRankLeOne (M A : ℕ) : Prop :=
  ∃ a b : ℤ, ¬(a = 0 ∧ b = 0) ∧ (a, b) ∈ kernelPairs M A

/-- **External rank exactly one.**  The kernel is a nonzero proper subgroup of `ℤ × ℤ`. -/
def ExternalRankOne (M A : ℕ) : Prop :=
  ExternalRankLeOne M A ∧ ¬ ExternalRankZero M A

/-- **External rank two.**  The kernel is trivial: the two external valuation vectors are
linearly independent. -/
def ExternalRankTwo (M A : ℕ) : Prop :=
  ∀ a b : ℤ, (a, b) ∈ kernelPairs M A → a = 0 ∧ b = 0

/-- Unfolded form of `ExternalRankZero`. -/
theorem externalRankZero_def {M A : ℕ} :
    ExternalRankZero M A ↔
      ((1 : ℤ), (0 : ℤ)) ∈ kernelPairs M A ∧ ((0 : ℤ), (1 : ℤ)) ∈ kernelPairs M A :=
  Iff.rfl

/-- Unfolded form of `ExternalRankLeOne`. -/
theorem externalRankLeOne_def {M A : ℕ} :
    ExternalRankLeOne M A ↔ ∃ a b : ℤ, ¬(a = 0 ∧ b = 0) ∧ (a, b) ∈ kernelPairs M A :=
  Iff.rfl

/-- Unfolded form of `ExternalRankOne`. -/
theorem externalRankOne_def {M A : ℕ} :
    ExternalRankOne M A ↔ ExternalRankLeOne M A ∧ ¬ ExternalRankZero M A :=
  Iff.rfl

/-- Unfolded form of `ExternalRankTwo`. -/
theorem externalRankTwo_def {M A : ℕ} :
    ExternalRankTwo M A ↔ ∀ a b : ℤ, (a, b) ∈ kernelPairs M A → a = 0 ∧ b = 0 :=
  Iff.rfl

/-- Rank two is the exact complement of rank at most one. -/
theorem externalRankTwo_iff_not_externalRankLeOne {M A : ℕ} :
    ExternalRankTwo M A ↔ ¬ ExternalRankLeOne M A := by
  constructor
  · rintro h ⟨a, b, hab, hmem⟩
    exact hab (h a b hmem)
  · intro h a b hmem
    by_contra hab
    exact h ⟨a, b, hab, hmem⟩

/-! ### The degenerate rank-zero case is impossible -/

/-- Rank zero is exactly the case in which both outputs are three-smooth. -/
theorem externalRankZero_iff_threeSmooth_outputs {M A : ℕ} (hMne : M ≠ 0) (hAne : A ≠ 0) :
    ExternalRankZero M A ↔ IsThreeSmoothReal (M : ℝ) ∧ IsThreeSmoothReal (A : ℝ) := by
  constructor
  · intro h
    exact ⟨isThreeSmoothReal_natCast_iff.mpr
        ((mem_kernelPairs_one_zero_iff hMne hAne).mp (externalRankZero_def.mp h).1),
      isThreeSmoothReal_natCast_iff.mpr
        ((mem_kernelPairs_zero_one_iff hMne hAne).mp (externalRankZero_def.mp h).2)⟩
  · rintro ⟨hMs, hAs⟩
    exact externalRankZero_def.mpr
      ⟨(mem_kernelPairs_one_zero_iff hMne hAne).mpr (isThreeSmoothReal_natCast_iff.mp hMs),
        (mem_kernelPairs_zero_one_iff hMne hAne).mpr (isThreeSmoothReal_natCast_iff.mp hAs)⟩

/-- **The two outputs of a counterexample are never both three-smooth.**  This is the report's
`lp:thm-smooth`, in the machine-checked form supplied by `SmoothOutputs`. -/
theorem not_threeSmooth_outputs {y : ℝ} {M A : ℕ}
    (hM : (M : ℝ) = (2 : ℝ) ^ y) (hA : (A : ℝ) = (3 : ℝ) ^ y)
    (hy : y ∉ Set.range ((↑) : ℤ → ℝ)) :
    ¬ (IsThreeSmoothReal (M : ℝ) ∧ IsThreeSmoothReal (A : ℝ)) := by
  rintro ⟨hMs, hAs⟩
  refine hy (integer_of_threeSmooth_outputs ?_ ?_)
  · rw [← hM]
    exact hMs
  · rw [← hA]
    exact hAs

/-- **The rank-zero type is impossible.**  A hypothetical nonintegral solution never has
external rank zero: that would make both outputs three-smooth and force the exponent to be an
integer.  This is the first of the two deliverables of this file. -/
theorem not_externalRankZero {y : ℝ} {M A : ℕ}
    (hM : (M : ℝ) = (2 : ℝ) ^ y) (hA : (A : ℝ) = (3 : ℝ) ^ y)
    (hy : y ∉ Set.range ((↑) : ℤ → ℝ)) :
    ¬ ExternalRankZero M A := by
  have hMne : M ≠ 0 := nat_ne_zero_of_natCast_eq_rpow (by norm_num) hM
  have hAne : A ≠ 0 := nat_ne_zero_of_natCast_eq_rpow (by norm_num) hA
  intro h
  exact not_threeSmooth_outputs hM hA hy
    ((externalRankZero_iff_threeSmooth_outputs hMne hAne).mp h)

/-- A rough first output already rules out rank zero. -/
theorem not_externalRankZero_of_not_threeSmooth_fst {M A : ℕ} (hMne : M ≠ 0) (hAne : A ≠ 0)
    (hMs : ¬ IsThreeSmoothReal (M : ℝ)) : ¬ ExternalRankZero M A := fun hz =>
  hMs (isThreeSmoothReal_natCast_iff.mpr
    ((mem_kernelPairs_one_zero_iff hMne hAne).mp (externalRankZero_def.mp hz).1))

/-- A rough second output already rules out rank zero. -/
theorem not_externalRankZero_of_not_threeSmooth_snd {M A : ℕ} (hMne : M ≠ 0) (hAne : A ≠ 0)
    (hAs : ¬ IsThreeSmoothReal (A : ℝ)) : ¬ ExternalRankZero M A := fun hz =>
  hAs (isThreeSmoothReal_natCast_iff.mpr
    ((mem_kernelPairs_zero_one_iff hMne hAne).mp (externalRankZero_def.mp hz).2))

/-! ### Rank at most one is multiplicative dependence -/

/-- **The kernel detects multiplicative dependence.**  The four integers `M`, `A`, `2`, `3` are
multiplicatively dependent exactly when the second-iterate kernel contains a nonzero vector,
that is, exactly when the external rank is at most one.

The nontrivial half is that a relation `M ^ a * A ^ b * 2 ^ c * 3 ^ d = 1` with `(a, b, c, d)`
not all zero automatically has `(a, b) ≠ (0, 0)`; this is the irrationality of
`θ = log 3 / log 2`, packaged in `KernelDichotomy`. -/
theorem multiplicativelyDependentOutputs_iff_externalRankLeOne {y : ℝ} {M A : ℕ}
    (hM : (M : ℝ) = (2 : ℝ) ^ y) (hA : (A : ℝ) = (3 : ℝ) ^ y) :
    MultiplicativelyDependentOutputs M A ↔ ExternalRankLeOne M A := by
  constructor
  · intro h
    obtain ⟨a, b, c, d, hab, hlin⟩ :=
      secondIterateKernelRelation_of_multiplicativelyDependentOutputs hM hA h
    have hrel : (M : ℝ) ^ a * (A : ℝ) ^ b * (2 : ℝ) ^ c * (3 : ℝ) ^ d = 1 :=
      (outputs_zpow_eq_one_iff hM hA a b c d).mpr hlin
    exact externalRankLeOne_def.mpr ⟨a, b, hab, mem_kernelPairs_iff.mpr ⟨c, d, hrel⟩⟩
  · intro h
    obtain ⟨a, b, hab, hmem⟩ := externalRankLeOne_def.mp h
    obtain ⟨c, d, heq⟩ := mem_kernelPairs_iff.mp hmem
    exact ⟨a, b, c, d, fun hzero => hab ⟨hzero.1, hzero.2.1⟩, heq⟩

/-- Multiplicative independence of `M`, `A`, `2`, `3` is exactly external rank two. -/
theorem not_multiplicativelyDependentOutputs_iff_externalRankTwo {y : ℝ} {M A : ℕ}
    (hM : (M : ℝ) = (2 : ℝ) ^ y) (hA : (A : ℝ) = (3 : ℝ) ^ y) :
    ¬ MultiplicativelyDependentOutputs M A ↔ ExternalRankTwo M A := by
  rw [externalRankTwo_iff_not_externalRankLeOne,
    multiplicativelyDependentOutputs_iff_externalRankLeOne hM hA]

/-! ### Nonvanishing of the kernel coordinates when both outputs are rough -/

/-- If the second output is rough, no nonzero kernel vector has vanishing first coordinate. -/
theorem fst_ne_zero_of_mem_kernelPairs {M A : ℕ} (hMne : M ≠ 0) (hAne : A ≠ 0)
    (hAs : ¬ IsThreeSmoothReal (A : ℝ)) {a b : ℤ} (hab : ¬(a = 0 ∧ b = 0))
    (hmem : (a, b) ∈ kernelPairs M A) : a ≠ 0 := by
  intro ha0
  subst ha0
  have hb : b ≠ 0 := fun hb0 => hab ⟨rfl, hb0⟩
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · have hmem' : ((0 : ℤ), -b) ∈ kernelPairs M A := by
      have hneg' := neg_mem_kernelPairs hmem
      rwa [neg_zero] at hneg'
    exact hAs (isThreeSmoothReal_natCast_iff.mpr
      (threeSmooth_snd_of_mem_kernelPairs hMne hAne (by omega : (0 : ℤ) < -b) hmem'))
  · exact hAs (isThreeSmoothReal_natCast_iff.mpr
      (threeSmooth_snd_of_mem_kernelPairs hMne hAne hpos hmem))

/-- If the first output is rough, no nonzero kernel vector has vanishing second coordinate. -/
theorem snd_ne_zero_of_mem_kernelPairs {M A : ℕ} (hMne : M ≠ 0) (hAne : A ≠ 0)
    (hMs : ¬ IsThreeSmoothReal (M : ℝ)) {a b : ℤ} (hab : ¬(a = 0 ∧ b = 0))
    (hmem : (a, b) ∈ kernelPairs M A) : b ≠ 0 := by
  intro hb0
  subst hb0
  have ha : a ≠ 0 := fun ha0 => hab ⟨ha0, rfl⟩
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have hmem' : (-a, (0 : ℤ)) ∈ kernelPairs M A := by
      have hneg' := neg_mem_kernelPairs hmem
      rwa [neg_zero] at hneg'
    exact hMs (isThreeSmoothReal_natCast_iff.mpr
      (threeSmooth_fst_of_mem_kernelPairs hMne hAne (by omega : (0 : ℤ) < -a) hmem'))
  · exact hMs (isThreeSmoothReal_natCast_iff.mpr
      (threeSmooth_fst_of_mem_kernelPairs hMne hAne hpos hmem))

/-! ### The four external types -/

/-- **The four external valuation types of a hypothetical counterexample.**  The degenerate
rank-zero type is absent by design: `not_externalRankZero` shows it cannot occur. -/
inductive ExternalRankType
  /-- Rank one with the first output three-smooth. -/
  | smoothFirst
  /-- Rank one with the second output three-smooth. -/
  | smoothSecond
  /-- Rank one with both outputs rough: the external vectors are proportional. -/
  | proportional
  /-- Rank two: both outputs rough and the external vectors independent. -/
  | independent

/-- **The classifying predicate.**  Which of the four external types the pair of outputs
`(M, A)` realizes.  The rank is expressed through membership of the second-iterate kernel
`kernelPairs M A`, following the report's identification of the kernel with the kernel of
`(r, s) ↦ r • m_ext + s • a_ext`. -/
def HasExternalRankType (M A : ℕ) : ExternalRankType → Prop
  | ExternalRankType.smoothFirst =>
      IsThreeSmoothReal (M : ℝ) ∧ ¬ IsThreeSmoothReal (A : ℝ)
  | ExternalRankType.smoothSecond =>
      ¬ IsThreeSmoothReal (M : ℝ) ∧ IsThreeSmoothReal (A : ℝ)
  | ExternalRankType.proportional =>
      ¬ IsThreeSmoothReal (M : ℝ) ∧ ¬ IsThreeSmoothReal (A : ℝ) ∧
        ∃ a b : ℤ, ¬(a = 0 ∧ b = 0) ∧ (a, b) ∈ kernelPairs M A
  | ExternalRankType.independent =>
      ¬ IsThreeSmoothReal (M : ℝ) ∧ ¬ IsThreeSmoothReal (A : ℝ) ∧
        ∀ a b : ℤ, (a, b) ∈ kernelPairs M A → a = 0 ∧ b = 0

/-- Unfolded form of the first smooth type. -/
theorem hasExternalRankType_smoothFirst_iff {M A : ℕ} :
    HasExternalRankType M A ExternalRankType.smoothFirst ↔
      IsThreeSmoothReal (M : ℝ) ∧ ¬ IsThreeSmoothReal (A : ℝ) :=
  Iff.rfl

/-- Unfolded form of the second smooth type. -/
theorem hasExternalRankType_smoothSecond_iff {M A : ℕ} :
    HasExternalRankType M A ExternalRankType.smoothSecond ↔
      ¬ IsThreeSmoothReal (M : ℝ) ∧ IsThreeSmoothReal (A : ℝ) :=
  Iff.rfl

/-- Unfolded form of the proportional type, in rank language. -/
theorem hasExternalRankType_proportional_iff {M A : ℕ} :
    HasExternalRankType M A ExternalRankType.proportional ↔
      ¬ IsThreeSmoothReal (M : ℝ) ∧ ¬ IsThreeSmoothReal (A : ℝ) ∧ ExternalRankLeOne M A :=
  Iff.rfl

/-- Unfolded form of the independent type, in rank language. -/
theorem hasExternalRankType_independent_iff {M A : ℕ} :
    HasExternalRankType M A ExternalRankType.independent ↔
      ¬ IsThreeSmoothReal (M : ℝ) ∧ ¬ IsThreeSmoothReal (A : ℝ) ∧ ExternalRankTwo M A :=
  Iff.rfl

/-! ### Exhaustiveness and mutual exclusivity -/

/-- **Exhaustiveness.**  Every hypothetical nonintegral solution realizes one of the four
external types.  The rank-zero case is eliminated by `not_threeSmooth_outputs`. -/
theorem exists_hasExternalRankType {y : ℝ} {M A : ℕ}
    (hM : (M : ℝ) = (2 : ℝ) ^ y) (hA : (A : ℝ) = (3 : ℝ) ^ y)
    (hy : y ∉ Set.range ((↑) : ℤ → ℝ)) :
    ∃ t : ExternalRankType, HasExternalRankType M A t := by
  by_cases hMs : IsThreeSmoothReal (M : ℝ)
  · have hAs : ¬ IsThreeSmoothReal (A : ℝ) := fun hAs =>
      not_threeSmooth_outputs hM hA hy ⟨hMs, hAs⟩
    exact ⟨ExternalRankType.smoothFirst, hasExternalRankType_smoothFirst_iff.mpr ⟨hMs, hAs⟩⟩
  · by_cases hAs : IsThreeSmoothReal (A : ℝ)
    · exact ⟨ExternalRankType.smoothSecond, hasExternalRankType_smoothSecond_iff.mpr ⟨hMs, hAs⟩⟩
    · by_cases hrank : ExternalRankLeOne M A
      · exact ⟨ExternalRankType.proportional,
          hasExternalRankType_proportional_iff.mpr ⟨hMs, hAs, hrank⟩⟩
      · exact ⟨ExternalRankType.independent, hasExternalRankType_independent_iff.mpr
          ⟨hMs, hAs, externalRankTwo_iff_not_externalRankLeOne.mpr hrank⟩⟩

/-- **Mutual exclusivity.**  No pair of outputs realizes two different external types.  This is
unconditional: it needs neither the exponent nor the exclusion of the rank-zero case. -/
theorem eq_of_hasExternalRankType {M A : ℕ} {t t' : ExternalRankType}
    (h : HasExternalRankType M A t) (h' : HasExternalRankType M A t') : t = t' := by
  cases t <;> cases t' <;>
    simp only [hasExternalRankType_smoothFirst_iff, hasExternalRankType_smoothSecond_iff,
      hasExternalRankType_proportional_iff, hasExternalRankType_independent_iff,
      externalRankLeOne_def, externalRankTwo_def] at h h' <;>
    first
      | rfl
      | exact absurd h.1 h'.1
      | exact absurd h'.1 h.1
      | exact absurd h.2 h'.2.1
      | exact absurd h'.2 h.2.1
      | (obtain ⟨a, b, hab, hmem⟩ := h.2.2; exact absurd (h'.2.2 a b hmem) hab)
      | (obtain ⟨a, b, hab, hmem⟩ := h'.2.2; exact absurd (h.2.2 a b hmem) hab)

/-- **The four-type classification.**  A hypothetical nonintegral solution of the two-base
problem realizes exactly one of the four external valuation types.  Together with
`not_externalRankZero`, which discards the degenerate rank-zero pattern, this is the report's
classification of counterexamples by external valuation rank. -/
theorem existsUnique_hasExternalRankType {y : ℝ} {M A : ℕ}
    (hM : (M : ℝ) = (2 : ℝ) ^ y) (hA : (A : ℝ) = (3 : ℝ) ^ y)
    (hy : y ∉ Set.range ((↑) : ℤ → ℝ)) :
    ∃! t : ExternalRankType, HasExternalRankType M A t := by
  obtain ⟨t, ht⟩ := exists_hasExternalRankType hM hA hy
  exact ⟨t, ht, fun t' ht' => eq_of_hasExternalRankType ht' ht⟩

/-- The classification for a `TwoBaseNonintegerSolution`, with the two natural outputs
produced along the way. -/
theorem TwoBaseNonintegerSolution.externalRankClassification {y : ℝ}
    (hy : TwoBaseNonintegerSolution y) :
    ∃ M A : ℕ, (M : ℝ) = (2 : ℝ) ^ y ∧ (A : ℝ) = (3 : ℝ) ^ y ∧
      ∃! t : ExternalRankType, HasExternalRankType M A t := by
  obtain ⟨M, A, hM, hA⟩ := exists_nat_outputs_of_twoBaseIntegralSolution hy.1
  exact ⟨M, A, hM, hA, existsUnique_hasExternalRankType hM hA hy.2⟩

/-! ### The types carry the announced ranks -/

/-- The three non-degenerate rank-one types really have external rank one. -/
theorem externalRankOne_of_hasExternalRankType_ne_independent {M A : ℕ}
    (hMne : M ≠ 0) (hAne : A ≠ 0) {t : ExternalRankType}
    (ht : HasExternalRankType M A t) (hne : t ≠ ExternalRankType.independent) :
    ExternalRankOne M A := by
  cases t
  · obtain ⟨hMs, hAs⟩ := hasExternalRankType_smoothFirst_iff.mp ht
    refine externalRankOne_def.mpr ⟨externalRankLeOne_def.mpr ⟨1, 0, ?_, ?_⟩, ?_⟩
    · exact fun hz => one_ne_zero hz.1
    · exact (mem_kernelPairs_one_zero_iff hMne hAne).mpr (isThreeSmoothReal_natCast_iff.mp hMs)
    · exact not_externalRankZero_of_not_threeSmooth_snd hMne hAne hAs
  · obtain ⟨hMs, hAs⟩ := hasExternalRankType_smoothSecond_iff.mp ht
    refine externalRankOne_def.mpr ⟨externalRankLeOne_def.mpr ⟨0, 1, ?_, ?_⟩, ?_⟩
    · exact fun hz => one_ne_zero hz.2
    · exact (mem_kernelPairs_zero_one_iff hMne hAne).mpr (isThreeSmoothReal_natCast_iff.mp hAs)
    · exact not_externalRankZero_of_not_threeSmooth_fst hMne hAne hMs
  · obtain ⟨hMs, _hAs, hrank⟩ := hasExternalRankType_proportional_iff.mp ht
    exact externalRankOne_def.mpr
      ⟨hrank, not_externalRankZero_of_not_threeSmooth_fst hMne hAne hMs⟩
  · exact absurd rfl hne

/-- The independent type really has external rank two. -/
theorem externalRankTwo_of_hasExternalRankType_independent {M A : ℕ}
    (ht : HasExternalRankType M A ExternalRankType.independent) : ExternalRankTwo M A :=
  (hasExternalRankType_independent_iff.mp ht).2.2

/-! ### The dependent and independent branches -/

/-- **The independent type is exactly the multiplicatively independent branch.**  This is the
third deliverable: the dependent/independent dichotomy of `KernelDichotomy` sits in the
classification as the split between the last type and the other three. -/
theorem hasExternalRankType_independent_iff_not_multiplicativelyDependentOutputs {y : ℝ}
    {M A : ℕ} (hM : (M : ℝ) = (2 : ℝ) ^ y) (hA : (A : ℝ) = (3 : ℝ) ^ y) :
    HasExternalRankType M A ExternalRankType.independent ↔
      ¬ MultiplicativelyDependentOutputs M A := by
  have hMne : M ≠ 0 := nat_ne_zero_of_natCast_eq_rpow (by norm_num) hM
  have hAne : A ≠ 0 := nat_ne_zero_of_natCast_eq_rpow (by norm_num) hA
  constructor
  · intro ht
    exact (not_multiplicativelyDependentOutputs_iff_externalRankTwo hM hA).mpr
      (hasExternalRankType_independent_iff.mp ht).2.2
  · intro hind
    have hrank : ExternalRankTwo M A :=
      (not_multiplicativelyDependentOutputs_iff_externalRankTwo hM hA).mp hind
    refine hasExternalRankType_independent_iff.mpr ⟨?_, ?_, hrank⟩
    · intro hMs
      refine hind ((multiplicativelyDependentOutputs_iff_externalRankLeOne hM hA).mpr ?_)
      exact externalRankLeOne_def.mpr ⟨1, 0, fun hz => one_ne_zero hz.1,
        (mem_kernelPairs_one_zero_iff hMne hAne).mpr (isThreeSmoothReal_natCast_iff.mp hMs)⟩
    · intro hAs
      refine hind ((multiplicativelyDependentOutputs_iff_externalRankLeOne hM hA).mpr ?_)
      exact externalRankLeOne_def.mpr ⟨0, 1, fun hz => one_ne_zero hz.2,
        (mem_kernelPairs_zero_one_iff hMne hAne).mpr (isThreeSmoothReal_natCast_iff.mp hAs)⟩

/-- **The dependent branch is the union of the first three types.**  Multiplicative dependence
of `M`, `A`, `2`, `3` holds exactly when the external rank is one, that is, in the two smooth
types and the proportional type. -/
theorem multiplicativelyDependentOutputs_iff_hasExternalRankType_rank_one {y : ℝ} {M A : ℕ}
    (hM : (M : ℝ) = (2 : ℝ) ^ y) (hA : (A : ℝ) = (3 : ℝ) ^ y)
    (hy : y ∉ Set.range ((↑) : ℤ → ℝ)) :
    MultiplicativelyDependentOutputs M A ↔
      HasExternalRankType M A ExternalRankType.smoothFirst ∨
        HasExternalRankType M A ExternalRankType.smoothSecond ∨
          HasExternalRankType M A ExternalRankType.proportional := by
  have hMne : M ≠ 0 := nat_ne_zero_of_natCast_eq_rpow (by norm_num) hM
  have hAne : A ≠ 0 := nat_ne_zero_of_natCast_eq_rpow (by norm_num) hA
  constructor
  · intro hdep
    obtain ⟨t, ht⟩ := exists_hasExternalRankType hM hA hy
    cases t
    · exact Or.inl ht
    · exact Or.inr (Or.inl ht)
    · exact Or.inr (Or.inr ht)
    · exact absurd hdep
        ((hasExternalRankType_independent_iff_not_multiplicativelyDependentOutputs hM hA).mp ht)
  · intro ht
    refine (multiplicativelyDependentOutputs_iff_externalRankLeOne hM hA).mpr ?_
    rcases ht with h | h | h
    · exact externalRankLeOne_def.mpr ⟨1, 0, fun hz => one_ne_zero hz.1,
        (mem_kernelPairs_one_zero_iff hMne hAne).mpr (isThreeSmoothReal_natCast_iff.mp
          (hasExternalRankType_smoothFirst_iff.mp h).1)⟩
    · exact externalRankLeOne_def.mpr ⟨0, 1, fun hz => one_ne_zero hz.2,
        (mem_kernelPairs_zero_one_iff hMne hAne).mpr (isThreeSmoothReal_natCast_iff.mp
          (hasExternalRankType_smoothSecond_iff.mp h).2)⟩
    · exact (hasExternalRankType_proportional_iff.mp h).2.2

/-! ### The shape of the kernel in each surviving type -/

/-- **The first smooth type has kernel the first coordinate axis.**  The direction `(1, 0)`
lies in the kernel, and the rank bound `kernelPairs_det_eq_zero` forces every kernel vector to
have vanishing second coordinate. -/
theorem kernelPairs_snd_eq_zero_of_smoothFirst {y : ℝ} {M A : ℕ}
    (hM : (M : ℝ) = (2 : ℝ) ^ y) (hA : (A : ℝ) = (3 : ℝ) ^ y)
    (hy : y ∉ Set.range ((↑) : ℤ → ℝ))
    (ht : HasExternalRankType M A ExternalRankType.smoothFirst) :
    ((1 : ℤ), (0 : ℤ)) ∈ kernelPairs M A ∧
      ∀ a b : ℤ, (a, b) ∈ kernelPairs M A → b = 0 := by
  have hMne : M ≠ 0 := nat_ne_zero_of_natCast_eq_rpow (by norm_num) hM
  have hAne : A ≠ 0 := nat_ne_zero_of_natCast_eq_rpow (by norm_num) hA
  have hMs := (hasExternalRankType_smoothFirst_iff.mp ht).1
  have h10 : ((1 : ℤ), (0 : ℤ)) ∈ kernelPairs M A :=
    (mem_kernelPairs_one_zero_iff hMne hAne).mpr (isThreeSmoothReal_natCast_iff.mp hMs)
  refine ⟨h10, ?_⟩
  intro a b hmem
  have hdet := kernelPairs_det_eq_zero hM hA hy h10 hmem
  omega

/-- **The second smooth type has kernel the second coordinate axis.** -/
theorem kernelPairs_fst_eq_zero_of_smoothSecond {y : ℝ} {M A : ℕ}
    (hM : (M : ℝ) = (2 : ℝ) ^ y) (hA : (A : ℝ) = (3 : ℝ) ^ y)
    (hy : y ∉ Set.range ((↑) : ℤ → ℝ))
    (ht : HasExternalRankType M A ExternalRankType.smoothSecond) :
    ((0 : ℤ), (1 : ℤ)) ∈ kernelPairs M A ∧
      ∀ a b : ℤ, (a, b) ∈ kernelPairs M A → a = 0 := by
  have hMne : M ≠ 0 := nat_ne_zero_of_natCast_eq_rpow (by norm_num) hM
  have hAne : A ≠ 0 := nat_ne_zero_of_natCast_eq_rpow (by norm_num) hA
  have hAs := (hasExternalRankType_smoothSecond_iff.mp ht).2
  have h01 : ((0 : ℤ), (1 : ℤ)) ∈ kernelPairs M A :=
    (mem_kernelPairs_zero_one_iff hMne hAne).mpr (isThreeSmoothReal_natCast_iff.mp hAs)
  refine ⟨h01, ?_⟩
  intro a b hmem
  have hdet := kernelPairs_det_eq_zero hM hA hy h01 hmem
  omega

/-- **The proportional type is a genuine line with mixed signs.**  In the third type the kernel
is generated, up to proportionality, by a single vector whose two coordinates are nonzero and
of opposite sign, and every kernel vector is proportional to it.

The two ingredients are the parts of `kernelPairs_prop_dim`: `kernelPairs_mul_nonpos` for the
sign statement and `kernelPairs_det_eq_zero` for the rank bound.  This is the report's remark
that in the dependent branch the relation is essentially unique and its exponents on `M` and
`A` have opposite signs unless one of the outputs is three-smooth. -/
theorem exists_generator_of_proportional {y : ℝ} {M A : ℕ}
    (hM : (M : ℝ) = (2 : ℝ) ^ y) (hA : (A : ℝ) = (3 : ℝ) ^ y)
    (hy : y ∉ Set.range ((↑) : ℤ → ℝ))
    (ht : HasExternalRankType M A ExternalRankType.proportional) :
    ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a * b < 0 ∧ (a, b) ∈ kernelPairs M A ∧
      ∀ a' b' : ℤ, (a', b') ∈ kernelPairs M A → a * b' - a' * b = 0 := by
  have hMne : M ≠ 0 := nat_ne_zero_of_natCast_eq_rpow (by norm_num) hM
  have hAne : A ≠ 0 := nat_ne_zero_of_natCast_eq_rpow (by norm_num) hA
  obtain ⟨hMs, hAs, hrank⟩ := hasExternalRankType_proportional_iff.mp ht
  obtain ⟨a, b, hab, hmem⟩ := externalRankLeOne_def.mp hrank
  have ha : a ≠ 0 := fst_ne_zero_of_mem_kernelPairs hMne hAne hAs hab hmem
  have hb : b ≠ 0 := snd_ne_zero_of_mem_kernelPairs hMne hAne hMs hab hmem
  have hle : a * b ≤ 0 := kernelPairs_mul_nonpos hM hA hy hmem
  have hne : a * b ≠ 0 := mul_ne_zero ha hb
  refine ⟨a, b, ha, hb, lt_of_le_of_ne hle hne, hmem, ?_⟩
  intro a' b' hmem'
  exact kernelPairs_det_eq_zero hM hA hy hmem hmem'

end LeanProofs.TwoBaseIntegerExponent
