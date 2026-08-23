import IntegerPoints.GKBProcessAux
import IntegerPoints.GKBProcessGeometry
import IntegerPoints.GKLemma39Class

/-!
# Uniform parameters for the Graham--Kolesnik B-process

This module is the class-management and parameter-selection layer for
Graham--Kolesnik Theorem 3.10.  It has three roles.

* It supplies theory-independent operations on `InGKClass`: restriction to a
  subinterval, lowering the derivative order, and enlarging the relative
  error when the unsigned model factor is nonnegative.
* It packages one input exponent-pair estimate at the dual exponent `1 / s`
  together with a sufficiently high original order and a sufficiently small
  original error.  The latter is chosen using `|C39| + 1`, so no sign
  assumption on the constant returned by Lemma 3.9 is hidden.
* It fixes a number of dyadic blocks depending only on `s` and proves exact
  truncated-block cover and sum identities for the derivative interval.

The output constant of the input exponent-pair estimate is normalized to be
nonnegative.  Both error inequalities needed downstream are explicit:
`C39 * eps <= eps0` for applying the input pair, and
`C39 * eps <= 1/4` for monotonicity of the dual stationary-phase weight.
-/

open Real Finset Set

namespace LeanProofs.IntegerPoints

/-! ## Generic management of `InGKClass` -/

namespace InGKClass

/-- Restrict a Graham--Kolesnik class to a closed subinterval. -/
theorem restrictInterval
    {N s y eps a b c d : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hf : InGKClass N P s y eps a b f)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    InGKClass N P s y eps c d f := by
  obtain ⟨hNa, hab, hb2N, hcont, hestimate⟩ := hf
  refine ⟨hNa.trans hac, hcd, hdb.trans hb2N, hcont, ?_⟩
  intro p hp t ht
  exact hestimate p hp t ⟨hac.trans ht.1, ht.2.trans hdb⟩

/-- Lower the derivative order required of a Graham--Kolesnik class. -/
theorem lowerOrder
    {N s y eps a b : ℝ} {P Q : ℕ} {f : ℝ → ℝ}
    (hQP : Q ≤ P) (hf : InGKClass N P s y eps a b f) :
    InGKClass N Q s y eps a b f := by
  obtain ⟨hNa, hab, hb2N, hcont, hestimate⟩ := hf
  refine ⟨hNa, hab, hb2N, hcont.of_le (by exact_mod_cast hQP), ?_⟩
  intro p hp t ht
  exact hestimate p (hp.trans_le hQP) t ht

/-- Enlarge the relative error when every unsigned model factor is
nonnegative.  Keeping this premise explicit makes the lemma usable beyond the
positive-parameter specialization below. -/
theorem enlargeError
    {N s y eps eps' a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (heps : eps ≤ eps')
    (hmodel : ∀ p : ℕ, p < P → ∀ t ∈ Icc a b,
      0 ≤ (∏ i ∈ Finset.range p, (s + i)) * y * t ^ (-s - p))
    (hf : InGKClass N P s y eps a b f) :
    InGKClass N P s y eps' a b f := by
  obtain ⟨hNa, hab, hb2N, hcont, hestimate⟩ := hf
  refine ⟨hNa, hab, hb2N, hcont, ?_⟩
  intro p hp t ht
  calc
    |iteratedDeriv (p + 1) f t -
        (-1) ^ p * (∏ i ∈ Finset.range p, (s + i)) * y * t ^ (-s - p)| <
        eps * (∏ i ∈ Finset.range p, (s + i)) * y * t ^ (-s - p) :=
      hestimate p hp t ht
    _ = eps *
        ((∏ i ∈ Finset.range p, (s + i)) * y * t ^ (-s - p)) := by ring
    _ ≤ eps' *
        ((∏ i ∈ Finset.range p, (s + i)) * y * t ^ (-s - p)) :=
      mul_le_mul_of_nonneg_right heps (hmodel p hp t ht)
    _ = eps' * (∏ i ∈ Finset.range p, (s + i)) * y * t ^ (-s - p) := by ring

/-- Positivity of the class scale and its parameters makes every unsigned
model factor nonnegative. -/
theorem modelFactor_nonneg
    {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 ≤ s) (hy : 0 ≤ y)
    (hf : InGKClass N P s y eps a b f)
    (p : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    0 ≤ (∏ i ∈ Finset.range p, (s + i)) * y * t ^ (-s - p) := by
  have ht0 : 0 < t := hN.trans_le (hf.1.trans ht.1)
  have hprod : 0 ≤ ∏ i ∈ Finset.range p, (s + i) := by
    exact Finset.prod_nonneg fun i _ => by positivity
  have hpow : 0 ≤ t ^ (-s - p) := (Real.rpow_pos_of_pos ht0 _).le
  positivity

/-- Simultaneously lower the derivative order and enlarge the error in the
standard positive-parameter setting. -/
theorem weaken_of_pos
    {N s y eps eps' a b : ℝ} {P Q : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hQP : Q ≤ P) (heps : eps ≤ eps')
    (hf : InGKClass N P s y eps a b f) :
    InGKClass N Q s y eps' a b f := by
  have hlow : InGKClass N Q s y eps a b f := lowerOrder hQP hf
  exact enlargeError heps
    (fun p hp t ht => modelFactor_nonneg hN hs.le hy.le hlow p ht) hlow

end InGKClass

namespace GKB

/-! ## Robust error selection -/

/-- An original error small enough for both the input exponent-pair error and
the quarter-sized dual error.  Division by `|C| + 1` is robust even if the
constant supplied by Lemma 3.9 has arbitrary sign. -/
noncomputable def controlledError (eps0 C : ℝ) : ℝ :=
  min eps0 (1 / 4) / (|C| + 1)

/-- All bounds furnished by `controlledError`. -/
theorem controlledError_spec {eps0 C : ℝ} (heps0 : 0 < eps0) :
    0 < controlledError eps0 C ∧
      controlledError eps0 C < 1 / 2 ∧
      controlledError eps0 C ≤ 1 / 4 ∧
      C * controlledError eps0 C ≤ eps0 ∧
      C * controlledError eps0 C ≤ 1 / 4 := by
  have hden : 0 < |C| + 1 := by positivity
  have hmin : 0 < min eps0 (1 / 4) := lt_min heps0 (by norm_num)
  have hpos : 0 < controlledError eps0 C := by
    unfold controlledError
    exact div_pos hmin hden
  have hquarter : controlledError eps0 C ≤ 1 / 4 := by
    rw [controlledError, div_le_iff₀ hden]
    have hminQuarter : min eps0 (1 / 4) ≤ 1 / 4 := min_le_right _ _
    have hdenOne : 1 ≤ |C| + 1 := by linarith [abs_nonneg C]
    nlinarith
  have hCden : C ≤ |C| + 1 :=
    (le_abs_self C).trans (by linarith [abs_nonneg C])
  have hscaled : C * controlledError eps0 C ≤ min eps0 (1 / 4) := by
    calc
      C * controlledError eps0 C ≤
          (|C| + 1) * controlledError eps0 C :=
        mul_le_mul_of_nonneg_right hCden hpos.le
      _ = min eps0 (1 / 4) := by
        rw [controlledError, mul_comm]
        exact div_mul_cancel₀ _ hden.ne'
  exact ⟨hpos, hquarter.trans_lt (by norm_num), hquarter,
    hscaled.trans (min_le_left _ _), hscaled.trans (min_le_right _ _)⟩

/-! ## A fixed finite dyadic cover -/

/-- A number of dyadic blocks, depending only on `s`, whose total ratio is
larger than the endpoint ratio from `GKB.endpoint_ratio_bound`. -/
noncomputable def dyadicDepth (s : ℝ) : ℕ :=
  Classical.choose
    (pow_unbounded_of_one_lt (endpointRatio s) (by norm_num : (1 : ℝ) < 2))

theorem endpointRatio_lt_two_pow (s : ℝ) :
    endpointRatio s < (2 : ℝ) ^ dyadicDepth s :=
  Classical.choose_spec
    (pow_unbounded_of_one_lt (endpointRatio s) (by norm_num : (1 : ℝ) < 2))

/-- A dyadic block truncated at the final upper endpoint `B`. -/
noncomputable def truncatedDyadicBlock (B J : ℝ) (j : ℕ) : Finset ℕ :=
  intRange (dyadicCut J j) (min B (dyadicCut J (j + 1)))

/-- The recursive union of the first `q` truncated dyadic blocks. -/
noncomputable def truncatedDyadicCover (B J : ℝ) : ℕ → Finset ℕ
  | 0 => ∅
  | q + 1 => truncatedDyadicCover B J q ∪ truncatedDyadicBlock B J q

@[simp]
theorem truncatedDyadicCover_zero (B J : ℝ) :
    truncatedDyadicCover B J 0 = ∅ := rfl

theorem truncatedDyadicCover_succ (B J : ℝ) (q : ℕ) :
    truncatedDyadicCover B J (q + 1) =
      truncatedDyadicCover B J q ∪ truncatedDyadicBlock B J q := rfl

/-- Two real half-open ranges sharing an ordered endpoint merge exactly. -/
theorem intRange_union_adjacent {A B C : ℝ} (hAB : A ≤ B) (hBC : B ≤ C) :
    intRange A B ∪ intRange B C = intRange A C := by
  unfold intRange
  exact Finset.Ioc_union_Ioc_eq_Ioc
    (Nat.floor_mono hAB) (Nat.floor_mono hBC)

/-- The union step for two consecutive dyadic blocks, including the case in
which truncation has already occurred before the new block begins. -/
theorem intRange_min_middle_union {J B C D : ℝ}
    (hJC : J ≤ C) (hCD : C ≤ D) :
    intRange J (min B C) ∪ intRange C (min B D) =
      intRange J (min B D) := by
  rcases le_total B C with hBC | hCB
  · have hBD : B ≤ D := hBC.trans hCD
    rw [min_eq_left hBC, min_eq_left hBD]
    have hempty : intRange C B = ∅ := by
      rw [intRange, Finset.Ioc_eq_empty_of_le]
      exact Nat.floor_mono hBC
    rw [hempty, Finset.union_empty]
  · rw [min_eq_right hCB]
    exact intRange_union_adjacent hJC (le_min hCB hCD)

/-- The first `q` truncated blocks are exactly the range from `J` to the
smaller of `B` and the `q`-th dyadic cut. -/
theorem truncatedDyadicCover_eq_intRange {B J : ℝ}
    (hJ : 0 ≤ J) (hJB : J ≤ B) (q : ℕ) :
    truncatedDyadicCover B J q = intRange J (min B (dyadicCut J q)) := by
  induction q with
  | zero =>
      rw [truncatedDyadicCover_zero, dyadicCut_zero, min_eq_right hJB]
      simp [intRange]
  | succ q ih =>
      rw [truncatedDyadicCover_succ, ih]
      have hJq : J ≤ dyadicCut J q := by
        calc
          J = dyadicCut J 0 := (dyadicCut_zero J).symm
          _ ≤ dyadicCut J q := dyadicCut_monotone hJ (Nat.zero_le q)
      exact intRange_min_middle_union hJq (dyadicCut_le_succ hJ q)

/-- The accumulated cover is disjoint from the next truncated block. -/
theorem disjoint_truncatedDyadicCover_next {B J : ℝ}
    (hJ : 0 ≤ J) (hJB : J ≤ B) (q : ℕ) :
    Disjoint (truncatedDyadicCover B J q) (truncatedDyadicBlock B J q) := by
  rw [truncatedDyadicCover_eq_intRange hJ hJB]
  unfold truncatedDyadicBlock intRange
  exact Finset.Ioc_disjoint_Ioc_of_le
    (Nat.floor_mono (min_le_right B (dyadicCut J q)))

/-- Sum form of the finite disjoint dyadic decomposition. -/
theorem sum_truncatedDyadicCover
    {M : Type*} [AddCommMonoid M] (g : ℕ → M)
    {B J : ℝ} (hJ : 0 ≤ J) (hJB : J ≤ B) (q : ℕ) :
    ∑ n ∈ truncatedDyadicCover B J q, g n =
      ∑ j ∈ Finset.range q, ∑ n ∈ truncatedDyadicBlock B J j, g n := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [truncatedDyadicCover_succ,
        Finset.sum_union (disjoint_truncatedDyadicCover_next hJ hJB q),
        ih, Finset.sum_range_succ]

/-! ## Geometry of the derivative interval -/

/-- The fixed terminal dyadic cut lies strictly beyond the upper derivative
endpoint. -/
theorem derivative_upper_lt_dyadicCut
    {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f) :
    deriv f a < dyadicCut (deriv f b) (dyadicDepth s) := by
  have hAlpha : 0 < deriv f b :=
    (endpoint_derivative_bounds hN hs hy hP heps hf).2.2.1
  have hratio := endpointRatio_lt_two_pow s
  calc
    deriv f a < endpointRatio s * deriv f b :=
      (endpoint_ratio_bound hN hs hy hP heps hf).1
    _ < (2 : ℝ) ^ dyadicDepth s * deriv f b :=
      mul_lt_mul_of_pos_right hratio hAlpha
    _ = dyadicCut (deriv f b) (dyadicDepth s) := rfl

/-- Closed-interval form of the fixed dyadic coverage. -/
theorem derivative_Icc_subset_dyadic_span
    {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f) :
    Icc (deriv f b) (deriv f a) ⊆
      Icc (deriv f b) (dyadicCut (deriv f b) (dyadicDepth s)) :=
  Set.Icc_subset_Icc le_rfl
    (derivative_upper_lt_dyadicCut hN hs hy hP heps hf).le

/-- Exact finite-cover identity for the integer derivative range. -/
theorem derivative_truncatedDyadicCover_eq_intRange
    {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f) :
    truncatedDyadicCover (deriv f a) (deriv f b) (dyadicDepth s) =
      intRange (deriv f b) (deriv f a) := by
  have hends := endpoint_derivative_bounds hN hs hy hP heps hf
  rw [truncatedDyadicCover_eq_intRange hends.2.2.1.le hends.2.2.2.1,
    min_eq_left (derivative_upper_lt_dyadicCut hN hs hy hP heps hf).le]

/-- Exact sum decomposition of the integer derivative range into at most
`dyadicDepth s` truncated dyadic blocks. -/
theorem sum_derivative_intRange_eq_sum_truncatedDyadicBlocks
    {M : Type*} [AddCommMonoid M] (g : ℕ → M)
    {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f) :
    ∑ n ∈ intRange (deriv f b) (deriv f a), g n =
      ∑ j ∈ Finset.range (dyadicDepth s),
        ∑ n ∈ truncatedDyadicBlock (deriv f a) (deriv f b) j, g n := by
  have hends := endpoint_derivative_bounds hN hs hy hP heps hf
  rw [← derivative_truncatedDyadicCover_eq_intRange hN hs hy hP heps hf]
  exact sum_truncatedDyadicCover g hends.2.2.1.le hends.2.2.2.1 _

/-! ## Uniform input-pair and inverse-class parameters -/

/-- All parameters selected once for the B-process at a fixed exponent pair
and original exponent `s`. -/
structure Parameters (k l s : ℝ) where
  pairOrder : ℕ
  pairError : ℝ
  pairConstant : ℝ
  pairError_pos : 0 < pairError
  pairError_lt_half : pairError < 1 / 2
  pairConstant_nonneg : 0 ≤ pairConstant
  pairBound :
    ∀ (N y a b : ℝ) (f : ℝ → ℝ), 0 < N → 0 < y →
      InGKClass N pairOrder (1 / s) y pairError a b f →
      ‖∑ n ∈ intRange a b, e (f n)‖ ≤
        pairConstant *
          ((y * N ^ (-(1 / s))) ^ k * N ^ l + y⁻¹ * N ^ (1 / s))
  originalOrder : ℕ
  originalOrder_eq_max : originalOrder = max 4 pairOrder
  originalError : ℝ
  originalError_pos : 0 < originalError
  originalError_lt_half : originalError < 1 / 2
  originalError_le_quarter : originalError ≤ 1 / 4
  lemma39Constant : ℝ
  lemma39Error_le_pairError : lemma39Constant * originalError ≤ pairError
  lemma39Error_le_quarter : lemma39Constant * originalError ≤ 1 / 4
  lemma39Class :
    ∀ (N y a b : ℝ) (f x phi : ℝ → ℝ), 0 < N → 0 < y →
      InGKClass N originalOrder s y originalError a b f →
      a < b → ContDiff ℝ originalOrder phi →
      (∀ nu ∈ Icc (deriv f b) (deriv f a),
        x nu ∈ Icc a b ∧ deriv f (x nu) = nu) →
      (∀ nu ∈ Icc (deriv f b) (deriv f a),
        phi nu = nu * x nu - f (x nu)) →
      ∀ J : ℝ, deriv f b ≤ J → J ≤ deriv f a →
        InGKClass J originalOrder (1 / s) (y ^ (1 / s))
          (lemma39Constant * originalError)
          (max (deriv f b) J) (min (deriv f a) (2 * J)) phi

theorem Parameters.four_le_originalOrder
    {k l s : ℝ} (params : Parameters k l s) :
    4 ≤ params.originalOrder := by
  rw [params.originalOrder_eq_max]
  exact le_max_left _ _

theorem Parameters.pairOrder_le_originalOrder
    {k l s : ℝ} (params : Parameters k l s) :
    params.pairOrder ≤ params.originalOrder := by
  rw [params.originalOrder_eq_max]
  exact le_max_right _ _

/-- Every dyadic inverse class returned by the stored Lemma 3.9 map weakens
to exactly the order and error expected by the stored input exponent-pair
bound. -/
theorem Parameters.dualPairClass
    {k l s N y a b J : ℝ} {f x phi : ℝ → ℝ}
    (params : Parameters k l s) (hs : 0 < s)
    (hN : 0 < N) (hy : 0 < y)
    (hf : InGKClass N params.originalOrder s y params.originalError a b f)
    (hab : a < b) (hphi : ContDiff ℝ params.originalOrder phi)
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu)
    (hlegendre : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      phi nu = nu * x nu - f (x nu))
    (hJLower : deriv f b ≤ J) (hJUpper : J ≤ deriv f a) :
    InGKClass J params.pairOrder (1 / s) (y ^ (1 / s)) params.pairError
      (max (deriv f b) J) (min (deriv f a) (2 * J)) phi := by
  have hdual := params.lemma39Class N y a b f x phi hN hy hf hab hphi hx
    hlegendre J hJLower hJUpper
  have hAlpha : 0 < deriv f b :=
    (endpoint_derivative_bounds hN hs hy params.four_le_originalOrder
      params.originalError_le_quarter hf).2.2.1
  have hJ : 0 < J := hAlpha.trans_le hJLower
  have hsigma : 0 < 1 / s := by positivity
  have heta : 0 < y ^ (1 / s) := Real.rpow_pos_of_pos hy _
  exact InGKClass.weaken_of_pos hJ hsigma heta
    params.pairOrder_le_originalOrder params.lemma39Error_le_pairError hdual

/-- Existence of one coherent parameter package.  The exponent-pair constant
is replaced by its nonnegative maximum with zero, the original order is
`max 4 P0`, and the original error is `controlledError eps0 C39`. -/
theorem exists_parameters {k l s : ℝ}
    (hkl : IsExponentPair k l) (hs : 0 < s) :
    Nonempty (Parameters k l s) := by
  have hsigma : 0 < 1 / s := by positivity
  obtain ⟨P0, eps0, C0, heps0, heps0Half, hpair0⟩ :=
    hkl.2.2.2.2 (1 / s) hsigma
  let P : ℕ := max 4 P0
  have hP4 : 4 ≤ P := le_max_left _ _
  have hP2 : 2 ≤ P := by omega
  obtain ⟨C39, hC39⟩ := gk_lemma39_class_holds s P hs hP2
  let eps : ℝ := controlledError eps0 C39
  have hepsSpec := controlledError_spec (C := C39) heps0
  have heps : 0 < eps := by simpa only [eps] using hepsSpec.1
  have hepsHalf : eps < 1 / 2 := by simpa only [eps] using hepsSpec.2.1
  have hepsQuarter : eps ≤ 1 / 4 := by simpa only [eps] using hepsSpec.2.2.1
  have hC39Pair : C39 * eps ≤ eps0 := by
    simpa only [eps] using hepsSpec.2.2.2.1
  have hC39Quarter : C39 * eps ≤ 1 / 4 := by
    simpa only [eps] using hepsSpec.2.2.2.2
  let Cpair : ℝ := max C0 0
  have hCpair : 0 ≤ Cpair := le_max_right _ _
  have hpair :
      ∀ (N y a b : ℝ) (f : ℝ → ℝ), 0 < N → 0 < y →
        InGKClass N P0 (1 / s) y eps0 a b f →
        ‖∑ n ∈ intRange a b, e (f n)‖ ≤
          Cpair * ((y * N ^ (-(1 / s))) ^ k * N ^ l +
            y⁻¹ * N ^ (1 / s)) := by
    intro N y a b f hN hy hf
    have hbase :
        0 ≤ (y * N ^ (-(1 / s))) ^ k * N ^ l +
          y⁻¹ * N ^ (1 / s) := by positivity
    calc
      ‖∑ n ∈ intRange a b, e (f n)‖ ≤
          C0 * ((y * N ^ (-(1 / s))) ^ k * N ^ l +
            y⁻¹ * N ^ (1 / s)) := hpair0 N y a b f hN hy hf
      _ ≤ Cpair * ((y * N ^ (-(1 / s))) ^ k * N ^ l +
            y⁻¹ * N ^ (1 / s)) := by
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hbase
  refine ⟨{
    pairOrder := P0
    pairError := eps0
    pairConstant := Cpair
    pairError_pos := heps0
    pairError_lt_half := heps0Half
    pairConstant_nonneg := hCpair
    pairBound := hpair
    originalOrder := P
    originalOrder_eq_max := rfl
    originalError := eps
    originalError_pos := heps
    originalError_lt_half := hepsHalf
    originalError_le_quarter := hepsQuarter
    lemma39Constant := C39
    lemma39Error_le_pairError := hC39Pair
    lemma39Error_le_quarter := hC39Quarter
    lemma39Class := ?_
  }⟩
  intro N y a b f x phi hN hy hf hab hphi hx hlegendre J hJLower hJUpper
  exact hC39 N y eps a b f x phi hN hy heps hepsHalf hf hab hphi hx
    hlegendre J hJLower hJUpper

/-- A canonical, noncomputably selected parameter package for downstream use. -/
noncomputable def chooseParameters {k l s : ℝ}
    (hkl : IsExponentPair k l) (hs : 0 < s) : Parameters k l s :=
  Classical.choice (exists_parameters hkl hs)

end GKB

end LeanProofs.IntegerPoints
