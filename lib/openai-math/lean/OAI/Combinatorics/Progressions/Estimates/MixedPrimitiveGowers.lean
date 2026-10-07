import OAI.Combinatorics.Progressions.Dynamics.MixedCyclicErrorBudget
import OAI.Combinatorics.Progressions.Estimates.MixedFrozenMiddleRows
import OAI.Combinatorics.Progressions.Estimates.MixedPreciseSampledExchange
import OAI.Combinatorics.Progressions.Estimates.MixedRootCyclicComparison
import OAI.Combinatorics.Progressions.Estimates.NativeResidualCrossInduction
import OAI.Combinatorics.Progressions.Estimates.NativeSeparatedSumIntervals
import OAI.Combinatorics.Progressions.Geometry.MixedProfileCoordinates

namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_mixed_sum_pair_factors (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      {N : ℕ} [NeZero N] (f : ZMod N → ℂ), (∀ x, ‖f x‖ ≤ 1) →
      ∀ (i : Fin W.outputDim) (A : Fin (n + 2) → (Fin (n + 2) → ZMod N) → ℂ),
      (∀ j x, ‖A j x‖ ≤ 1) → (∀ j, MissesBoxCoordinate (A j) j) →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      Real.exp (-p) ≤ ‖𝔼 u : Fin n → ZMod N, 𝔼 m : ZMod N, 𝔼 h : ZMod N,
        f (m + h + ∑ j, u j) * star (W.eval i (mixedSlotInput (h.val : ℤ) m.val (fun j => (u j).val))) *
          ∏ j, A j (Fin.cons h (Fin.cons m u))‖ →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ (j k : Fin W.outputDim)
        (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
          Finset.univ (fun x : Fin (n + 2) → ZMod N => fun l => ((x l).val : ℤ))
          (fun x => W.mixedAntisymmetric j k (fun l => ((x l).val : ℤ)))),
        Nonempty (NativePolynomialOrbitFactors (pi V.mixedPairModels)
          V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
          (fun _ : Fin (n + 2) => (N : ℝ)) ((p + C) ^ C)) := by
  obtain ⟨a, _, hkernel⟩ := NativeMultidegreeNilcharacter.exists_mixed_sum_kernel_correlation n
  obtain ⟨b, _, hstep⟩ := exists_mixed_pair_step_drop n
  obtain ⟨c, _, horbit⟩ := exists_mixed_pair_orbit_factors n
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a
  let U := (X + Q + Polynomial.C b) ^ b
  let T := (X + Q + U + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + U + T)
  refine ⟨C, hC, ?_⟩
  intro p W N _ f hf i A hA hmiss hN hcorr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + a) ^ a
  let u := (p + q + b) ^ b
  let t := (p + q + u + c) ^ c
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hsum : q + u + t ≤ (p + C) ^ C := by
    simpa [X, Q, U, T, q, u, t, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hsum, hu, ht]
  have huC : u ≤ (p + C) ^ C := by linarith only [hsum, hq, ht]
  have htC : t ≤ (p + C) ^ C := by linarith only [hsum, hq, hu]
  obtain ⟨j, k, ⟨V⟩⟩ := hkernel W f hf i A hA hmiss hcorr
  obtain ⟨F⟩ := hstep (W := W) V ((Real.exp_le_exp.mpr huC).trans hN)
  obtain ⟨O⟩ := horbit (W := W) F hu ((Real.exp_le_exp.mpr htC).trans hN)
  exact ⟨q, hq, hqC, j, k, V, ⟨O.mono htC (fun _ => by exact_mod_cast NeZero.pos N)⟩⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def HasPositiveMixedTargetInterval {J : Type*} {d N : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (η : J → (Fin (d + 3) → ℤ) → ℂ) (q : ℝ) : Prop :=
  ∃ (j : J) (A : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ),
    (∀ i x, ‖A i x‖ ≤ 1) ∧
    (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
    ∃ a len : ℕ, 0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
      Real.exp (-q) ≤ (len : ℝ) / N ∧ Real.exp (-q) ≤
        (𝔼 t : (Fin (d + 1) → ZMod N) × ZMod N,
          𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
            star (f ((∑ k, mixedDifferencePoint t n k : ℤ) : ZMod N)) *
              star (η j (mixedDifferencePoint t n)) * ∏ i, A i (mixedDifferencePoint t n)).re

theorem HasCommonMixedTargetInterval.positive {J : Type*} {d N : ℕ} [NeZero N] {p q : ℝ}
    {f : ZMod N → ℂ} {M : NativeMixedCorrelation (d + 2) N p f}
    {η : J → (Fin (d + 3) → ℤ) → ℂ} (H : HasCommonMixedTargetInterval f M η q)
    (hq : 0 ≤ q) : HasPositiveMixedTargetInterval f η (2 * q) := by
  classical
  obtain ⟨j, A, hA, hAi, a, len, hlen, hend, hshort, hvol, Q, _, hdense, hcorr⟩ := H
  let row (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ℤ) :=
    star (f ((∑ k, mixedDifferencePoint t n k : ℤ) : ZMod N)) *
      star (η j (mixedDifferencePoint t n)) * ∏ i, A i (mixedDifferencePoint t n)
  have hdensity : Real.exp (-q) * Fintype.card ((Fin (d + 1) → ZMod N) × ZMod N) ≤
      (Q.card : ℝ) := by
    simpa only [mixedProfile_card, Nat.cast_pow] using hdense
  obtain ⟨w, hw, _, hpositive⟩ := exists_dense_row_phase_alignment Q
    (Finset.Ico (a : ℤ) (a + len)) row (Real.exp_nonneg (-q)) hdensity
      (fun t ht => (hcorr t ht).2)
  let phase (x : Fin (d + 3) → ℤ) :=
    w (mixedProfileFromCoordinates (fun k => (x k : ZMod N)))
  let B (i : Fin (d + 3)) (x : Fin (d + 3) → ℤ) :=
    (if i = 1 then phase x else 1) * A i x
  have hB : ∀ i x, ‖B i x‖ ≤ 1 := by
    intro i x
    by_cases hi : i = 1
    · simp only [B, hi, ite_true, norm_mul]
      exact (mul_le_mul_of_nonneg_right (hw _) (norm_nonneg _)).trans (by
        simpa only [one_mul] using hA 1 x)
    · simpa only [B, hi, ite_false, one_mul] using hA i x
  have hBi : ∀ i x y, (∀ k, k ≠ i → x k = y k) → B i x = B i y := by
    intro i x y hxy
    by_cases hi : i = 1
    · subst i
      simp only [B, ite_true]
      rw [hAi 1 x y hxy]
      congr 1
      apply congrArg w
      exact mixedProfileFromCoordinates_independent _ _ (fun k hk => congrArg (fun z : ℤ => (z : ZMod N)) (hxy k hk))
    · simpa only [B, hi, ite_false, one_mul] using hAi i x y hxy
  have hphase (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ℤ) :
      phase (mixedDifferencePoint t n) = w t := by
    exact congrArg w (mixedProfileFromCoordinates_point t n)
  have hprod (x : Fin (d + 3) → ℤ) : (∏ i, B i x) = phase x * ∏ i, A i x := by
    simp only [B, Finset.prod_mul_distrib]
    simp
  have hpoint (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ℤ) :
      star (f ((∑ k, mixedDifferencePoint t n k : ℤ) : ZMod N)) *
        star (η j (mixedDifferencePoint t n)) * ∏ i, B i (mixedDifferencePoint t n) = w t * row t n := by
    rw [hprod, hphase]
    dsimp only [row]
    ring
  refine ⟨j, B, hB, hBi, a, len, hlen, hend, hshort,
    (Real.exp_le_exp.mpr (by linarith : -(2 * q) ≤ -q)).trans hvol, ?_⟩
  have hscore : Real.exp (-(2 * q)) ≤
      (𝔼 t, 𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), w t * row t n).re := by
    have heq : Real.exp (-(2 * q)) = Real.exp (-q) * Real.exp (-q) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact hpositive
  simpa only [hpoint] using hscore

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def HasCyclicMixedTargetCorrelation {J : Type*} {d N : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (η : J → (Fin (d + 3) → ℤ) → ℂ) (q : ℝ) : Prop :=
  ∃ (j : J) (A : Fin (d + 3) → (Fin (d + 3) → ZMod N) → ℂ),
    (∀ i x, ‖A i x‖ ≤ 1) ∧
    (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
    Real.exp (-q) ≤ ‖𝔼 x : Fin (d + 3) → ZMod N,
      star (f (∑ k, x k)) * star (η j (fun k => ((x k).val : ℤ))) * ∏ i, A i x‖

theorem HasCyclicMixedTargetCorrelation.mono {J : Type*} {d N : ℕ} [NeZero N] {q q' : ℝ}
    {f : ZMod N → ℂ} {η : J → (Fin (d + 3) → ℤ) → ℂ}
    (H : HasCyclicMixedTargetCorrelation f η q) (hqq' : q ≤ q') :
    HasCyclicMixedTargetCorrelation f η q' := by
  obtain ⟨j, A, hA, hAi, hc⟩ := H
  exact ⟨j, A, hA, hAi, (Real.exp_le_exp.mpr (neg_le_neg hqq')).trans hc⟩

theorem exists_mixed_interval_cutoff_weights {d N : ℕ} [NeZero N]
    (I : Finset (ZMod N)) (A : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ)
    (hA : ∀ i x, ‖A i x‖ ≤ 1)
    (hAi : ∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) :
    ∃ B : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ,
      (∀ i x, ‖B i x‖ ≤ 1) ∧
      (∀ i x y, (∀ k, k ≠ i → x k = y k) → B i x = B i y) ∧
      (∀ x, (∏ i, B i x) = finiteIndicator I (x 1 : ZMod N) * ∏ i, A i x) := by
  classical
  let B (i : Fin (d + 3)) (x : Fin (d + 3) → ℤ) :=
    (if i = 0 then finiteIndicator I (x 1 : ZMod N) else 1) * A i x
  refine ⟨B, ?_, ?_, ?_⟩
  · intro i x
    by_cases hi : i = 0
    · simp only [B, hi, ite_true, norm_mul]
      exact (mul_le_mul_of_nonneg_right (finiteIndicator_norm_le_one I _)
        (norm_nonneg _)).trans (by simpa only [one_mul] using hA 0 x)
    · simpa only [B, hi, ite_false, one_mul] using hA i x
  · intro i x y hxy
    by_cases hi : i = 0
    · subst i
      simp only [B, ite_true]
      rw [hAi 0 x y hxy, hxy 1 (by
        intro e
        have he := congrArg Fin.val e
        norm_num only [Fin.val_one, Fin.val_zero] at he)]
    · simpa only [B, hi, ite_false, one_mul] using hAi i x y hxy
  · intro x
    simp only [B, Finset.prod_mul_distrib]
    simp

theorem mixedInterval_zeroExtension_average {d N : ℕ} [NeZero N]
    (a len : ℕ) (hend : a + len ≤ N) (hshort : 2 * ((len : ℤ) - 1) < N)
    (F : (Fin (d + 3) → ℤ) → ℂ) :
    (𝔼 x : Fin (d + 3) → ZMod N,
      finiteIndicator (cyclicInterval (a : ZMod N) len) (x 1) * F (fun k => ((x k).val : ℤ))) =
      (((len : ℝ) / N : ℝ) : ℂ) *
        (𝔼 t : (Fin (d + 1) → ZMod N) × ZMod N,
          𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), F (mixedDifferencePoint t n)) := by
  let I := cyclicInterval (a : ZMod N) len
  have hbase (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ZMod N) :
      mixedProfileEquiv d (ZMod N) (t, n) 1 = n := rfl
  have hrow (t : (Fin (d + 1) → ZMod N) × ZMod N) :
      (𝔼 n : ZMod N, finiteIndicator I (mixedProfileEquiv d (ZMod N) (t, n) 1) *
        F (fun k => ((mixedProfileEquiv d (ZMod N) (t, n) k).val : ℤ))) =
      (((len : ℝ) / N : ℝ) : ℂ) * (𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), F (mixedDifferencePoint t n)) := by
    simpa only [hbase, mixedProfileEquiv_point] using
      cyclicInterval_zeroExtension_average a len hend hshort (fun n => F (mixedDifferencePoint t n))
  rw [mixedProfile_average]
  change (𝔼 t, 𝔼 n : ZMod N, finiteIndicator I (mixedProfileEquiv d (ZMod N) (t, n) 1) *
    F (fun k => ((mixedProfileEquiv d (ZMod N) (t, n) k).val : ℤ))) = _
  simp_rw [hrow]
  rw [← Finset.mul_expect]

theorem HasPositiveMixedTargetInterval.cyclic {J : Type*} {d N : ℕ} [NeZero N] {q : ℝ}
    {f : ZMod N → ℂ} {η : J → (Fin (d + 3) → ℤ) → ℂ}
    (H : HasPositiveMixedTargetInterval f η q) : HasCyclicMixedTargetCorrelation f η (2 * q) := by
  classical
  obtain ⟨j, A, hA, hAi, a, len, _, hend, hshort, hvol, hpositive⟩ := H
  let I := cyclicInterval (a : ZMod N) len
  obtain ⟨B, hB, hBi, hprod⟩ := exists_mixed_interval_cutoff_weights I A hA hAi
  let F (x : Fin (d + 3) → ℤ) := star (f ((∑ k, x k : ℤ) : ZMod N)) * star (η j x) * ∏ i, A i x
  let R (x : Fin (d + 3) → ZMod N) :=
    star (f (∑ k, x k)) * star (η j (fun k => ((x k).val : ℤ))) * ∏ i, B i (fun k => ((x k).val : ℤ))
  have hpoint (x : Fin (d + 3) → ZMod N) :
      R x = finiteIndicator I (x 1) * F (fun k => ((x k).val : ℤ)) := by
    dsimp only [R]
    rw [hprod]
    simp only [F, Int.cast_sum, Int.cast_natCast, ZMod.natCast_zmod_val]
    ring
  have hmean : (𝔼 x, R x).re = (len : ℝ) / N *
      (𝔼 t : (Fin (d + 1) → ZMod N) × ZMod N,
        𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), F (mixedDifferencePoint t n)).re := by
    simp_rw [hpoint]
    rw [mixedInterval_zeroExtension_average a len hend hshort F]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  refine ⟨j, (fun i x => B i (fun k => ((x k).val : ℤ))), (fun i x => hB i _), ?_, ?_⟩
  · intro i x y hxy
    exact hBi i _ _ (fun k hk => congrArg (fun z : ZMod N => (z.val : ℤ)) (hxy k hk))
  · change Real.exp (-(2 * q)) ≤ ‖𝔼 x, R x‖
    apply le_trans ?_ (Complex.re_le_norm _)
    rw [hmean]
    calc
      _ = Real.exp (-q) * Real.exp (-q) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul hvol hpositive (Real.exp_nonneg _) (by positivity)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem HasCyclicMixedTargetCorrelation.mixed_sum {d N : ℕ} [NeZero N] {p q : ℝ}
    {f : ZMod N → ℂ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p)
    (H : HasCyclicMixedTargetCorrelation f
      (fun k x => W.eval k (mixedReplicatedInput (x 0) (fun j => x j.succ))) q) :
    ∃ (i : Fin W.outputDim) (A : Fin (d + 3) → (Fin (d + 3) → ZMod N) → ℂ),
      (∀ j x, ‖A j x‖ ≤ 1) ∧ (∀ j, MissesBoxCoordinate (A j) j) ∧
      Real.exp (-q) ≤ ‖𝔼 u : Fin (d + 1) → ZMod N, 𝔼 m : ZMod N, 𝔼 h : ZMod N,
        star (f (m + h + ∑ j, u j)) *
          star (W.eval i (mixedSlotInput (h.val : ℤ) m.val (fun j => (u j).val))) *
            ∏ j, A j (Fin.cons h (Fin.cons m u))‖ := by
  obtain ⟨i, A, hA, hAi, hc⟩ := H
  refine ⟨i, A, hA, ?_, ?_⟩
  · intro j x v
    apply hAi j
    intro k hkj
    exact Function.update_of_ne hkj v x
  · have hvals (m : ZMod N) (u : Fin (d + 1) → ZMod N) :
        (fun j : Fin (d + 2) => (((Fin.cons m u : Fin (d + 2) → ZMod N) j).val : ℤ)) =
          Fin.cons (m.val : ℤ) (fun j => ((u j).val : ℤ)) := by
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    have hmean :
        (𝔼 x : Fin (d + 3) → ZMod N,
          star (f (∑ k, x k)) * star (W.eval i
            (mixedReplicatedInput ((x 0).val : ℤ) (fun j => ((x j.succ).val : ℤ)))) * ∏ j, A j x) =
        𝔼 u : Fin (d + 1) → ZMod N, 𝔼 m : ZMod N, 𝔼 h : ZMod N,
          star (f (m + h + ∑ j, u j)) *
            star (W.eval i (mixedSlotInput (h.val : ℤ) m.val (fun j => (u j).val))) *
              ∏ j, A j (Fin.cons h (Fin.cons m u)) := by
      rw [expect_mixed_tuple]
      apply Finset.expect_congr rfl
      intro u _
      rw [Finset.expect_comm]
      apply Finset.expect_congr rfl
      intro m _
      apply Finset.expect_congr rfl
      intro h _
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hvals, mixedSlotInput,
        add_left_comm, add_assoc]
    exact hc.trans_eq (congrArg norm hmean)

end Erdos3

end

section

namespace Erdos3

theorem exists_retained_cyclic_sum (d : ℕ) {A : ℕ} (hI : CyclicNativeInverse (d + 2) A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) q,
        W.dim ≤ 2 ^ (d + 3) * M.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence (d + 2) q M.mixed.eval
          (fun k x => W.eval k (fun j => x j.1)) ∧
        tensorPowerBudget (d + 2).factorial q ≤ (p + C) ^ C ∧
        HasCyclicMixedTargetCorrelation f
          (fun k x => (W.tensorPower (d + 2).factorial).eval k
            (mixedReplicatedInput (x 0) (fun j => x j.succ))) ((p + C) ^ C) := by
  obtain ⟨a, _, hretained⟩ := exists_retained_sum_target_intervals d hI
  obtain ⟨b, _, hseparate⟩ := exists_separated_sum_intervals d
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  let R := (P + Polynomial.C b) ^ b
  let T := Polynomial.C ((d + 2).factorial + 1) * (P + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (P + (2 * R + 8) + 4 * (5 * R + 10) + T)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let q := (p + a) ^ a
  let r := (q + b) ^ b
  let t := ((d + 2).factorial + 1 : ℝ) * (q + 1)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htotal : q + (2 * r + 8) + 4 * (5 * r + 10) + t ≤ (p + C) ^ C := by
    simpa [X, P, R, T, q, r, t, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hgridC : 2 * r + 8 ≤ (p + C) ^ C := by linarith
  have hcorrC : 2 * (2 * (5 * r + 10)) ≤ (p + C) ^ C := by linarith
  have htC : t ≤ (p + C) ^ C := by linarith
  obtain ⟨q₀, hq₀, hq₀q, M, W, hdim, hsym, E, H⟩ :=
    hretained hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hG
  have Hsep := hseparate hq hq₀q f hf M W hsym H
  have Hcommon := Hsep.common hr ((Real.exp_le_exp.mpr hgridC).trans hN) hf
    (fun k x => (W.tensorPower (d + 2).factorial).norm_eval k _)
  refine ⟨q₀, hq₀, hq₀q.trans hqC, M, W, hdim, hsym, E, ?_,
    ((Hcommon.positive (by positivity)).cyclic).mono hcorrC⟩
  apply le_trans ?_ htC
  have hqq : q₀ ≤ q := hq₀q
  exact mul_le_mul_of_nonneg_left (by linarith only [hqq] : q₀ + 1 ≤ q + 1) (by positivity)

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_cyclic_target_pair_factors (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p),
      p ≤ q → ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((q + C) ^ C) ≤ (N : ℝ) →
      HasCyclicMixedTargetCorrelation f
        (fun k x => W.eval k (mixedReplicatedInput (x 0) (fun j => x j.succ))) q →
      ∃ u : ℝ, 0 ≤ u ∧ u ≤ (q + C) ^ C ∧
      ∃ (i j : Fin W.outputDim)
        (V : NativeSampleCorrelation (fun _ : Fin (d + 3) => 1) (d + 2) u
          Finset.univ (fun x : Fin (d + 3) → ZMod N => fun k => ((x k).val : ℤ))
          (fun x => W.mixedAntisymmetric i j (fun k => ((x k).val : ℤ)))),
        Nonempty (NativePolynomialOrbitFactors (pi V.mixedPairModels)
          V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
          (fun _ : Fin (d + 3) => (N : ℝ)) ((q + C) ^ C)) := by
  obtain ⟨C, hC, hpair⟩ := exists_mixed_sum_pair_factors (d + 1)
  refine ⟨C, hC, ?_⟩
  intro N _ p q W hpq f hf hN H
  have H' : HasCyclicMixedTargetCorrelation f
      (fun k x => (W.mono hpq).eval k (mixedReplicatedInput (x 0) (fun j => x j.succ))) q := H
  obtain ⟨i, A, hA, hmiss, hc⟩ := HasCyclicMixedTargetCorrelation.mixed_sum (W.mono hpq) H'
  obtain ⟨u, hu, huC, i', j', V, R⟩ := hpair (W.mono hpq) (fun x => star (f x))
    (fun x => by simpa only [norm_star] using hf x) i A hA hmiss hN hc
  exact ⟨u, hu, huC, i', j', V, R⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_retained_mixed_pair_factors (d : ℕ) {A : ℕ}
    (hI : CyclicNativeInverse (d + 2) A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) q,
        W.dim ≤ 2 ^ (d + 3) * M.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence (d + 2) q M.mixed.eval
          (fun k x => W.eval k (fun j => x j.1)) ∧
        tensorPowerBudget (d + 2).factorial q ≤ (p + C) ^ C ∧
        ∃ u : ℝ, 0 ≤ u ∧ u ≤ (p + C) ^ C ∧
        ∃ (i j : Fin (W.tensorPower (d + 2).factorial).outputDim)
          (V : NativeSampleCorrelation (fun _ : Fin (d + 3) => 1) (d + 2) u
            Finset.univ (fun x : Fin (d + 3) → ZMod N => fun k => ((x k).val : ℤ))
            (fun x => (W.tensorPower (d + 2).factorial).mixedAntisymmetric i j (fun k => ((x k).val : ℤ)))),
          ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
            Nonempty (NativePolynomialOrbitFactors (pi V.mixedPairModels)
              V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
              (fun _ : Fin (d + 3) => (N : ℝ)) r) := by
  obtain ⟨a, _, hcyclic⟩ := exists_retained_cyclic_sum d hI
  obtain ⟨b, _, hpair⟩ := exists_cyclic_target_pair_factors d
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  let R := (P + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + R)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let q := (p + a) ^ a
  let r := (q + b) ^ b
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hsum : q + r ≤ (p + C) ^ C := by
    simpa [X, P, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hrC : r ≤ (p + C) ^ C := by linarith
  obtain ⟨q₀, hq₀, hq₀q, M, W, hdim, hsym, E, htensor, H⟩ :=
    hcyclic hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hG
  obtain ⟨u, hu, hur, i, j, V, R⟩ := hpair (W.tensorPower (d + 2).factorial) htensor f hf
    ((Real.exp_le_exp.mpr hrC).trans hN) H
  exact ⟨q₀, hq₀, hq₀q.trans hqC, M, W, hdim, hsym, E, htensor.trans hqC,
    u, hu, hur.trans hrC, i, j, V, r, hr, hrC, R⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_retained_mixed_sampled_exchange (d : ℕ) {A : ℕ}
    (hI : CyclicNativeInverse (d + 2) A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      Real.exp ((p + e + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) q,
        W.dim ≤ 2 ^ (d + 3) * M.mixed.dim ∧
        (∀ (a : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) a).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence (d + 2) q M.mixed.eval
          (fun k x => W.eval k (fun j => x j.1)) ∧
        tensorPowerBudget (d + 2).factorial q ≤ (p + C) ^ C ∧
        ∃ u : ℝ, 0 ≤ u ∧ u ≤ (p + C) ^ C ∧
        ∃ (i j : Fin (W.tensorPower (d + 2).factorial).outputDim)
          (V : NativeSampleCorrelation (fun _ : Fin (d + 3) => 1) (d + 2) u
            Finset.univ (fun x : Fin (d + 3) → ZMod N => fun k => ((x k).val : ℤ))
            (fun x => (W.tensorPower (d + 2).factorial).mixedAntisymmetric i j (fun k => ((x k).val : ℤ)))),
          ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
          ∃ _R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
            V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
            (fun _ : Fin (d + 3) => (N : ℝ)) r,
          ∃ G : (Fin (d + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
            (∀ π a c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (d + 2)
              ((p + e + C) ^ C) (G π a c))) ∧
            (∀ π a c (x : Fin 2 → ZMod N), ‖G π a c (fun k => ((x k).val : ℤ))‖ ≤ 1) ∧
            (∀ π a c, (𝔼 x : Fin 2 → ZMod N,
              ‖W.eval a (mixedSlotInput ((x (π 0)).val : ℤ) ((x (π 1)).val : ℤ)
                  (fun l => ((x (π l.succ.succ)).val : ℤ))) *
                  star (W.eval c (mixedSlotInput ((x (π 1)).val : ℤ) ((x (π 0)).val : ℤ)
                    (fun l => ((x (π l.succ.succ)).val : ℤ)))) -
                G π a c (fun k => ((x k).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨a, _, hpair⟩ := exists_retained_mixed_pair_factors d hI
  obtain ⟨b, _, hexchange⟩ := exists_mixed_precise_sampled_exchange (d + 1)
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  let S := (3 * P + X + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + S)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hG
  classical
  let v := p + e
  let t := (p + a) ^ a
  let tmax := (v + a) ^ a
  have hv : 0 ≤ v := add_nonneg hp he
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htm : 0 ≤ tmax := by dsimp [tmax]; positivity
  have hstep : t ≤ tmax := pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) a
  have hsum : tmax + (3 * tmax + v + b) ^ b ≤ (p + e + C) ^ C := by
    simpa [X, P, S, tmax, v, Polynomial.eval₂_pow] using hbudget v hv
  have htC : t ≤ (p + C) ^ C := by
    have h := hbudget p hp
    have hn : 0 ≤ (3 * t + p + b) ^ b := by positivity
    have hh : t + (3 * t + p + b) ^ b ≤ (p + C) ^ C := by
      simpa [X, P, S, t, Polynomial.eval₂_pow] using h
    linarith
  have htmaxC : tmax ≤ (p + e + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hsC : (3 * tmax + v + b) ^ b ≤ (p + e + C) ^ C :=
    (le_add_of_nonneg_left htm).trans hsum
  obtain ⟨q, hq, hqt, M, W, hdim, hsym, E, htensor, u, hu, hut, i, j, V, r, hr, hrt, ⟨R⟩⟩ :=
    hpair hp ((Real.exp_le_exp.mpr (hstep.trans htmaxC)).trans hN) f hf hG
  let : NeZero (d + 2).factorial := ⟨Nat.ne_of_gt (Nat.factorial_pos _)⟩
  have htnonneg : 0 ≤ tensorPowerBudget (d + 2).factorial q :=
    hq.trans (tensorPowerBudget_bounds (d + 2).factorial hq).1
  have hcost : (tensorPowerBudget (d + 2).factorial q + u + r + e + b) ^ b ≤
      (p + e + C) ^ C := by
    apply le_trans _ hsC
    apply pow_le_pow_left₀ (by positivity)
    dsimp only [v]
    linarith
  obtain ⟨G, hGa, hGb, hGc⟩ := hexchange (W := W) R hr he ((Real.exp_le_exp.mpr hcost).trans hN)
  refine ⟨q, hq, hqt.trans htC, M, W, hdim, hsym, E, htensor.trans htC,
    u, hu, hut.trans htC, i, j, V, r, hr, hrt.trans htC, R, G, ?_, hGb, hGc⟩
  intro π a c
  exact ⟨(Classical.choice (hGa π a c)).mono hcost⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators NNReal

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_retained_mixed_cyclic_comparison (d : ℕ) {A : ℕ}
    (hI : CyclicNativeInverse (d + 2) A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      Real.exp ((p + e + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) q,
        W.dim ≤ 2 ^ (d + 3) * M.mixed.dim ∧
        (∀ (a : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) a).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence (d + 2) q M.mixed.eval
          (fun k x => W.eval k (fun j => x j.1)) ∧
        tensorPowerBudget (d + 2).factorial q ≤ (p + C) ^ C ∧
        ∃ u : ℝ, 0 ≤ u ∧ u ≤ (p + C) ^ C ∧
        ∃ (i j : Fin (W.tensorPower (d + 2).factorial).outputDim)
          (V : NativeSampleCorrelation (fun _ : Fin (d + 3) => 1) (d + 2) u
            Finset.univ (fun x : Fin (d + 3) → ZMod N => fun k => ((x k).val : ℤ))
            (fun x => (W.tensorPower (d + 2).factorial).mixedAntisymmetric i j (fun k => ((x k).val : ℤ)))),
          ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
          ∃ _R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
            V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
            (fun _ : Fin (d + 3) => (N : ℝ)) r,
          ∃ K : (Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) →
              (MixedNonconstantCorner d → Fin W.mixedIntegrationRoot.outputDim) → (Fin 2 → ℤ) → ℂ,
            (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (d + 2)
              ((p + e + C) ^ C) (K a b))) ∧
            (∀ a b, (𝔼 x : Fin 2 → ZMod N,
              ‖W.mixedIntegrationRoot.mixedCyclicDiagonalDerivative a x *
                  star (W.mixedIntegrationRoot.mixedCanonicalTensor b (fun k => ((x k).val : ℤ))) -
                K a b (fun k => ((x k).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨a, _, hmodel⟩ := exists_retained_mixed_sampled_exchange d hI
  obtain ⟨b, _, hroot⟩ := NativeMultidegreeNilcharacter.exists_mixedRootCyclicCorrection_expansion d
  let L := mixedCyclicErrorSlope d
  let J := mixedCyclicErrorBuffer d
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C a) ^ a
  let T := (X + Polynomial.C L * U + Polynomial.C J + Polynomial.C a) ^ a
  let S := (U + T + X + Polynomial.C J + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + T + X + Polynomial.C J + S)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hGowers
  let v := p + e
  let u := (p + a) ^ a
  let umax := (v + a) ^ a
  let accuracy := e + (L : ℝ) * u + J
  let t := (p + accuracy + a) ^ a
  let tmax := (v + (L : ℝ) * umax + J + a) ^ a
  let errorScale := e + J
  let smax := (umax + tmax + v + J + b) ^ b
  let δ : ℝ≥0 := ⟨Real.exp (-errorScale), (Real.exp_pos _).le⟩
  have hδval : (δ : ℝ) = Real.exp (-errorScale) := rfl
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have humax : 0 ≤ umax := by dsimp [umax]; positivity
  have ht : 0 ≤ t := by dsimp [t, accuracy]; positivity
  have htmax : 0 ≤ tmax := by dsimp [tmax]; positivity
  have hsmax : 0 ≤ smax := by dsimp [smax]; positivity
  have hb : 0 ≤ errorScale := by dsimp [errorScale]; positivity
  have hδ : 0 < δ := Real.exp_pos _
  have hinv : (δ : ℝ)⁻¹ ≤ Real.exp errorScale := by rw [hδval, ← Real.exp_neg, neg_neg]
  have hsum : umax + tmax + v + J + smax ≤ (p + e + C) ^ C := by
    simpa [X, U, T, S, umax, tmax, smax, v, Polynomial.eval₂_pow] using hbudget v hv
  have hum : u ≤ umax := pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) a
  have htm : t ≤ tmax := by
    apply pow_le_pow_left₀ (by dsimp [accuracy]; positivity)
    have hL := mul_le_mul_of_nonneg_left hum (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    dsimp [accuracy, v]
    linarith
  have htC : tmax ≤ (p + e + C) ^ C := by linarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
  have hsC : smax ≤ (p + e + C) ^ C := by linarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
  have hbC : errorScale ≤ (p + e + C) ^ C := by dsimp [errorScale, v] at *; linarith
  have huC : u ≤ (p + C) ^ C := by
    have hh : u + (p + (L : ℝ) * u + J + a) ^ a + p + J +
        (u + (p + (L : ℝ) * u + J + a) ^ a + p + J + b) ^ b ≤ (p + C) ^ C := by
      simpa [X, U, T, S, u, Polynomial.eval₂_pow] using hbudget p hp
    have h1 : 0 ≤ (p + (L : ℝ) * u + J + a) ^ a := by positivity
    have h2 : 0 ≤ (u + (p + (L : ℝ) * u + J + a) ^ a + p + J + b) ^ b := by positivity
    linarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
  obtain ⟨q, hq, hqu, M, W, hdim, hsymm, E, htensor, u₀, hu₀, hu₀u, i, j, V, r, hr, hru,
      R, G, hG, hcap, herr⟩ :=
    hmodel hp (by dsimp [accuracy]; positivity : 0 ≤ accuracy)
      ((Real.exp_le_exp.mpr (htm.trans htC)).trans hN) f hf hGowers
  have hqmax : q ≤ umax := hqu.trans hum
  have hcost : (q + t + errorScale + b) ^ b ≤ (p + e + C) ^ C := by
    apply le_trans _ hsC
    apply pow_le_pow_left₀ (by positivity)
    dsimp [errorScale, v]
    linarith
  have herror := mixed_cyclic_error_bound d (Nat.cast_nonneg W.outputDim) hu
    (W.output_bound.trans (Real.exp_le_exp.mpr hqu)) ((Real.exp_le_exp.mpr hbC).trans hN)
  have hexchange : ∀ π a c, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval a (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval c (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π a c (fun k => ((x k).val : ℤ))‖) ≤ Real.exp (-accuracy) := by
    intro π a c
    simp only [mixedSwapSample_input]
    simpa only [mixedSampledInput_slots] using herr π a c
  refine ⟨q, hq, hqu.trans huC, M, W, hdim, hsymm, E, htensor.trans huC,
    u₀, hu₀, hu₀u.trans huC, i, j, V, r, hr, hru.trans huC, R,
    W.mixedRootCyclicCorrection N δ G, ?_, ?_⟩
  · intro a c
    exact ⟨(Classical.choice (hroot W N δ hδ ht hb hinv hsymm G hG a c)).mono hcost⟩
  · intro a c
    apply (W.mixedRootCyclicCorrection_mean_error δ hδ G (Real.exp_nonneg _) hcap hexchange a c).trans
    simpa only [W.mixedIntegrationRoot_outputDim, Nat.cast_pow, hδval, errorScale, accuracy, L, J] using herror

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_retained_mixed_original_integration (d : ℕ) {A : ℕ}
    (hI : CyclicNativeInverse (d + 2) A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      Real.exp ((p + e + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) q,
        W.dim ≤ 2 ^ (d + 3) * M.mixed.dim ∧
        (∀ (a : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) a).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence (d + 2) q M.mixed.eval
          (fun k x => W.eval k (fun j => x j.1)) ∧
        tensorPowerBudget (d + 2).factorial q ≤ (p + C) ^ C ∧
        ∃ u : ℝ, 0 ≤ u ∧ u ≤ (p + C) ^ C ∧
        ∃ (i j : Fin (W.tensorPower (d + 2).factorial).outputDim)
          (V : NativeSampleCorrelation (fun _ : Fin (d + 3) => 1) (d + 2) u
            Finset.univ (fun x : Fin (d + 3) → ZMod N => fun k => ((x k).val : ℤ))
            (fun x => (W.tensorPower (d + 2).factorial).mixedAntisymmetric i j (fun k => ((x k).val : ℤ)))),
          ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
          ∃ _R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
            V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
            (fun _ : Fin (d + 3) => (N : ℝ)) r,
          ∃ K : (Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) →
              Fin M.mixed.outputDim → (MixedMiddleCorner d → Fin W.mixedIntegrationRoot.outputDim) →
              Fin W.mixedIntegrationRoot.outputDim → (Fin 2 → ℤ) → ℂ,
            (∀ a i b c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (d + 2)
              ((p + e + C) ^ C) (K a i b c))) ∧
            (∀ a i b c, (𝔼 x : Fin 2 → ZMod N,
              ‖W.mixedIntegrationRoot.mixedCyclicDiagonalDerivative a x *
                  (M.mixed.eval i (fun k => ((x k).val : ℤ)) *
                    (W.mixedIntegrationRoot.mixedMiddleTensor b (fun k => ((x k).val : ℤ)) *
                      W.mixedIntegrationRoot.eval c (fun _ => ((x 0).val : ℤ)))) -
                K a i b c (fun k => ((x k).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨a, _, hmodel⟩ := exists_retained_mixed_cyclic_comparison d hI
  obtain ⟨b, _, hexpansion⟩ := NativeMultidegreeNilcharacter.exists_mixedOriginalWeightCorrection_expansion d
  let L := mixedRootTensorExponent d * (d + 3)
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C a) ^ a
  let T := (X + Polynomial.C L * U + Polynomial.C a) ^ a
  let S := (U + T + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + T + S)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hGowers
  let v := p + e
  let u := (p + a) ^ a
  let umax := (v + a) ^ a
  let accuracy := e + (L : ℝ) * u
  let t := (p + accuracy + a) ^ a
  let tmax := (v + (L : ℝ) * umax + a) ^ a
  let smax := (umax + tmax + b) ^ b
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have humax : 0 ≤ umax := by dsimp [umax]; positivity
  have ht : 0 ≤ t := by dsimp [t, accuracy]; positivity
  have htmax : 0 ≤ tmax := by dsimp [tmax]; positivity
  have hsmax : 0 ≤ smax := by dsimp [smax]; positivity
  have hsum : umax + tmax + smax ≤ (p + e + C) ^ C := by
    simpa [X, U, T, S, umax, tmax, smax, v, Polynomial.eval₂_pow] using hbudget v hv
  have hum : u ≤ umax := pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) a
  have htm : t ≤ tmax := by
    apply pow_le_pow_left₀ (by dsimp [accuracy]; positivity)
    have hL := mul_le_mul_of_nonneg_left hum (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    dsimp [accuracy, v]
    linarith
  have htC : tmax ≤ (p + e + C) ^ C := by linarith
  have hsC : smax ≤ (p + e + C) ^ C := by linarith
  have huC : u ≤ (p + C) ^ C := by
    have hh : u + (p + (L : ℝ) * u + a) ^ a +
        (u + (p + (L : ℝ) * u + a) ^ a + b) ^ b ≤ (p + C) ^ C := by
      simpa [X, U, T, S, u, Polynomial.eval₂_pow] using hbudget p hp
    have h1 : 0 ≤ (p + (L : ℝ) * u + a) ^ a := by positivity
    have h2 : 0 ≤ (u + (p + (L : ℝ) * u + a) ^ a + b) ^ b := by positivity
    linarith
  obtain ⟨q, hq, hqu, M, W, hdim, hsymm, E, htensor, u₀, hu₀, hu₀u, i, j, V, r, hr, hru,
      R, K, hK, herr⟩ :=
    hmodel hp (by dsimp [accuracy]; positivity : 0 ≤ accuracy)
      ((Real.exp_le_exp.mpr (htm.trans htC)).trans hN) f hf hGowers
  have hqmax : q ≤ umax := hqu.trans hum
  have hcost : (q + t + b) ^ b ≤ (p + e + C) ^ C := by
    apply le_trans _ hsC
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hd : (W.outputDim : ℝ) ≤ Real.exp u :=
    W.output_bound.trans (Real.exp_le_exp.mpr hqu)
  have hpow : (W.outputDim : ℝ) ^ L ≤ Real.exp ((L : ℝ) * u) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hd L).trans_eq (Real.exp_nat_mul u L).symm
  have hrootDim : (W.mixedIntegrationRoot.outputDim : ℝ) ^ (d + 3) ≤ Real.exp ((L : ℝ) * u) := by
    simpa only [W.mixedIntegrationRoot_outputDim, Nat.cast_pow, ← pow_mul, L] using hpow
  have herror : (W.mixedIntegrationRoot.outputDim : ℝ) ^ (d + 3) * Real.exp (-accuracy) ≤ Real.exp (-e) := by
    calc
      _ ≤ Real.exp ((L : ℝ) * u) * Real.exp (-accuracy) :=
        mul_le_mul_of_nonneg_right hrootDim (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [accuracy]; ring
  refine ⟨q, hq, hqu.trans huC, M, W, hdim, hsymm, E, htensor.trans huC,
    u₀, hu₀, hu₀u.trans huC, i, j, V, r, hr, hru.trans huC, R,
    (fun a i b c => M.mixed.mixedOriginalWeightCorrection W K a i (mixedSplitHigherMerge b c)), ?_, ?_⟩
  · intro a i b c
    exact ⟨(Classical.choice (hexpansion M.mixed W ht E K hK a i (mixedSplitHigherMerge b c))).mono hcost⟩
  · intro a i b c
    have H := M.mixed.mixedOriginalWeightCorrection_mean_error W K
      (fun a (x : Fin 2 → ZMod N) => W.mixedIntegrationRoot.mixedCyclicDiagonalDerivative a x)
      herr a i (mixedSplitHigherMerge b c)
    simpa only [NativeMultidegreeNilcharacter.mixedHigherTensor_split] using H.trans herror

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def mixedRowCoordinateCount (s : ℕ) : ℕ := Fintype.card (MixedMiddleCorner s) + 3

theorem mixedRowIndex_card (s D : ℕ) :
    (Fintype.card (((Fin D × Fin D) × (MixedMiddleCorner s → Fin D)) × Fin D) : ℝ) =
      (D : ℝ) ^ mixedRowCoordinateCount s := by
  simp only [mixedRowCoordinateCount, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_pow, pow_add]
  ring

namespace NativeMultidegreeNilcharacter

open scoped BigOperators

theorem mixed_original_row_correlation_bound {s : ℕ} {p ε : ℝ} {N : ℕ} [NeZero N]
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (s + 2)) p)
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)
    (i : Fin M.outputDim) (row : ZMod N → ZMod N → ℂ)
    (hrow : ∀ h n, ‖row h n‖ ≤ 1)
    (K : (Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) →
      (MixedMiddleCorner s → Fin W.mixedIntegrationRoot.outputDim) → Fin W.mixedIntegrationRoot.outputDim → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b c, (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedIntegrationRoot.mixedCyclicDiagonalDerivative a x *
          (M.eval i (fun k => ((x k).val : ℤ)) *
            (W.mixedIntegrationRoot.mixedMiddleTensor b (fun k => ((x k).val : ℤ)) *
              W.mixedIntegrationRoot.eval c (fun _ => ((x 0).val : ℤ)))) -
        K a b c (fun k => ((x k).val : ℤ))‖) ≤ ε) :
    (𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
      row h n * star (M.evalCyclic N i (correlationInput h n))‖) ≤
      (∑ abc : ((Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) ×
          (MixedMiddleCorner s → Fin W.mixedIntegrationRoot.outputDim)) × Fin W.mixedIntegrationRoot.outputDim,
        𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
          row h n *
            (W.mixedIntegrationRoot.mixedCyclicDiagonalDerivative abc.1.1 ![h, n] *
              W.mixedIntegrationRoot.mixedMiddleTensor abc.1.2 ![(h.val : ℤ), (n.val : ℤ)]) *
                star (K abc.1.1 abc.1.2 abc.2 ![(h.val : ℤ), (n.val : ℤ)])‖) +
          (W.mixedIntegrationRoot.outputDim : ℝ) ^ mixedRowCoordinateCount s * ε := by
  let R := W.mixedIntegrationRoot
  let I := (Fin R.outputDim × Fin R.outputDim) × (MixedMiddleCorner s → Fin R.outputDim)
  have hinput (h n : ZMod N) : (fun k => ((![h, n] k).val : ℤ)) = ![(h.val : ℤ), (n.val : ℤ)] := by
    funext k
    fin_cases k <;> rfl
  have heval (h n : ZMod N) : M.evalCyclic N i (correlationInput h n) =
      M.eval i ![(h.val : ℤ), (n.val : ℤ)] := by
    unfold evalCyclic
    congr 1
    funext k
    fin_cases k <;> rfl
  have hunit (h n : ZMod N) : ∑ ab : I,
      ‖R.mixedCyclicDiagonalDerivative ab.1 ![h, n] *
        R.mixedMiddleTensor ab.2 ![(h.val : ℤ), (n.val : ℤ)]‖ ^ 2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [norm_mul, mul_pow, ← Finset.mul_sum, R.mixedMiddleTensor_unit, mul_one]
    exact R.mixedCyclicDiagonalDerivative_unit _
  have hh := unit_row_correlation_bound row
    (fun h n => M.eval i ![(h.val : ℤ), (n.val : ℤ)])
    (fun ab : I => fun h n => R.mixedCyclicDiagonalDerivative ab.1 ![h, n] *
      R.mixedMiddleTensor ab.2 ![(h.val : ℤ), (n.val : ℤ)])
    (fun c h => R.eval c (fun _ => (h.val : ℤ)))
    (fun ab c h n => K ab.1 ab.2 c ![(h.val : ℤ), (n.val : ℤ)]) hrow hunit
    (fun h => R.unit_eval _) (fun ab h n => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (R.mixedCyclicDiagonalDerivative_norm _ _)
        (norm_nonneg _)).trans (by
          simpa only [one_mul] using R.mixedMiddleTensor_norm _ _))
      (fun c h => R.norm_eval _ _) (ε := ε) (by
      intro ab c
      have he := herr ab.1 ab.2 c
      rw [expect_fin_two] at he
      simpa only [hinput, Matrix.cons_val_zero, mul_assoc, mul_comm, mul_left_comm] using he)
  have hcard : (Fintype.card (I × Fin R.outputDim) : ℝ) =
      (R.outputDim : ℝ) ^ mixedRowCoordinateCount s := mixedRowIndex_card s R.outputDim
  simpa only [heval, hcard] using hh

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {d : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p)

noncomputable def mixedPrimitiveFactor {N : ℕ} [NeZero N] (f : ZMod N → ℂ)
    (i : Fin W.outputDim) (n : ZMod N) : ℂ :=
  f n * W.eval i (fun _ => (n.val : ℤ))

theorem mixedPrimitiveFactor_norm {N : ℕ} [NeZero N] (f : ZMod N → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (i : Fin W.outputDim) (n : ZMod N) :
    ‖W.mixedPrimitiveFactor f i n‖ ≤ 1 := by
  rw [mixedPrimitiveFactor, norm_mul]
  exact (mul_le_mul_of_nonneg_right (hf n) (norm_nonneg _)).trans (by
    simpa only [one_mul] using W.norm_eval _ _)

theorem mixedPrimitiveFactor_cross {N : ℕ} [NeZero N] (f : ZMod N → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim) (h n : ZMod N) :
    multiplicativeDerivative f h n * W.mixedCyclicDiagonalDerivative a ![h, n] =
      W.mixedPrimitiveFactor f a.1 n * star (W.mixedPrimitiveFactor f a.2 (n + h)) := by
  simp only [multiplicativeDerivative, mixedCyclicDiagonalDerivative, mixedPrimitiveFactor,
    Matrix.cons_val_zero, Matrix.cons_val_one, star_mul]
  rw [add_comm h n]
  ring

end NativeMultidegreeNilcharacter

namespace NativeMixedCorrelation

variable {d : ℕ} {m p : ℝ} {N : ℕ} [NeZero N] {f : ZMod N → ℂ}
  (M : NativeMixedCorrelation (d + 2) N m f)
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p)

noncomputable def mixedPrimitiveRow (a : Fin W.outputDim × Fin W.outputDim)
    (b : (MixedMiddleCorner d → Fin W.outputDim)) (h n : ZMod N) : ℂ :=
  (W.mixedPrimitiveFactor f a.1 n * star (W.mixedPrimitiveFactor f a.2 (n + h))) *
    W.mixedMiddleTensor b ![(h.val : ℤ), (n.val : ℤ)] *
      star (M.residualMultiplier h (fun _ => (n.val : ℤ)))

theorem mixedPrimitiveRow_eq (a : Fin W.outputDim × Fin W.outputDim)
    (b : (MixedMiddleCorner d → Fin W.outputDim)) (h n : ZMod N) :
    M.mixedPrimitiveRow W a b h n = M.normalizedResidualRow h n *
      (W.mixedCyclicDiagonalDerivative a ![h, n] *
        W.mixedMiddleTensor b ![(h.val : ℤ), (n.val : ℤ)]) := by
  rw [mixedPrimitiveRow, M.normalizedResidualRow_factor, ← W.mixedPrimitiveFactor_cross f a h n]
  ring

theorem mixedPrimitiveRow_norm (hf : ∀ n, ‖f n‖ ≤ 1)
    (a : Fin W.outputDim × Fin W.outputDim) (b : (MixedMiddleCorner d → Fin W.outputDim))
    (h n : ZMod N) : ‖M.mixedPrimitiveRow W a b h n‖ ≤ 1 := by
  rw [M.mixedPrimitiveRow_eq, norm_mul]
  refine (mul_le_mul_of_nonneg_right (M.normalizedResidualRow_norm hf h n)
    (norm_nonneg _)).trans ?_
  rw [one_mul, norm_mul]
  exact (mul_le_mul_of_nonneg_right (W.mixedCyclicDiagonalDerivative_norm _ _)
    (norm_nonneg _)).trans (by
      simpa only [one_mul] using W.mixedMiddleTensor_norm _ _)

end NativeMixedCorrelation

theorem exists_mixed_primitive_rows (d : ℕ) {I : ℕ} (hI : CyclicNativeInverse (d + 2) I) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) q,
      ∃ a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim,
      ∃ b : (MixedMiddleCorner d → Fin W.mixedIntegrationRoot.outputDim),
        Nonempty (NativeMeanRowCorrelation (fun _ : Fin 2 => 1) (d + 2) ((p + C) ^ C)
          (fun h n : ZMod N => ![(h.val : ℤ), (n.val : ℤ)])
          (M.mixedPrimitiveRow W.mixedIntegrationRoot a b)) := by
  obtain ⟨A, _, hintegrate⟩ := exists_retained_mixed_original_integration d hI
  let L := mixedRowCoordinateCount d
  let B0 := mixedRootTensorExponent d + 1
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let R := Polynomial.C B0 * (U + 1)
  let E := 4 * U + Polynomial.C L * R + 4
  let T := (X + E + Polynomial.C A) ^ A
  let V := 4 * U + 2 + Polynomial.C L * R + T
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + R + E + T + V)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let u := (p + A) ^ A
  let r := (B0 : ℝ) * (u + 1)
  let e := 4 * u + (L : ℝ) * r + 4
  let t := (p + e + A) ^ A
  let v := 4 * u + 2 + (L : ℝ) * r + t
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hsum : u + r + e + t + v ≤ (p + C) ^ C := by
    simpa [X, U, R, E, T, V, u, r, e, t, v, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := by linarith
  have huC : u ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  obtain ⟨q, hq, hqu, M, W, hdim, hsymm, E, htensor, u0, hu0, hu0u,
    i, j, Vpair, rpair, hrpair, hrbound, R, K, hK, herr⟩ :=
    hintegrate hp he ((Real.exp_le_exp.mpr htC).trans hN) f hf hGowers
  obtain ⟨out, H, hHM, hH, hdense, hcorr⟩ := M.exists_fixed_normalized_residual_coordinate
  let B := W.mixedIntegrationRoot
  have hroot : tensorPowerBudget (mixedRootTensorExponent d) q ≤ r := by
    dsimp [tensorPowerBudget, r, B0]
    push_cast
    exact mul_le_mul_of_nonneg_left (show q + 1 ≤ u + 1 by dsimp [u]; linarith) (by positivity)
  have hD : (B.outputDim : ℝ) ≤ Real.exp r :=
    B.output_bound.trans (Real.exp_le_exp.mpr hroot)
  have hDL : (B.outputDim : ℝ) ^ L ≤ Real.exp ((L : ℝ) * r) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hD L).trans_eq (Real.exp_nat_mul r L).symm
  let J := ((Fin B.outputDim × Fin B.outputDim) × (MixedMiddleCorner d → Fin B.outputDim)) × Fin B.outputDim
  let z (abc : J) := 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
    M.normalizedResidualRow h n *
      (B.mixedCyclicDiagonalDerivative abc.1.1 ![h, n] *
        B.mixedMiddleTensor abc.1.2 ![(h.val : ℤ), (n.val : ℤ)]) *
          star (K abc.1.1 out abc.1.2 abc.2 ![(h.val : ℤ), (n.val : ℤ)])‖
  have hcard : (Fintype.card J : ℝ) ≤ Real.exp ((L : ℝ) * r) := by
    have hc : (Fintype.card J : ℝ) = (B.outputDim : ℝ) ^ L := mixedRowIndex_card d B.outputDim
    rw [hc]
    exact hDL
  have hmass : Real.exp (-(4 * u)) ≤ 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
      M.normalizedResidualRow h n * star (M.mixed.evalCyclic N out (correlationInput h n))‖ := by
    have hh := dense_set_mean_lower_bound H _ (fun _ => norm_nonneg _)
      (Real.exp_nonneg (-(2 * q))) (by simpa only [ZMod.card] using hdense) hcorr
    have heq : Real.exp (-(2 * q)) * Real.exp (-(2 * q)) = Real.exp (-(4 * q)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [heq] at hh
    exact (Real.exp_le_exp.mpr (by linarith)).trans hh
  have htransfer := M.mixed.mixed_original_row_correlation_bound W out
    M.normalizedResidualRow (M.normalizedResidualRow_norm hf)
    (fun a b c => K a out b c) (fun a b c => herr a out b c)
  change _ ≤ (∑ abc : J, z abc) + (B.outputDim : ℝ) ^ L * Real.exp (-e) at htransfer
  let δ := Real.exp (-(4 * u + 2))
  have hδ : 0 < δ := Real.exp_pos _
  have herror : (B.outputDim : ℝ) ^ L * Real.exp (-e) ≤ δ := by
    calc
      _ ≤ Real.exp ((L : ℝ) * r) * Real.exp (-e) :=
        mul_le_mul_of_nonneg_right hDL (Real.exp_nonneg _)
      _ = Real.exp (-(4 * u + 4)) := by rw [← Real.exp_add]; congr 1; dsimp [e]; ring
      _ ≤ δ := Real.exp_le_exp.mpr (by linarith)
  have htwo : 2 * δ ≤ Real.exp (-(4 * u)) := by
    calc
      _ ≤ Real.exp 2 * δ := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) hδ.le
      _ = _ := by dsimp [δ]; rw [← Real.exp_add]; congr 1; ring
  have hmass' : δ ≤ ∑ abc : J, z abc := by linarith
  obtain ⟨abc, habc⟩ := exists_large_nonnegative_weighted_term (fun _ : J => (1 : ℝ)) z
    (fun _ => by norm_num) (fun _ => Finset.expect_nonneg (fun _ _ => norm_nonneg _))
    hδ (Real.exp_pos _) (by simpa using hcard) (by simpa only [one_mul] using hmass')
  have habc' : Real.exp (-(4 * u + 2 + (L : ℝ) * r)) ≤ z abc := by
    have heq : δ / Real.exp ((L : ℝ) * r) = Real.exp (-(4 * u + 2 + (L : ℝ) * r)) := by
      dsimp [δ]; rw [← Real.exp_sub]; congr 1; ring
    rwa [heq] at habc
  let expansion := Classical.choice (hK abc.1.1 out abc.1.2 abc.2)
  obtain ⟨P⟩ := NativeMeanRowCorrelation.exists_of_expansion expansion
    (by positivity : 0 ≤ 4 * u + 2 + (L : ℝ) * r) habc'
  have heq : (fun h n : ZMod N => M.normalizedResidualRow h n *
      (B.mixedCyclicDiagonalDerivative abc.1.1 ![h, n] *
        B.mixedMiddleTensor abc.1.2 ![(h.val : ℤ), (n.val : ℤ)])) =
      M.mixedPrimitiveRow B abc.1.1 abc.1.2 := by
    funext h n
    exact (M.mixedPrimitiveRow_eq B abc.1.1 abc.1.2 h n).symm
  refine ⟨q, hq, hqu.trans huC, M, W, abc.1.1, abc.1.2, ?_⟩
  exact ⟨heq ▸ P.mono hvC⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMixedCorrelation

variable {d : ℕ} {m p : ℝ} {N : ℕ} [NeZero N] {f : ZMod N → ℂ}
  (M : NativeMixedCorrelation (d + 2) N m f)
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p)

noncomputable def mixedResidualRowFactor (b : (MixedMiddleCorner d → Fin W.outputDim))
    (h : ZMod N) (x : Unit → ℤ) : ℂ :=
  M.residualMultiplier h x * star (W.mixedMiddleTensor b ![(h.val : ℤ), x ()])

theorem mixedResidualRowFactor_norm (b : (MixedMiddleCorner d → Fin W.outputDim))
    (h : ZMod N) (x : Unit → ℤ) : ‖M.mixedResidualRowFactor W b h x‖ ≤ 1 := by
  rw [mixedResidualRowFactor, norm_mul, norm_star]
  exact (mul_le_mul_of_nonneg_right (M.residualMultiplier_norm h x)
    (norm_nonneg _)).trans (by
      simpa only [one_mul] using W.mixedMiddleTensor_norm _ _)

theorem mixedPrimitiveRow_cross_residual (a : Fin W.outputDim × Fin W.outputDim)
    (b : (MixedMiddleCorner d → Fin W.outputDim)) (h n : ZMod N) :
    M.mixedPrimitiveRow W a b h n =
      (W.mixedPrimitiveFactor f a.1 n * star (W.mixedPrimitiveFactor f a.2 (n + h))) *
        star (M.mixedResidualRowFactor W b h (fun _ => (n.val : ℤ))) := by
  simp only [mixedPrimitiveRow, mixedResidualRowFactor, star_mul, star_star]
  ring

theorem exists_mixedResidualRowFactor_expansion (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {m p : ℝ} {N : ℕ} [NeZero N] {f : ZMod N → ℂ}
      (M : NativeMixedCorrelation (d + 2) N m f)
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p)
      (b : (MixedMiddleCorner d → Fin W.outputDim)) (h : ZMod N),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (d + 1) ((m + p + C) ^ C)
        (M.mixedResidualRowFactor W b h)) := by
  obtain ⟨A, _, hmiddle⟩ := NativeMultidegreeNilcharacter.exists_mixedMiddleTensor_row_expansion d
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro m p N _ f M W b h
  have hm : 0 ≤ m := (Nat.cast_nonneg M.mixed.dim).trans M.mixed.complexity.1.1
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let t := m + p + (m + p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hmt : m ≤ t := by
    have hpow : 0 ≤ (m + p + A) ^ A := by positivity
    dsimp [t]
    linarith
  have hAt : (p + A) ^ A ≤ t := by
    apply (pow_le_pow_left₀ (by positivity) (show p + A ≤ m + p + A by linarith) A).trans
    exact le_add_of_nonneg_left (add_nonneg hm hp)
  obtain ⟨F⟩ := hmul ht ((Classical.choice (M.residualMultiplier_expansion h)).mono hmt)
    ((Classical.choice (hmiddle W h.val b)).conjugate.mono hAt)
  have hcost : (t + B) ^ B ≤ (m + p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget (m + p) (add_nonneg hm hp)
  exact ⟨F.mono hcost⟩

end NativeMixedCorrelation

theorem exists_mixed_residual_cross_rows (d : ℕ) {I : ℕ} (hI : CyclicNativeInverse (d + 2) I) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) q,
      ∃ a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim,
      ∃ b : (MixedMiddleCorner d → Fin W.mixedIntegrationRoot.outputDim),
        Nonempty (NativeMeanRowCorrelation (fun _ : Fin 2 => 1) (d + 2) ((p + C) ^ C)
          (fun h n : ZMod N => ![(h.val : ℤ), (n.val : ℤ)])
          (fun h n =>
            (W.mixedIntegrationRoot.mixedPrimitiveFactor f a.1 n *
              star (W.mixedIntegrationRoot.mixedPrimitiveFactor f a.2 (n + h))) *
                star (M.mixedResidualRowFactor W.mixedIntegrationRoot b h (fun _ => (n.val : ℤ))))) ∧
        (∀ h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (d + 1) ((p + C) ^ C)
          (M.mixedResidualRowFactor W.mixedIntegrationRoot b h))) ∧
        (∀ h x, ‖M.mixedResidualRowFactor W.mixedIntegrationRoot b h x‖ ≤ 1) := by
  obtain ⟨A, _, hrows⟩ := exists_mixed_primitive_rows d hI
  obtain ⟨B, _, hfactor⟩ := NativeMixedCorrelation.exists_mixedResidualRowFactor_expansion d
  let n := mixedRootTensorExponent d
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + (Polynomial.C (n + 2) * (U + 1) + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let u := (p + A) ^ A
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hsum : u + (((n : ℝ) + 2) * (u + 1) + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, U, u, Polynomial.eval₂_pow] using hbudget p hp
  have huC : u ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  obtain ⟨q, hq, hqu, M, W, a, b, ⟨V⟩⟩ :=
    hrows hp ((Real.exp_le_exp.mpr huC).trans hN) f hf hGowers
  have hcost : (q + tensorPowerBudget (mixedRootTensorExponent d) q + B) ^ B ≤ (p + C) ^ C := by
    apply le_trans _ ((le_add_of_nonneg_left hu).trans hsum)
    apply pow_le_pow_left₀ (by unfold tensorPowerBudget; positivity)
    simp only [tensorPowerBudget]
    have hm := mul_le_mul_of_nonneg_left (show q + 1 ≤ u + 1 by dsimp [u]; linarith)
      (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)
    change q + ((n : ℝ) + 1) * (q + 1) + B ≤ ((n : ℝ) + 2) * (u + 1) + B
    nlinarith
  have heq : M.mixedPrimitiveRow W.mixedIntegrationRoot a b =
      (fun h n =>
        (W.mixedIntegrationRoot.mixedPrimitiveFactor f a.1 n *
          star (W.mixedIntegrationRoot.mixedPrimitiveFactor f a.2 (n + h))) *
            star (M.mixedResidualRowFactor W.mixedIntegrationRoot b h (fun _ => (n.val : ℤ)))) := by
    funext h n
    exact M.mixedPrimitiveRow_cross_residual W.mixedIntegrationRoot a b h n
  refine ⟨q, hq, hqu.trans huC, M, W, a, b, ⟨heq ▸ V.mono huC⟩, ?_, ?_⟩
  · intro h
    exact ⟨(Classical.choice (hfactor M W.mixedIntegrationRoot b h)).mono hcost⟩
  · intro h x
    exact M.mixedResidualRowFactor_norm W.mixedIntegrationRoot b h x

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeMeanRowCorrelation.lie NativeMeanRowCorrelation.algebra
  NativeMeanRowCorrelation.topology NativeMeanRowCorrelation.topologicalAdd
  NativeMeanRowCorrelation.continuousSMul NativeMeanRowCorrelation.hausdorff

theorem exists_mixed_primitive_gowers (d : ℕ) {I : ℕ} (hI : CyclicNativeInverse (d + 2) I) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
        ∃ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) q,
        ∃ i : Fin W.outputDim,
          Real.exp (-((p + C) ^ C)) ≤ gowersNorm (d + 3) (W.mixedPrimitiveFactor f i) := by
  obtain ⟨A, _, hrows⟩ := exists_mixed_residual_cross_rows d hI
  obtain ⟨B, _, hcross⟩ := RationalFilteredNilmanifold.exists_gowers_of_residual_cross_rows (d + 2) (by omega)
  let n := mixedRootTensorExponent d
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + Polynomial.C (n + 1) * (U + 1) + (U + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let u := (p + A) ^ A
  let v := (u + B) ^ B
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have htotal : u + ((n : ℝ) + 1) * (u + 1) + v ≤ (p + C) ^ C := by
    simpa [X, U, u, v, Polynomial.eval₂_pow] using hbudget p hp
  have hr : 0 ≤ ((n : ℝ) + 1) * (u + 1) := by positivity
  have huC : u ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  obtain ⟨q, hq, hqu, M, W, a, b, ⟨V⟩, hR, hRnorm⟩ :=
    hrows hp ((Real.exp_le_exp.mpr huC).trans hN) f hf hGowers
  have hc := hcross V.model V.test hu V.complexity
    ((Real.exp_le_exp.mpr hvC).trans hN)
    (W.mixedIntegrationRoot.mixedPrimitiveFactor f a.1) (W.mixedIntegrationRoot.mixedPrimitiveFactor f a.2)
    (M.mixedResidualRowFactor W.mixedIntegrationRoot b)
    (W.mixedIntegrationRoot.mixedPrimitiveFactor_norm f hf a.1)
    (W.mixedIntegrationRoot.mixedPrimitiveFactor_norm f hf a.2)
    (fun h n => hRnorm h (fun _ => (n.val : ℤ))) hR V.correlation
  have hroot : 0 ≤ tensorPowerBudget (mixedRootTensorExponent d) q := by unfold tensorPowerBudget; positivity
  have hrootC : tensorPowerBudget (mixedRootTensorExponent d) q ≤ (p + C) ^ C := by
    have hm := mul_le_mul_of_nonneg_left (show q + 1 ≤ u + 1 by dsimp [u]; linarith)
      (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)
    change ((n : ℝ) + 1) * (q + 1) ≤ (p + C) ^ C
    linarith
  exact ⟨tensorPowerBudget (mixedRootTensorExponent d) q, hroot, hrootC, W.mixedIntegrationRoot, a.2,
    (Real.exp_le_exp.mpr (neg_le_neg hvC)).trans hc⟩

end Erdos3

end

end OAI
