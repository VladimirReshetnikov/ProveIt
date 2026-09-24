import Surreal.Foundations.OmnificDivision
import Surreal.Foundations.OmnificRealScaling
import Surreal.Foundations.OmnificConstantRigidity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.OrderIsoNat

/-!
# A nonterminating ordered-division sequence

The example `odg:ex:euclid`, generalized from omega to any positive purely
infinite omnific integer. Starting with sqrt(2) times that integer and the
integer itself, the first quotient is one and every later quotient is two.
All remainders stay positive and infinite at every ordinary finite stage.
-/

universe u
namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The real contraction factor in the nonterminating Euclidean example. -/
def omnificEuclideanRatio : ℝ := Real.sqrt 2 - 1

/-- The contraction is positive, strictly below one, and satisfies the recurrence identity. -/
theorem omnificEuclideanRatio_spec :
    0 < omnificEuclideanRatio ∧ omnificEuclideanRatio < 1 ∧
      1 = 2 * omnificEuclideanRatio + omnificEuclideanRatio ^ 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  unfold omnificEuclideanRatio
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The source remainder sequence: the first term is sqrt(2)t, then rho^n t. -/
def omnificEuclideanSequence (t : OmnificInteger.{u})
    (ht : t ∈ omnificPurelyInfiniteIdeal) : ℕ → OmnificInteger.{u}
  | 0 => omnificRealScale (Real.sqrt 2) t ht
  | n + 1 => omnificRealScale (omnificEuclideanRatio ^ n) t ht

/-- Every term remains purely infinite. -/
theorem omnificEuclideanSequence_mem (t : OmnificInteger.{u})
    (ht : t ∈ omnificPurelyInfiniteIdeal) (n : ℕ) :
    omnificEuclideanSequence t ht n ∈ omnificPurelyInfiniteIdeal := by
  cases n <;> exact omnificRealScale_mem_purelyInfinite _ t ht

/-- Every term is positive when the initial scale is positive. -/
theorem omnificEuclideanSequence_pos (t : OmnificInteger.{u})
    (ht : t ∈ omnificPurelyInfiniteIdeal) (hp : 0 < t) (n : ℕ) :
    0 < omnificEuclideanSequence t ht n := by
  have hreal (r : ℝ) (hr : 0 < r) : 0 < omnificRealScale r t ht := by
    change 0 < ofReal r * omnificToSurreal t
    exact mul_pos (by simpa only [map_zero] using ofReal_strictMono hr) hp
  cases n with
  | zero => exact hreal _ (Real.sqrt_pos.mpr (by norm_num))
  | succ n => exact hreal _ (pow_pos omnificEuclideanRatio_spec.1 _)

/-- The geometric tail strictly decreases at every ordinary step. -/
theorem omnificEuclideanSequence_tail_lt (t : OmnificInteger.{u})
    (ht : t ∈ omnificPurelyInfiniteIdeal) (hp : 0 < t) (n : ℕ) :
    omnificEuclideanSequence t ht (n + 2) < omnificEuclideanSequence t ht (n + 1) := by
  apply omnificToSurreal_strictMono.lt_iff_lt.mp
  simp only [omnificEuclideanSequence, omnificToSurreal_realScale]
  have hp' : 0 < omnificToSurreal t := hp
  apply mul_lt_mul_of_pos_right _ hp'
  apply ofReal_strictMono
  rw [pow_succ]
  exact mul_lt_of_lt_one_right (pow_pos omnificEuclideanRatio_spec.1 _)
    omnificEuclideanRatio_spec.2.1

/-- The first step has quotient one. -/
theorem omnificEuclideanSequence_first (t : OmnificInteger.{u})
    (ht : t ∈ omnificPurelyInfiniteIdeal) :
    omnificEuclideanSequence t ht 0 =
      omnificEuclideanSequence t ht 1 + omnificEuclideanSequence t ht 2 := by
  apply omnificToSurreal_injective
  simp only [omnificEuclideanSequence, omnificToSurreal_realScale, pow_zero, pow_one,
    map_one, map_add, omnificEuclideanRatio, map_sub]
  ring

/-- Every subsequent division identity has quotient two. -/
theorem omnificEuclideanSequence_recurrence (t : OmnificInteger.{u})
    (ht : t ∈ omnificPurelyInfiniteIdeal) (n : ℕ) :
    omnificEuclideanSequence t ht (n + 1) =
      omnificEuclideanSequence t ht (n + 2) * 2 +
        omnificEuclideanSequence t ht (n + 3) := by
  have hr : omnificEuclideanRatio ^ n =
      omnificEuclideanRatio ^ (n + 1) * 2 + omnificEuclideanRatio ^ (n + 2) := by
    calc
      _ = omnificEuclideanRatio ^ n * 1 := by ring
      _ = omnificEuclideanRatio ^ n *
          (2 * omnificEuclideanRatio + omnificEuclideanRatio ^ 2) :=
        congrArg (omnificEuclideanRatio ^ n * ·) omnificEuclideanRatio_spec.2.2
      _ = _ := by ring
  apply omnificToSurreal_injective
  simp only [omnificEuclideanSequence, map_add, map_mul, omnificToSurreal_realScale,
    map_ofNat]
  have h := congrArg (fun r : ℝ => ofReal r * omnificToSurreal t) hr
  simp only [map_add, map_mul, map_ofNat, add_mul] at h
  convert h using 1
  ring

/-- The actual ordered quotient and remainder agree with every step of the source sequence. -/
theorem omnificEuclideanSequence_division (t : OmnificInteger.{u})
    (ht : t ∈ omnificPurelyInfiniteIdeal) (hp : 0 < t) (n : ℕ) :
    omnificQuotient (omnificEuclideanSequence t ht n)
      (omnificEuclideanSequence t ht (n + 1)) = (if n = 0 then 1 else 2) ∧
    omnificRemainder (omnificEuclideanSequence t ht n)
      (omnificEuclideanSequence t ht (n + 1)) = omnificEuclideanSequence t ht (n + 2) := by
  have hb := omnificEuclideanSequence_pos t ht hp (n + 1)
  have hr := (omnificEuclideanSequence_pos t ht hp (n + 2)).le
  have hl := omnificEuclideanSequence_tail_lt t ht hp n
  have he : omnificEuclideanSequence t ht n =
      omnificEuclideanSequence t ht (n + 1) * (if n = 0 then 1 else 2) +
        omnificEuclideanSequence t ht (n + 2) := by
    cases n with
    | zero => simpa only [ite_true, _root_.mul_one] using omnificEuclideanSequence_first t ht
    | succ n => simpa only [Nat.succ_ne_zero, if_false] using
        omnificEuclideanSequence_recurrence t ht n
  obtain ⟨hq, hr⟩ := omnific_division_unique _ _ _ _ hb he ⟨hr, hl⟩
  exact ⟨hq.symm, hr.symm⟩

/-- No finite stage of the ordered-division sequence has a zero or finite remainder. -/
theorem omnificEuclideanSequence_ne_zero_not_finite (t : OmnificInteger.{u})
    (ht : t ∈ omnificPurelyInfiniteIdeal) (hp : 0 < t) (n : ℕ) :
    omnificEuclideanSequence t ht n ≠ 0 ∧
      ¬ IsFinite (omnificToSurreal (omnificEuclideanSequence t ht n)) := by
  have hn := ne_of_gt (omnificEuclideanSequence_pos t ht hp n)
  exact ⟨hn, omnific_purelyInfinite_not_finite _ (omnificEuclideanSequence_mem t ht n) hn⟩

/-- The report's sequence starting with sqrt(2) omega and omega. -/
def omnificOmegaEuclideanSequence : ℕ → OmnificInteger.{u} :=
  omnificEuclideanSequence (omnificMonomial 1 zero_lt_one)
    (omnificMonomial_mem_purelyInfinite 1 zero_lt_one)

/-- The specialized sequence has exactly the normal-form values stated in the report. -/
theorem omnificOmegaEuclideanSequence_values :
    omnificToSurreal (omnificOmegaEuclideanSequence 0 : OmnificInteger.{u}) =
      ofReal (Real.sqrt 2) * omegaPower 1 ∧
    ∀ n, omnificToSurreal (omnificOmegaEuclideanSequence (n + 1) : OmnificInteger.{u}) =
      ofReal (omnificEuclideanRatio ^ n) * omegaPower 1 := by
  exact ⟨rfl, fun _ => rfl⟩

/-- The source sequence never reaches zero, and every displayed division step is the unique
ordered division step. In particular, ordinary finite Euclidean iteration never terminates. -/
theorem omnificOmegaEuclideanSequence_nontermination (n : ℕ) :
    let r := omnificOmegaEuclideanSequence.{u}
    0 < r n ∧ ¬ IsFinite (omnificToSurreal (r n)) ∧
      omnificQuotient (r n) (r (n + 1)) = (if n = 0 then 1 else 2) ∧
      omnificRemainder (r n) (r (n + 1)) = r (n + 2) := by
  have hp : 0 < omnificMonomial (1 : SignSequence.{u}) zero_lt_one := omegaPower_pos 1
  exact ⟨omnificEuclideanSequence_pos _ _ hp n,
    (omnificEuclideanSequence_ne_zero_not_finite _ _ hp n).2,
    omnificEuclideanSequence_division _ _ hp n⟩

/-- Strict descent among positive omnific integers is not a well-founded termination measure. -/
theorem omnific_positive_order_not_wellFounded :
    ¬ WellFounded ((· < ·) : {x : OmnificInteger.{u} // 0 < x} →
      {x : OmnificInteger.{u} // 0 < x} → Prop) := by
  let t := omnificMonomial (1 : SignSequence.{u}) zero_lt_one
  have ht := omnificMonomial_mem_purelyInfinite (1 : SignSequence.{u}) zero_lt_one
  have hp : 0 < t := omegaPower_pos 1
  let f : ℕ → {x : OmnificInteger.{u} // 0 < x} := fun n =>
    ⟨omnificEuclideanSequence t ht (n + 1), omnificEuclideanSequence_pos t ht hp _⟩
  have hf (n : ℕ) : f (n + 1) < f n := omnificEuclideanSequence_tail_lt t ht hp n
  exact (RelEmbedding.natGT f hf).not_wellFounded

end
end Surreal.Foundations.SignSequence
