import IntegerPoints.GKStatements
import IntegerPoints.FiniteHilbert

/-!
# Graham--Kolesnik Appendix A, Theorem 2

This module proves the mean-square lower bound invoked in section 3.3.  The
off-diagonal integral is written as the difference of two finite Hilbert
forms.  The sharp finite Hilbert inequality then bounds that difference by
the sum of the squared integer frequencies.
-/

open Real Finset MeasureTheory intervalIntegral

namespace LeanProofs.IntegerPoints

namespace GKAppendixA

/-- The integer interval occurring in Appendix A, without real floors. -/
theorem intRange_nat_two (N : ℕ) :
    intRange (N : ℝ) (2 * (N : ℝ)) = Finset.Ioc N (2 * N) := by
  unfold intRange
  have hfloor : ⌊2 * (N : ℝ)⌋₊ = 2 * N := by
    apply (Nat.floor_eq_iff (by positivity)).2
    constructor <;> norm_num
  rw [Nat.floor_natCast, hfloor]

/-- The dyadic interval `(N, 2N]` contains exactly `N` integers. -/
theorem card_intRange_nat_two (N : ℕ) :
    (intRange (N : ℝ) (2 * (N : ℝ))).card = N := by
  rw [intRange_nat_two, Nat.card_Ioc]
  omega

/-- Endpoint coefficients whose Hilbert form is the integrated
off-diagonal exponential sum. -/
noncomputable def endpointCoeff (X : ℝ) (n : ℕ) : ℂ :=
  (n : ℂ) * e (X / (n : ℝ))

/-- The endpoint finite Hilbert form. -/
noncomputable def endpointHilbert (N : ℕ) (X : ℝ) : ℂ :=
  ∑ m ∈ intRange (N : ℝ) (2 * (N : ℝ)),
    ∑ n ∈ (intRange (N : ℝ) (2 * (N : ℝ))).filter (fun n => n ≠ m),
      endpointCoeff X m * starRingEnd ℂ (endpointCoeff X n) /
        ((n : ℂ) - (m : ℂ))

/-- The endpoint coefficients have squared norm `n²`. -/
theorem endpointCoeff_norm_sq (X : ℝ) (n : ℕ) :
    ‖endpointCoeff X n‖ ^ 2 = (n : ℝ) ^ 2 := by
  rw [endpointCoeff, norm_mul, norm_e]
  simp

/-- The finite Hilbert estimate specialized to the endpoint coefficients. -/
theorem endpointHilbert_norm_le (N : ℕ) (X : ℝ) :
    ‖endpointHilbert N X‖ ≤
      π * ∑ n ∈ intRange (N : ℝ) (2 * (N : ℝ)), (n : ℝ) ^ 2 := by
  simpa only [endpointHilbert, endpointCoeff_norm_sq] using
    FiniteHilbert.finite_hilbert
      (intRange (N : ℝ) (2 * (N : ℝ))) (endpointCoeff X)

/-- The elementary cubic bound for the squared frequencies in `(N, 2N]`. -/
theorem sum_sq_intRange_nat_two_le (N : ℕ) :
    ∑ n ∈ intRange (N : ℝ) (2 * (N : ℝ)), (n : ℝ) ^ 2 ≤
      4 * (N : ℝ) ^ 2 * N := by
  rw [intRange_nat_two]
  calc
    ∑ n ∈ Finset.Ioc N (2 * N), (n : ℝ) ^ 2 ≤
        ∑ _n ∈ Finset.Ioc N (2 * N), (2 * (N : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      simp only [Finset.mem_Ioc] at hn
      have hnle : (n : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hn.2
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      nlinarith
    _ = 4 * (N : ℝ) ^ 2 * N := by
      rw [Finset.sum_const, Nat.card_Ioc]
      have hsub : 2 * N - N = N := by omega
      rw [hsub]
      ring

/-- The exact integral of a nonconstant linear Fourier character. -/
theorem integral_e_linear {u a b : ℝ} (hu : u ≠ 0) :
    (∫ t in a..b, e (u * t)) =
      (e (u * b) - e (u * a)) /
        ((2 * π * Complex.I : ℂ) * (u : ℂ)) := by
  set c : ℂ := (2 * π * Complex.I : ℂ) * (u : ℂ) with hc
  have hπ : ((π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) hπ) Complex.I_ne_zero)
      (by exact_mod_cast hu)
  have hepoint (t : ℝ) : e (u * t) = Complex.exp (c * t) := by
    rw [e, hc]
    push_cast
    congr 1
    ring
  simp_rw [hepoint]
  rw [integral_exp_mul_complex hc0, hc]

/-- A Hilbert-form summand is the endpoint antiderivative of the corresponding
off-diagonal Fourier character. -/
theorem endpoint_term_eq (X : ℝ) {m n : ℕ}
    (hm0 : m ≠ 0) (hn0 : n ≠ 0) (hmn : m ≠ n) :
    endpointCoeff X m * starRingEnd ℂ (endpointCoeff X n) /
        ((n : ℂ) - (m : ℂ)) =
      e ((1 / (m : ℝ) - 1 / (n : ℝ)) * X) /
        (((1 / (m : ℝ) - 1 / (n : ℝ) : ℝ) : ℂ)) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm0
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have hmnR : (n : ℝ) - (m : ℝ) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast Ne.symm hmn
  have hmnC : (n : ℂ) - (m : ℂ) ≠ 0 := by
    exact_mod_cast hmnR
  have huR : 1 / (m : ℝ) - 1 / (n : ℝ) ≠ 0 := by
    rw [sub_ne_zero]
    intro hinv
    apply hmn
    have hcast : (m : ℝ) = (n : ℝ) := by
      apply inv_injective
      simpa only [one_div] using hinv
    exact_mod_cast hcast
  have huC : (((1 / (m : ℝ) - 1 / (n : ℝ) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast huR
  have hphase :
      e (X / (m : ℝ)) * e (-(X / (n : ℝ))) =
        e ((1 / (m : ℝ) - 1 / (n : ℝ)) * X) := by
    rw [← KL.e_add]
    congr 1
    field_simp [hmR, hnR]
    ring
  rw [endpointCoeff, endpointCoeff, map_mul, ← KL.e_neg]
  simp only [map_natCast]
  calc
    (m : ℂ) * e (X / (m : ℝ)) *
          ((n : ℂ) * e (-(X / (n : ℝ)))) /
          ((n : ℂ) - (m : ℂ)) =
        ((m : ℂ) * (n : ℂ) /
          ((n : ℂ) - (m : ℂ))) *
          (e (X / (m : ℝ)) * e (-(X / (n : ℝ)))) := by ring
    _ = ((m : ℂ) * (n : ℂ) /
          ((n : ℂ) - (m : ℂ))) *
          e ((1 / (m : ℝ) - 1 / (n : ℝ)) * X) := by rw [hphase]
    _ = e ((1 / (m : ℝ) - 1 / (n : ℝ)) * X) /
          (((1 / (m : ℝ) - 1 / (n : ℝ) : ℝ) : ℂ)) := by
      push_cast
      field_simp [hmR, hnR, hmC, hnC, hmnC, huC]

/-- The exponential sum in the Appendix A mean square. -/
noncomputable def appendixSum (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ intRange (N : ℝ) (2 * (N : ℝ)), e (t / (n : ℝ))

/-- Expand the squared modulus into its double Fourier sum. -/
theorem appendixSum_mul_conj (N : ℕ) (t : ℝ) :
    appendixSum N t * starRingEnd ℂ (appendixSum N t) =
      ∑ m ∈ intRange (N : ℝ) (2 * (N : ℝ)),
        ∑ n ∈ intRange (N : ℝ) (2 * (N : ℝ)),
          e ((1 / (m : ℝ) - 1 / (n : ℝ)) * t) := by
  unfold appendixSum
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  rw [← KL.e_neg, ← KL.e_add]
  congr 1
  ring

/-- Exact integral of one off-diagonal term, expressed by the two endpoint
Hilbert summands. -/
theorem integral_offdiag_term {N : ℕ} (T : ℝ)
    {m n : ℕ}
    (hm : m ∈ intRange (N : ℝ) (2 * (N : ℝ)))
    (hn : n ∈ intRange (N : ℝ) (2 * (N : ℝ)))
    (hmn : m ≠ n) :
    (∫ t in T..(2 * T),
        e ((1 / (m : ℝ) - 1 / (n : ℝ)) * t)) =
      ((endpointCoeff (2 * T) m * starRingEnd ℂ (endpointCoeff (2 * T) n) /
          ((n : ℂ) - (m : ℂ))) -
        (endpointCoeff T m * starRingEnd ℂ (endpointCoeff T n) /
          ((n : ℂ) - (m : ℂ)))) /
        (2 * π * Complex.I : ℂ) := by
  have hm' := hm
  have hn' := hn
  rw [intRange_nat_two] at hm' hn'
  simp only [Finset.mem_Ioc] at hm' hn'
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  have hu : 1 / (m : ℝ) - 1 / (n : ℝ) ≠ 0 := by
    rw [sub_ne_zero]
    intro hinv
    apply hmn
    have hcast : (m : ℝ) = (n : ℝ) := by
      apply inv_injective
      simpa only [one_div] using hinv
    exact_mod_cast hcast
  have huC : (((1 / (m : ℝ) - 1 / (n : ℝ) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hu
  have hπ : ((π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hK : (2 * π * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hπ) Complex.I_ne_zero
  rw [integral_e_linear hu,
    endpoint_term_eq (2 * T) hm0 hn0 hmn,
    endpoint_term_eq T hm0 hn0 hmn]
  field_simp [huC, hK]

/-- Exact complex mean-square identity: the diagonal is `T` times the number
of summands and the residual is a difference of endpoint Hilbert forms. -/
theorem integral_appendixSum_mul_conj (N : ℕ) (T : ℝ) :
    (∫ t in T..(2 * T),
        appendixSum N t * starRingEnd ℂ (appendixSum N t)) =
      (T : ℂ) * (intRange (N : ℝ) (2 * (N : ℝ))).card +
        (endpointHilbert N (2 * T) - endpointHilbert N T) /
          (2 * π * Complex.I : ℂ) := by
  classical
  let S : Finset ℕ := intRange (N : ℝ) (2 * (N : ℝ))
  have hterm (m n : ℕ) : IntervalIntegrable
      (fun t : ℝ => e ((1 / (m : ℝ) - 1 / (n : ℝ)) * t))
      volume T (2 * T) := by
    apply Continuous.intervalIntegrable
    unfold e
    fun_prop
  have hinner (m : ℕ) : IntervalIntegrable
      (fun t : ℝ => ∑ n ∈ S,
        e ((1 / (m : ℝ) - 1 / (n : ℝ)) * t))
      volume T (2 * T) := by
    rw [show (fun t : ℝ => ∑ n ∈ S,
        e ((1 / (m : ℝ) - 1 / (n : ℝ)) * t)) =
      ∑ n ∈ S, (fun t : ℝ =>
        e ((1 / (m : ℝ) - 1 / (n : ℝ)) * t)) by
          funext t
          simp]
    exact IntervalIntegrable.sum S (fun n _ => hterm m n)
  have hintegral_inner (m : ℕ) :
      (∫ t in T..(2 * T), ∑ n ∈ S,
          e ((1 / (m : ℝ) - 1 / (n : ℝ)) * t)) =
        ∑ n ∈ S, ∫ t in T..(2 * T),
          e ((1 / (m : ℝ) - 1 / (n : ℝ)) * t) := by
    rw [intervalIntegral.integral_finsetSum
      (f := fun (n : ℕ) (t : ℝ) =>
        e ((1 / (m : ℝ) - 1 / (n : ℝ)) * t))
      (fun n _ => hterm m n)]
  have hdiag (m : ℕ) :
      (∫ t in T..(2 * T),
          e ((1 / (m : ℝ) - 1 / (m : ℝ)) * t)) = (T : ℂ) := by
    simp [e]
    ring
  have hsplit (m : ℕ) (hm : m ∈ S) :
      ∑ n ∈ S,
          ∫ t in T..(2 * T),
            e ((1 / (m : ℝ) - 1 / (n : ℝ)) * t) =
        (T : ℂ) +
          ∑ n ∈ S.filter (fun n => n ≠ m),
            ((endpointCoeff (2 * T) m *
                  starRingEnd ℂ (endpointCoeff (2 * T) n) /
                  ((n : ℂ) - (m : ℂ))) -
              (endpointCoeff T m * starRingEnd ℂ (endpointCoeff T n) /
                  ((n : ℂ) - (m : ℂ)))) /
                (2 * π * Complex.I : ℂ) := by
    calc
      ∑ n ∈ S,
          ∫ t in T..(2 * T),
            e ((1 / (m : ℝ) - 1 / (n : ℝ)) * t) =
          (∑ n ∈ S.erase m,
            ∫ t in T..(2 * T),
              e ((1 / (m : ℝ) - 1 / (n : ℝ)) * t)) +
            ∫ t in T..(2 * T),
              e ((1 / (m : ℝ) - 1 / (m : ℝ)) * t) := by
        exact (Finset.sum_erase_add S _ hm).symm
      _ = (∑ n ∈ S.filter (fun n => n ≠ m),
            ∫ t in T..(2 * T),
              e ((1 / (m : ℝ) - 1 / (n : ℝ)) * t)) + (T : ℂ) := by
        rw [Finset.filter_ne', hdiag]
      _ = (T : ℂ) +
          ∑ n ∈ S.filter (fun n => n ≠ m),
            ((endpointCoeff (2 * T) m *
                  starRingEnd ℂ (endpointCoeff (2 * T) n) /
                  ((n : ℂ) - (m : ℂ))) -
              (endpointCoeff T m * starRingEnd ℂ (endpointCoeff T n) /
                  ((n : ℂ) - (m : ℂ)))) /
                (2 * π * Complex.I : ℂ) := by
        rw [add_comm]
        congr 1
        refine Finset.sum_congr rfl fun n hn => ?_
        have hnS : n ∈ S := (Finset.mem_filter.mp hn).1
        have hnm : n ≠ m := (Finset.mem_filter.mp hn).2
        exact integral_offdiag_term T (by simpa only [S] using hm)
          (by simpa only [S] using hnS) (Ne.symm hnm)
  rw [show (fun t : ℝ =>
      appendixSum N t * starRingEnd ℂ (appendixSum N t)) =
    fun t : ℝ => ∑ m ∈ S, ∑ n ∈ S,
      e ((1 / (m : ℝ) - 1 / (n : ℝ)) * t) by
        funext t
        simpa only [S] using appendixSum_mul_conj N t]
  rw [intervalIntegral.integral_finsetSum
    (f := fun (m : ℕ) (t : ℝ) => ∑ n ∈ S,
      e ((1 / (m : ℝ) - 1 / (n : ℝ)) * t))
    (fun m _ => hinner m)]
  simp_rw [hintegral_inner]
  calc
    ∑ m ∈ S, ∑ n ∈ S,
        ∫ t in T..(2 * T),
          e ((1 / (m : ℝ) - 1 / (n : ℝ)) * t) =
      ∑ m ∈ S, ((T : ℂ) +
          ∑ n ∈ S.filter (fun n => n ≠ m),
            ((endpointCoeff (2 * T) m *
                  starRingEnd ℂ (endpointCoeff (2 * T) n) /
                  ((n : ℂ) - (m : ℂ))) -
              (endpointCoeff T m * starRingEnd ℂ (endpointCoeff T n) /
                  ((n : ℂ) - (m : ℂ)))) /
                (2 * π * Complex.I : ℂ)) := by
        exact Finset.sum_congr rfl fun m hm => hsplit m hm
    _ = (T : ℂ) * S.card +
        ∑ m ∈ S, ∑ n ∈ S.filter (fun n => n ≠ m),
          ((endpointCoeff (2 * T) m *
                starRingEnd ℂ (endpointCoeff (2 * T) n) /
                ((n : ℂ) - (m : ℂ))) -
            (endpointCoeff T m * starRingEnd ℂ (endpointCoeff T n) /
                ((n : ℂ) - (m : ℂ)))) /
              (2 * π * Complex.I : ℂ) := by
        rw [Finset.sum_add_distrib]
        simp
        ring
    _ = (T : ℂ) * (intRange (N : ℝ) (2 * (N : ℝ))).card +
        (endpointHilbert N (2 * T) - endpointHilbert N T) /
          (2 * π * Complex.I : ℂ) := by
        simp only [S, endpointHilbert, sub_div, Finset.sum_sub_distrib,
          ← Finset.sum_div]

/-- The endpoint residual has norm at most the sum of squared frequencies. -/
theorem endpoint_residual_norm_le (N : ℕ) (T : ℝ) :
    ‖(endpointHilbert N (2 * T) - endpointHilbert N T) /
        (2 * π * Complex.I : ℂ)‖ ≤
      ∑ n ∈ intRange (N : ℝ) (2 * (N : ℝ)), (n : ℝ) ^ 2 := by
  let Q : ℝ :=
    ∑ n ∈ intRange (N : ℝ) (2 * (N : ℝ)), (n : ℝ) ^ 2
  have hfactor : ‖(2 * π * Complex.I : ℂ)‖ = 2 * π := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one, abs_of_pos Real.pi_pos]
    norm_num
  have hnum :
      ‖endpointHilbert N (2 * T) - endpointHilbert N T‖ ≤ 2 * π * Q := by
    calc
      ‖endpointHilbert N (2 * T) - endpointHilbert N T‖ ≤
          ‖endpointHilbert N (2 * T)‖ + ‖endpointHilbert N T‖ :=
        norm_sub_le _ _
      _ ≤ π * Q + π * Q := by
        exact add_le_add (by simpa only [Q] using endpointHilbert_norm_le N (2 * T))
          (by simpa only [Q] using endpointHilbert_norm_le N T)
      _ = 2 * π * Q := by ring
  rw [norm_div, hfactor]
  calc
    ‖endpointHilbert N (2 * T) - endpointHilbert N T‖ / (2 * π) ≤
        (2 * π * Q) / (2 * π) := by
      exact div_le_div_of_nonneg_right hnum (by positivity)
    _ = Q := by field_simp [Real.pi_ne_zero]

/-- Real form of the exact mean-square identity. -/
theorem integral_appendixSum_norm_sq (N : ℕ) (T : ℝ) :
    (∫ t in T..(2 * T), ‖appendixSum N t‖ ^ 2) =
      T * (intRange (N : ℝ) (2 * (N : ℝ))).card +
        ((endpointHilbert N (2 * T) - endpointHilbert N T) /
          (2 * π * Complex.I : ℂ)).re := by
  calc
    (∫ t in T..(2 * T), ‖appendixSum N t‖ ^ 2) =
        ∫ t in T..(2 * T),
          (appendixSum N t * starRingEnd ℂ (appendixSum N t)).re := by
      apply intervalIntegral.integral_congr
      intro t _
      change ‖appendixSum N t‖ ^ 2 =
        (appendixSum N t * starRingEnd ℂ (appendixSum N t)).re
      simp [Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]
    _ = (∫ t in T..(2 * T),
          appendixSum N t * starRingEnd ℂ (appendixSum N t)).re := by
      exact intervalIntegral.intervalIntegral_re (𝕜 := ℂ) (f := fun t : ℝ =>
        appendixSum N t * starRingEnd ℂ (appendixSum N t)) (by
          apply Continuous.intervalIntegrable
          unfold appendixSum e
          fun_prop)
    _ = ((T : ℂ) * (intRange (N : ℝ) (2 * (N : ℝ))).card +
        (endpointHilbert N (2 * T) - endpointHilbert N T) /
          (2 * π * Complex.I : ℂ)).re := by
      rw [integral_appendixSum_mul_conj]
    _ = T * (intRange (N : ℝ) (2 * (N : ℝ))).card +
        ((endpointHilbert N (2 * T) - endpointHilbert N T) /
          (2 * π * Complex.I : ℂ)).re := by
      simp

end GKAppendixA

/-- **Graham–Kolesnik, Appendix A, Theorem 2**, in the form invoked in
§3.3. -/
theorem gk_appendixA_theorem2_invoked_holds :
    gk_appendixA_theorem2_invoked := by
  intro N T _hN _hT
  let Q : ℝ :=
    ∑ n ∈ intRange (N : ℝ) (2 * (N : ℝ)), (n : ℝ) ^ 2
  let R : ℂ :=
    (GKAppendixA.endpointHilbert N (2 * T) -
        GKAppendixA.endpointHilbert N T) /
      (2 * π * Complex.I : ℂ)
  have hRnorm : ‖R‖ ≤ Q := by
    simpa only [R, Q] using GKAppendixA.endpoint_residual_norm_le N T
  have habs : |R.re| ≤ ‖R‖ := Complex.abs_re_le_norm R
  have hre : -Q ≤ R.re := by
    calc
      -Q ≤ -‖R‖ := neg_le_neg hRnorm
      _ ≤ -|R.re| := neg_le_neg habs
      _ ≤ R.re := neg_abs_le _
  have hQ : Q ≤ 4 * (N : ℝ) ^ 2 * N := by
    simpa only [Q] using GKAppendixA.sum_sq_intRange_nat_two_le N
  change (T - 4 * (N : ℝ) ^ 2) * N ≤
    ∫ t in T..(2 * T), ‖GKAppendixA.appendixSum N t‖ ^ 2
  rw [GKAppendixA.integral_appendixSum_norm_sq,
    GKAppendixA.card_intRange_nat_two]
  change (T - 4 * (N : ℝ) ^ 2) * N ≤ T * N + R.re
  nlinarith

end LeanProofs.IntegerPoints
