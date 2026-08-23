import IntegerPoints.GKAppendixATheorem2
import IntegerPoints.Lemma9Tools
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Graham--Kolesnik section 3.3: the lower bound `l >= 1/2`

The Appendix A mean-square lower bound for
`S(t) = sum_{N < n <= 2N} e(t/n)` is incompatible with the exponent-pair
estimate when `l < 1/2`.  We use the globally smooth reciprocal extension
from `Lemma9Tools` so that the test phase meets the definition's global
`ContDiff` requirement without changing it on the dyadic summation interval.
-/

open Real Finset intervalIntegral Filter

namespace LeanProofs.IntegerPoints

namespace GKSec33

theorem iteratedDeriv_one_div (q : ℕ) (x : ℝ) :
    iteratedDeriv q (fun y : ℝ => 1 / y) x =
      (-1 : ℝ) ^ q * (q.factorial : ℝ) * x ^ (-1 - q : ℤ) := by
  simpa only [iteratedDerivWithin_univ] using
    (iteratedDerivWithin_one_div (s := Set.univ) q isOpen_univ
      (Set.mem_univ x))

theorem iteratedDeriv_cdiv (c : ℝ) (q : ℕ) (x : ℝ) :
    iteratedDeriv q (fun y : ℝ => c / y) x =
      c * ((-1 : ℝ) ^ q * (q.factorial : ℝ) * x ^ (-1 - q : ℤ)) := by
  have hfun : (fun y : ℝ => c / y) = fun y : ℝ => c * (1 / y) := by
    funext y
    simp only [div_eq_mul_inv, one_mul]
  rw [hfun, iteratedDeriv_const_mul_field, iteratedDeriv_one_div]

theorem iteratedDeriv_ftest_neg (y x : ℝ) (p : ℕ) (hx : 1 / 2 < x) :
    iteratedDeriv (p + 1) (L9.ftest (-y)) x =
      (-1 : ℝ) ^ p * ((p + 1).factorial : ℝ) * y *
        x ^ (-(2 : ℝ) - p) := by
  rw [(L9.ftest_eventuallyEq hx).iteratedDeriv_eq (p + 1),
    iteratedDeriv_cdiv, ← Real.rpow_intCast]
  push_cast
  rw [pow_succ]
  ring_nf

theorem two_poch_eq_factorial (p : ℕ) :
    ∏ i ∈ Finset.range p, ((2 : ℝ) + i) =
      ((p + 1).factorial : ℝ) := by
  induction p with
  | zero => simp
  | succ p ih =>
      rw [Finset.prod_range_succ, ih]
      calc
        ((p + 1).factorial : ℝ) * (2 + ↑p) =
            (((p + 2) * (p + 1).factorial : ℕ) : ℝ) := by
          push_cast
          ring
        _ = ((p + 2).factorial : ℝ) := by
          norm_cast

/-- The smooth reciprocal phase agrees with `-t/x` on the dyadic interval and
therefore belongs to every finite-order class `F(N,P,2,t,epsilon)`. -/
theorem ftest_neg_mem_gkClass (N P : ℕ) (ε t : ℝ)
    (hN : 0 < N) (hε : 0 < ε) (ht : 0 < t) :
    InGKClass (N : ℝ) P 2 t ε (N : ℝ) (2 * (N : ℝ))
      (L9.ftest (-t)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine ⟨le_rfl, ?_, le_rfl, L9.ftest_contDiff_nat (-t) P, ?_⟩
  · linarith
  · intro p _hp x hx
    have hxhalf : 1 / 2 < x := lt_of_lt_of_le (by norm_num) (hN1.trans hx.1)
    rw [iteratedDeriv_ftest_neg t x p hxhalf, two_poch_eq_factorial]
    have hx0 : 0 < x := by linarith
    have hfac : (0 : ℝ) < ((p + 1).factorial : ℝ) := by positivity
    have hrpow : 0 < x ^ (-(2 : ℝ) - p) := Real.rpow_pos_of_pos hx0 _
    norm_num
    positivity

/-- On `(N,2N]`, the smooth test phase is `-t/n`; conjugation therefore
identifies its exponential sum norm with the Appendix A sum. -/
theorem norm_ftest_neg_sum_eq_appendixSum (N : ℕ) (t : ℝ) (hN : 0 < N) :
    ‖∑ n ∈ intRange (N : ℝ) (2 * (N : ℝ)), e (L9.ftest (-t) n)‖ =
      ‖GKAppendixA.appendixSum N t‖ := by
  have hphase : ∀ n ∈ intRange (N : ℝ) (2 * (N : ℝ)),
      L9.ftest (-t) n = -(t / (n : ℝ)) := by
    intro n hn
    have hn' := hn
    rw [GKAppendixA.intRange_nat_two] at hn'
    simp only [Finset.mem_Ioc] at hn'
    have hn0 : 0 < n := lt_trans hN hn'.1
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    have hnHalf : 1 / 2 ≤ (n : ℝ) := by linarith
    unfold L9.ftest
    rw [L9.hfun_eq hnHalf]
    ring
  calc
    ‖∑ n ∈ intRange (N : ℝ) (2 * (N : ℝ)), e (L9.ftest (-t) n)‖ =
        ‖∑ n ∈ intRange (N : ℝ) (2 * (N : ℝ)), e (-(t / (n : ℝ)))‖ := by
      congr 1
      exact Finset.sum_congr rfl fun n hn => by rw [hphase n hn]
    _ = ‖∑ n ∈ intRange (N : ℝ) (2 * (N : ℝ)), e (t / (n : ℝ))‖ :=
      Lemma1.norm_sum_e_neg _ (fun x : ℝ => t / x)
    _ = ‖GKAppendixA.appendixSum N t‖ := rfl

/-- If `alpha < 1`, no fixed multiple of `N^alpha + 1` dominates every
positive natural number `N`. -/
theorem not_forall_nat_le_const_rpow_add_one {α K : ℝ} (hα : α < 1) :
    ¬ ∀ N : ℕ, 0 < N →
      (N : ℝ) ≤ K * ((N : ℝ) ^ α + 1) := by
  intro hall
  have hexp : -(1 - α) = α - 1 := by ring
  have hpowReal :
      Tendsto (fun x : ℝ => x ^ (α - 1)) atTop (nhds (0 : ℝ)) := by
    simpa only [hexp] using
      tendsto_rpow_neg_atTop (y := 1 - α) (show 0 < 1 - α by linarith)
  have hpowNat :
      Tendsto (fun N : ℕ => (N : ℝ) ^ (α - 1)) atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def] using
      hpowReal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinvNat :
      Tendsto (fun N : ℕ => (N : ℝ) ^ (-1 : ℝ)) atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def] using
      (tendsto_rpow_neg_atTop (y := (1 : ℝ)) zero_lt_one).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlim :
      Tendsto
        (fun N : ℕ => K * ((N : ℝ) ^ (α - 1) + (N : ℝ) ^ (-1 : ℝ)))
        atTop (nhds (0 : ℝ)) := by
    simpa only [zero_add, mul_zero] using
      (hpowNat.add hinvNat).const_mul K
  have hsmall :
      ∀ᶠ N : ℕ in atTop,
        K * ((N : ℝ) ^ (α - 1) + (N : ℝ) ^ (-1 : ℝ)) < 1 :=
    (tendsto_order.1 hlim).2 (1 : ℝ) zero_lt_one
  obtain ⟨N, hsmallN, hN1⟩ :=
    (hsmall.and (Filter.eventually_ge_atTop (1 : ℕ))).exists
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.2 hNpos
  have hnormalized :
      1 ≤ K * ((N : ℝ) ^ (α - 1) + (N : ℝ) ^ (-1 : ℝ)) := by
    calc
      1 = (N : ℝ) / (N : ℝ) := by rw [div_self hNR.ne']
      _ ≤ (K * ((N : ℝ) ^ α + 1)) / (N : ℝ) :=
        (div_le_div_iff_of_pos_right hNR).2 (hall N hNpos)
      _ = K * ((N : ℝ) ^ (α - 1) + (N : ℝ) ^ (-1 : ℝ)) := by
        rw [mul_div_assoc, add_div, ← Real.rpow_sub_one hNR.ne' α,
          one_div, ← Real.rpow_neg_one (N : ℝ)]
  exact (not_lt_of_ge hnormalized) hsmallN

/-- An exponent-pair estimate gives a uniform pointwise bound for the
Appendix A sums on `8N^2 <= t <= 16N^2`.  Taking maxima handles both signs of
`k` and does not assume that the estimate's original constant was stated
nonnegative. -/
theorem exists_appendixSum_pointwise_bound {k l : ℝ}
    (hpair : SatisfiesExponentPairBound k l) :
    ∃ C₀ D : ℝ, 0 ≤ C₀ ∧ 0 < D ∧
      ∀ (N : ℕ), 0 < N → ∀ t ∈ Set.Icc
        (8 * (N : ℝ) ^ 2) (2 * (8 * (N : ℝ) ^ 2)),
        ‖GKAppendixA.appendixSum N t‖ ≤
          C₀ * (D * (N : ℝ) ^ l + 1 / 8) := by
  obtain ⟨P, ε, C, hε, _hεhalf, hbound⟩ := hpair 2 (by norm_num)
  let C₀ : ℝ := max C 0
  let D : ℝ := max ((8 : ℝ) ^ k) ((16 : ℝ) ^ k)
  have hC₀ : 0 ≤ C₀ := by simp [C₀]
  have hD : 0 < D := lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) k)
    (le_max_left _ _)
  refine ⟨C₀, D, hC₀, hD, ?_⟩
  intro N hN t ht
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.2 hN
  have hN2 : 0 < (N : ℝ) ^ 2 := sq_pos_of_pos hNR
  have hT0 : 0 < 8 * (N : ℝ) ^ 2 := mul_pos (by norm_num) hN2
  have ht0 : 0 < t := lt_of_lt_of_le hT0 ht.1
  have hclass := ftest_neg_mem_gkClass N P ε t hN hε ht0
  have hraw := hbound (N : ℝ) t (N : ℝ) (2 * (N : ℝ))
    (L9.ftest (-t)) hNR ht0 hclass
  rw [norm_ftest_neg_sum_eq_appendixSum N t hN] at hraw
  have hNpow : (N : ℝ) ^ (-(2 : ℝ)) = 1 / (N : ℝ) ^ 2 := by
    rw [Real.rpow_neg hNR.le, Real.rpow_two, inv_eq_one_div]
  let q : ℝ := t * (N : ℝ) ^ (-(2 : ℝ))
  have hqeq : q = t / (N : ℝ) ^ 2 := by
    simp only [q, hNpow]
    ring
  have hq8 : 8 ≤ q := by
    rw [hqeq, le_div_iff₀ hN2]
    exact ht.1
  have hq16 : q ≤ 16 := by
    rw [hqeq, div_le_iff₀ hN2]
    nlinarith [ht.2]
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq8
  have hqpow : q ^ k ≤ D := by
    rcases le_total 0 k with hk | hk
    · exact (Real.rpow_le_rpow hq0.le hq16 hk).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_nonpos (by norm_num) hq8 hk).trans
        (le_max_left _ _)
  have htinv : t⁻¹ * (N : ℝ) ^ 2 ≤ 1 / 8 := by
    rw [inv_mul_eq_div, div_le_iff₀ ht0]
    nlinarith [ht.1]
  have hNl : 0 < (N : ℝ) ^ l := Real.rpow_pos_of_pos hNR l
  have hfirst : q ^ k * (N : ℝ) ^ l ≤ D * (N : ℝ) ^ l :=
    mul_le_mul_of_nonneg_right hqpow hNl.le
  have hinside :
      q ^ k * (N : ℝ) ^ l + t⁻¹ * (N : ℝ) ^ 2 ≤
        D * (N : ℝ) ^ l + 1 / 8 :=
    add_le_add hfirst htinv
  have hinside0 :
      0 ≤ q ^ k * (N : ℝ) ^ l + t⁻¹ * (N : ℝ) ^ 2 := by
    exact add_nonneg
      (mul_nonneg (Real.rpow_nonneg hq0.le k) hNl.le)
      (mul_nonneg (inv_nonneg.mpr ht0.le) hN2.le)
  rw [Real.rpow_two] at hraw
  change ‖GKAppendixA.appendixSum N t‖ ≤
    C * (q ^ k * (N : ℝ) ^ l + t⁻¹ * (N : ℝ) ^ 2) at hraw
  calc
    ‖GKAppendixA.appendixSum N t‖ ≤
        C * (q ^ k * (N : ℝ) ^ l + t⁻¹ * (N : ℝ) ^ 2) := hraw
    _ ≤ C₀ * (q ^ k * (N : ℝ) ^ l + t⁻¹ * (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (le_max_left C 0) hinside0
    _ ≤ C₀ * (D * (N : ℝ) ^ l + 1 / 8) :=
      mul_le_mul_of_nonneg_left hinside hC₀

/-- Combining a pointwise dyadic bound with Appendix A's mean-square lower
bound forces a growth inequality with exponent `2*l`. -/
theorem nat_le_rpow_of_appendixSum_bound {l C₀ D : ℝ}
    (hC₀ : 0 ≤ C₀) (hD : 0 ≤ D)
    (hpoint : ∀ (N : ℕ), 0 < N → ∀ t ∈ Set.Icc
      (8 * (N : ℝ) ^ 2) (2 * (8 * (N : ℝ) ^ 2)),
      ‖GKAppendixA.appendixSum N t‖ ≤
        C₀ * (D * (N : ℝ) ^ l + 1 / 8)) :
    ∀ (N : ℕ), 0 < N →
      (N : ℝ) ≤
        (4 * C₀ ^ 2 * (D ^ 2 + 1)) * ((N : ℝ) ^ (2 * l) + 1) := by
  intro N hN
  let n : ℝ := N
  let T : ℝ := 8 * n ^ 2
  let B : ℝ := C₀ * (D * n ^ l + 1 / 8)
  have hn : 0 < n := by simpa only [n] using Nat.cast_pos.2 hN
  have hn2 : 0 < n ^ 2 := sq_pos_of_pos hn
  have hT : 0 < T := by simp only [T]; positivity
  have hB : 0 ≤ B := by
    simp only [B]
    positivity
  have hcont : Continuous (fun t : ℝ => ‖GKAppendixA.appendixSum N t‖ ^ 2) := by
    unfold GKAppendixA.appendixSum e
    fun_prop
  have hupper :
      (∫ t in T..(2 * T), ‖GKAppendixA.appendixSum N t‖ ^ 2) ≤
        T * B ^ 2 := by
    calc
      (∫ t in T..(2 * T), ‖GKAppendixA.appendixSum N t‖ ^ 2) ≤
          ∫ _t in T..(2 * T), B ^ 2 := by
        apply intervalIntegral.integral_mono_on (show T ≤ 2 * T by linarith)
          (hcont.intervalIntegrable T (2 * T)) intervalIntegrable_const
        intro t ht
        have hp : ‖GKAppendixA.appendixSum N t‖ ≤ B := by
          simpa only [T, B, n] using hpoint N hN t ht
        exact pow_le_pow_left₀ (norm_nonneg _) hp 2
      _ = T * B ^ 2 := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring
  have hlower := gk_appendixA_theorem2_invoked_holds N T hN hT
  have hmain : (T - 4 * n ^ 2) * n ≤ T * B ^ 2 := by
    exact hlower.trans hupper
  have hscaled : 4 * n ^ 2 * n ≤ 8 * n ^ 2 * B ^ 2 := by
    calc
      4 * n ^ 2 * n = (T - 4 * n ^ 2) * n := by
        simp only [T]
        ring
      _ ≤ T * B ^ 2 := hmain
      _ = 8 * n ^ 2 * B ^ 2 := by simp only [T]
  have hfactor : 0 < 4 * n ^ 2 := mul_pos (by norm_num) hn2
  have hnB : n ≤ 2 * B ^ 2 := by
    apply (mul_le_mul_iff_left₀ hfactor).mp
    calc
      n * (4 * n ^ 2) = 4 * n ^ 2 * n := by ring
      _ ≤ 8 * n ^ 2 * B ^ 2 := hscaled
      _ = (2 * B ^ 2) * (4 * n ^ 2) := by ring
  let x : ℝ := n ^ l
  have hx : 0 < x := Real.rpow_pos_of_pos hn l
  have hsquare : (D * x + 1 / 8) ^ 2 ≤
      2 * (D ^ 2 * x ^ 2 + (1 / 8 : ℝ) ^ 2) := by
    nlinarith [sq_nonneg (D * x - 1 / 8)]
  have hproduct : D ^ 2 * x ^ 2 + (1 / 8 : ℝ) ^ 2 ≤
      (D ^ 2 + 1) * (x ^ 2 + 1) := by
    nlinarith [sq_nonneg D, sq_nonneg x]
  have hBbound : 2 * B ^ 2 ≤
      4 * C₀ ^ 2 * (D ^ 2 + 1) * (x ^ 2 + 1) := by
    simp only [B]
    calc
      2 * (C₀ * (D * n ^ l + 1 / 8)) ^ 2 =
          2 * C₀ ^ 2 * (D * x + 1 / 8) ^ 2 := by simp only [x]; ring
      _ ≤ 2 * C₀ ^ 2 *
          (2 * (D ^ 2 * x ^ 2 + (1 / 8 : ℝ) ^ 2)) := by
        gcongr
      _ ≤ 2 * C₀ ^ 2 * (2 * ((D ^ 2 + 1) * (x ^ 2 + 1))) := by
        gcongr
      _ = 4 * C₀ ^ 2 * (D ^ 2 + 1) * (x ^ 2 + 1) := by ring
  have hxpow : x ^ 2 = n ^ (2 * l) := by
    simp only [x]
    rw [← Real.rpow_two, ← Real.rpow_mul hn.le]
    congr 1
    ring
  calc
    (N : ℝ) = n := rfl
    _ ≤ 2 * B ^ 2 := hnB
    _ ≤ 4 * C₀ ^ 2 * (D ^ 2 + 1) * (x ^ 2 + 1) := hBbound
    _ = (4 * C₀ ^ 2 * (D ^ 2 + 1)) * ((N : ℝ) ^ (2 * l) + 1) := by
      rw [hxpow]

end GKSec33

/-- **Graham--Kolesnik, section 3.3**: every pair satisfying the exponential
sum estimate has second coordinate at least `1/2`. -/
theorem gk_sec33_l_ge_half_holds : gk_sec33_l_ge_half := by
  intro k l hpair
  by_contra hnot
  have hl : l < 1 / 2 := lt_of_not_ge hnot
  obtain ⟨C₀, D, hC₀, hD, hpoint⟩ :=
    GKSec33.exists_appendixSum_pointwise_bound hpair
  have hall := GKSec33.nat_le_rpow_of_appendixSum_bound hC₀ hD.le hpoint
  exact (GKSec33.not_forall_nat_le_const_rpow_add_one
    (K := 4 * C₀ ^ 2 * (D ^ 2 + 1)) (α := 2 * l) (by linarith)) hall

end LeanProofs.IntegerPoints
