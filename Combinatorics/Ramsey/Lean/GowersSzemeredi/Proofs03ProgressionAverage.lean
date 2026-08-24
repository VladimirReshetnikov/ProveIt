import GowersSzemeredi.Proofs03Equivalences
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# The generalized von Neumann bound for arithmetic progressions

This module proves the repaired prime-modulus form of Theorem 3.2.  The
restriction `k ≤ N` guarantees that the coefficient reindexed at each
inductive step is nonzero modulo `N`.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private def progressionTailDifference {N n : Nat}
    (f : Fin (n + 1) → ZMod N → Complex) (u : ZMod N) :
    Fin n → ZMod N → Complex :=
  fun i ↦ difference (f i.succ) (((i : Nat) + 1 : ZMod N) * u)

private def progressionTailProduct {N n : Nat}
    (f : Fin (n + 1) → ZMod N → Complex) (s r : ZMod N) : Complex :=
  ∏ i : Fin n, f i.succ (s - (((i : Nat) + 1 : ZMod N) * r))

private lemma progressionTailDifference_discValued {N n : Nat}
    (f : Fin (n + 1) → ZMod N → Complex)
    (hf : ∀ i, DiscValued (f i)) (u : ZMod N) :
    ∀ i, DiscValued (progressionTailDifference f u i) := by
  intro i
  exact difference_discValued (hf i.succ) _

private lemma progressionAverage_trivial {N k : Nat} [NeZero N]
    (f : Fin k → ZMod N → Complex) (hf : ∀ i, DiscValued (f i)) :
    ‖progressionAverage f‖ ≤ (N : Real) ^ 2 := by
  calc
    ‖progressionAverage f‖ ≤
        ∑ r : ZMod N, ‖∑ s : ZMod N, ∏ i, f i (s - (i : Nat) * r)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _r : ZMod N, ∑ _s : ZMod N, (1 : Real) := by
      apply Finset.sum_le_sum
      intro r _
      calc
        ‖∑ s : ZMod N, ∏ i, f i (s - (i : Nat) * r)‖ ≤
            ∑ s : ZMod N, ‖∏ i, f i (s - (i : Nat) * r)‖ := norm_sum_le _ _
        _ ≤ ∑ _s : ZMod N, (1 : Real) := by
          apply Finset.sum_le_sum
          intro s _
          rw [norm_prod]
          exact Finset.prod_le_one (fun _ _ ↦ norm_nonneg _)
            (fun i _ ↦ hf i _)
    _ = (N : Real) ^ 2 := by simp [ZMod.card, pow_two]

private lemma progressionAverage_two_factor {N : Nat} [NeZero N]
    (f : Fin 2 → ZMod N → Complex) :
    progressionAverage f =
      (∑ s : ZMod N, f 0 s) * (∑ t : ZMod N, f 1 t) := by
  unfold progressionAverage
  simp only [Fin.prod_univ_two, Fin.val_zero, Nat.cast_zero, zero_mul, sub_zero,
    Fin.val_one, Nat.cast_one, one_mul]
  calc
    (∑ r : ZMod N, ∑ s : ZMod N, f 0 s * f 1 (s - r)) =
        ∑ s : ZMod N, ∑ r : ZMod N, f 0 s * f 1 (s - r) := by
      rw [Finset.sum_comm]
    _ = ∑ s : ZMod N, ∑ t : ZMod N, f 0 s * f 1 t := by
      apply Finset.sum_congr rfl
      intro s _
      simpa [Equiv.subLeft_apply] using
        (Equiv.sum_comp (Equiv.subLeft s) (fun t ↦ f 0 s * f 1 t))
    _ = (∑ s : ZMod N, f 0 s) * (∑ t : ZMod N, f 1 t) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]

private lemma progressionAverage_split {N n : Nat} [NeZero N]
    (f : Fin (n + 1) → ZMod N → Complex) :
    progressionAverage f =
      ∑ s : ZMod N, f 0 s * ∑ r : ZMod N, progressionTailProduct f s r := by
  unfold progressionAverage
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  calc
    (∑ r : ZMod N, ∏ i, f i (s - (i : Nat) * r)) =
        ∑ r : ZMod N, f 0 s * progressionTailProduct f s r := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Fin.prod_univ_succ]
      simp only [Fin.val_zero, Nat.cast_zero, zero_mul, sub_zero]
      congr 1
      unfold progressionTailProduct
      apply Finset.prod_congr rfl
      intro i _
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
    _ = f 0 s * ∑ r : ZMod N, progressionTailProduct f s r := by
      rw [Finset.mul_sum]

private lemma progressionTail_energy {N n : Nat} [NeZero N]
    (f : Fin (n + 1) → ZMod N → Complex) :
    (∑ s : ZMod N,
        ‖∑ r : ZMod N, progressionTailProduct f s r‖ ^ 2) ≤
      ∑ u : ZMod N, ‖progressionAverage (progressionTailDifference f u)‖ := by
  let T : ZMod N → ZMod N → Complex := progressionTailProduct f
  have henergy :
      ((∑ s : ZMod N, ‖∑ r : ZMod N, T s r‖ ^ 2 : Real) : Complex) =
        ∑ u : ZMod N, progressionAverage (progressionTailDifference f u) := by
    calc
      ((∑ s : ZMod N, ‖∑ r : ZMod N, T s r‖ ^ 2 : Real) : Complex) =
          ∑ s : ZMod N,
            (∑ r : ZMod N, T s r) * star (∑ t : ZMod N, T s t) := by
        push_cast
        apply Finset.sum_congr rfl
        intro s _
        exact (Complex.mul_conj' _).symm
      _ = ∑ s : ZMod N, ∑ r : ZMod N, ∑ t : ZMod N,
            T s r * star (T s t) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [star_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
      _ = ∑ r : ZMod N, ∑ u : ZMod N, ∑ s : ZMod N,
            T s r * star (T s (r + u)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r _
        calc
          (∑ s : ZMod N, ∑ t : ZMod N, T s r * star (T s t)) =
              ∑ s : ZMod N, ∑ u : ZMod N,
                T s r * star (T s (r + u)) := by
            apply Finset.sum_congr rfl
            intro s _
            exact (Equiv.sum_comp (Equiv.addLeft r)
              (fun t : ZMod N ↦ T s r * star (T s t))).symm
          _ = ∑ u : ZMod N, ∑ s : ZMod N,
                T s r * star (T s (r + u)) := by rw [Finset.sum_comm]
      _ = ∑ u : ZMod N, ∑ r : ZMod N, ∑ s : ZMod N,
            T (s + r) r * star (T (s + r) (r + u)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro r _
        exact (Equiv.sum_comp (Equiv.addRight r)
          (fun s : ZMod N ↦ T s r * star (T s (r + u)))).symm
      _ = ∑ u : ZMod N,
          progressionAverage (progressionTailDifference f u) := by
        apply Finset.sum_congr rfl
        intro u _
        unfold progressionAverage
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro s _
        simp only [T, progressionTailProduct, progressionTailDifference,
          difference, star_prod]
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i _
        congr 2
        · ring
        · congr 1
          ring
  calc
    (∑ s : ZMod N, ‖∑ r : ZMod N, progressionTailProduct f s r‖ ^ 2) =
        ‖∑ u : ZMod N,
          progressionAverage (progressionTailDifference f u)‖ := by
      rw [← henergy]
      simp only [T]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      positivity
    _ ≤ ∑ u : ZMod N, ‖progressionAverage (progressionTailDifference f u)‖ :=
      norm_sum_le _ _

private lemma progression_cauchy_step {N n : Nat} [NeZero N]
    (f : Fin (n + 1) → ZMod N → Complex) (hf : DiscValued (f 0)) :
    ‖progressionAverage f‖ ^ 2 ≤
      (N : Real) * ∑ u : ZMod N, ‖progressionAverage (progressionTailDifference f u)‖ := by
  let B : ZMod N → Complex := fun s ↦
    ∑ r : ZMod N, progressionTailProduct f s r
  have hsplit : progressionAverage f = ∑ s : ZMod N, f 0 s * B s := by
    simpa only [B] using progressionAverage_split f
  have htriangle : ‖∑ s : ZMod N, f 0 s * B s‖ ≤
      ∑ s : ZMod N, ‖f 0 s * B s‖ := norm_sum_le _ _
  have hcauchy := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (ZMod N)))
    (f := fun s : ZMod N ↦ ‖f 0 s * B s‖)
  calc
    ‖progressionAverage f‖ ^ 2 = ‖∑ s : ZMod N, f 0 s * B s‖ ^ 2 := by rw [hsplit]
    _ ≤ (∑ s : ZMod N, ‖f 0 s * B s‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htriangle 2
    _ ≤ (N : Real) * ∑ s : ZMod N, ‖f 0 s * B s‖ ^ 2 := by
      simpa [ZMod.card] using hcauchy
    _ ≤ (N : Real) * ∑ s : ZMod N, ‖B s‖ ^ 2 := by
      gcongr with s
      rw [norm_mul]
      nlinarith [hf s, norm_nonneg (f 0 s), norm_nonneg (B s)]
    _ ≤ (N : Real) *
        ∑ u : ZMod N, ‖progressionAverage (progressionTailDifference f u)‖ := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [B] using progressionTail_energy f) (by positivity)

private lemma sum_rpow_le_rpow_average {N : Nat} [NeZero N]
    (beta : ZMod N → Real) (alpha p : Real)
    (hbeta : ∀ u, 0 ≤ beta u) (hsum : (∑ u, beta u) = alpha * N)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ u : ZMod N, beta u ^ p) ≤ alpha ^ p * N := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hjensen := (Real.concaveOn_rpow hp0 hp1).le_map_sum
    (t := (Finset.univ : Finset (ZMod N)))
    (w := fun _ : ZMod N ↦ (N : Real)⁻¹)
    (p := beta)
    (fun _ _ ↦ by positivity)
    (by simp [ZMod.card, hN.ne'])
    (fun u _ ↦ hbeta u)
  have hscaled :
      (N : Real)⁻¹ * ∑ u : ZMod N, beta u ^ p ≤ alpha ^ p := by
    simpa only [smul_eq_mul, inv_mul_eq_div, ← Finset.sum_div, hsum,
      mul_div_cancel_right₀ _ hN.ne'] using hjensen
  calc
    (∑ u : ZMod N, beta u ^ p) =
        (N : Real) * ((N : Real)⁻¹ * ∑ u : ZMod N, beta u ^ p) := by
      field_simp
    _ ≤ (N : Real) * alpha ^ p := mul_le_mul_of_nonneg_left hscaled hN.le
    _ = alpha ^ p * N := by ring

private lemma le_rpow_mul_of_sq_le {alpha p x C : Real}
    (ha0 : 0 ≤ alpha) (_hp0 : 0 ≤ p) (hx0 : 0 ≤ x) (hC0 : 0 ≤ C)
    (h : x ^ 2 ≤ alpha ^ p * C ^ 2) :
    x ≤ alpha ^ (p / 2) * C := by
  apply (sq_le_sq₀ hx0 (mul_nonneg (Real.rpow_nonneg ha0 _) hC0)).mp
  calc
    x ^ 2 ≤ alpha ^ p * C ^ 2 := h
    _ = (alpha ^ (p / 2) * C) ^ 2 := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha0]
      congr 1
      ring

private lemma theorem_3_2_induction {N k : Nat} [NeZero N] [Fact N.Prime]
    (hk2 : 2 ≤ k) (hkN : k ≤ N)
    (f : Fin k → ZMod N → Complex) (hf : ∀ i, DiscValued (f i))
    (alpha : Real) (ha0 : 0 ≤ alpha)
    (hu : ∀ i : Fin k, (i : Nat) + 1 = k →
      UniformOfDegree (f i) alpha (k - 2)) :
    ‖progressionAverage f‖ ≤
      alpha ^ ((1 : Real) / (2 : Real) ^ (k - 1)) * (N : Real) ^ 2 := by
  induction k using Nat.strong_induction_on generalizing alpha with
  | h k ih =>
      by_cases ha1 : alpha ≤ 1
      · by_cases hk : k = 2
        · subst k
          have hfirst : ‖∑ s : ZMod N, f 0 s‖ ≤ (N : Real) := by
            calc
              ‖∑ s : ZMod N, f 0 s‖ ≤ ∑ s : ZMod N, ‖f 0 s‖ := norm_sum_le _ _
              _ ≤ ∑ _s : ZMod N, (1 : Real) := by
                apply Finset.sum_le_sum
                intro s _
                exact hf 0 s
              _ = (N : Real) := by simp [ZMod.card]
          have hlast : UniformOfDegree (f 1) alpha 0 := hu 1 (by omega)
          have hlastSum : ‖∑ s : ZMod N, f 1 s‖ ^ 2 ≤ alpha * (N : Real) ^ 2 := by
            simpa [UniformOfDegree, Point, cubeDifference, iteratedDifference] using hlast
          have hfirstSq : ‖∑ s : ZMod N, f 0 s‖ ^ 2 ≤ (N : Real) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hfirst 2
          have hsq : ‖progressionAverage f‖ ^ 2 ≤
              alpha * ((N : Real) ^ 2) ^ 2 := by
            rw [progressionAverage_two_factor, norm_mul, mul_pow]
            calc
              ‖∑ s : ZMod N, f 0 s‖ ^ 2 * ‖∑ t : ZMod N, f 1 t‖ ^ 2 ≤
                  (N : Real) ^ 2 * (alpha * (N : Real) ^ 2) :=
                mul_le_mul hfirstSq hlastSum (sq_nonneg _) (by positivity)
              _ = alpha * ((N : Real) ^ 2) ^ 2 := by ring
          have hsq' : ‖progressionAverage f‖ ^ 2 ≤
              alpha ^ (1 : Real) * ((N : Real) ^ 2) ^ 2 := by
            simpa using hsq
          simpa using le_rpow_mul_of_sq_le ha0 (by norm_num : (0 : Real) ≤ 1)
            (norm_nonneg _) (by positivity : (0 : Real) ≤ (N : Real) ^ 2) hsq'
        · have hk3 : 3 ≤ k := by omega
          obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          have hn2 : 2 ≤ n := by omega
          have hnN : n ≤ N := by omega
          have hnltN : n < N := by omega
          have hlast : UniformOfDegree (f (Fin.last n)) alpha (n - 1) := by
            have := hu (Fin.last n) (by simp)
            convert this using 1
            all_goals omega
          have hconditions := lemma_3_1_holds N (n - 1) (f (Fin.last n))
            (by omega) (hf (Fin.last n)) alpha 0 0 ha0 ha1
            (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          have hiv : higherUniformConditioniv (f (Fin.last n)) alpha (n - 1) :=
            hconditions.2.2.1.mp (hconditions.1.mp hlast)
          rcases hiv with ⟨beta, hbeta, hbetaSum, hbetaUniform⟩
          let p : Real := 1 / (2 : Real) ^ (n - 1)
          have hp0 : 0 ≤ p := by positivity
          have hp1 : p ≤ 1 := by
            dsimp [p]
            exact (div_le_one (by positivity : (0 : Real) < 2 ^ (n - 1))).2
              (one_le_pow₀ (by norm_num))
          have hn0 : (n : ZMod N) ≠ 0 := by
            intro hn
            exact Nat.not_dvd_of_pos_of_lt (by omega) hnltN
              ((ZMod.natCast_eq_zero_iff n N).mp hn)
          have hpowerSum :
              (∑ u : ZMod N, beta ((n : ZMod N) * u) ^ p) ≤
                alpha ^ p * N := by
            calc
              (∑ u : ZMod N, beta ((n : ZMod N) * u) ^ p) =
                  ∑ v : ZMod N, beta v ^ p := by
                exact Equiv.sum_comp (Equiv.mulLeft₀ (n : ZMod N) hn0)
                  (fun v : ZMod N ↦ beta v ^ p)
              _ ≤ alpha ^ p * N :=
                sum_rpow_le_rpow_average beta alpha p (fun u ↦ (hbeta u).1)
                  hbetaSum hp0 hp1
          have havg (u : ZMod N) :
              ‖progressionAverage (progressionTailDifference f u)‖ ≤
                beta ((n : ZMod N) * u) ^ p * (N : Real) ^ 2 := by
            apply ih n (by omega) hn2 hnN
              (progressionTailDifference f u)
              (progressionTailDifference_discValued f hf u)
              (beta ((n : ZMod N) * u)) (hbeta _).1
            intro i hi
            have hisucc : i.succ = Fin.last n := by
              apply Fin.ext
              simp only [Fin.val_succ, Fin.val_last]
              omega
            have hlocal := hbetaUniform ((n : ZMod N) * u)
            have hcoeff : ((i : Nat) : ZMod N) + 1 = (n : ZMod N) := by
              rw [← Nat.cast_one, ← Nat.cast_add, hi]
            simp only [progressionTailDifference]
            rw [hisucc, hcoeff]
            convert hlocal using 1
            all_goals omega
          have hsq : ‖progressionAverage f‖ ^ 2 ≤
              alpha ^ p * ((N : Real) ^ 2) ^ 2 := by
            calc
              ‖progressionAverage f‖ ^ 2 ≤
                  (N : Real) * ∑ u : ZMod N,
                    ‖progressionAverage (progressionTailDifference f u)‖ :=
                progression_cauchy_step f (hf 0)
              _ ≤ (N : Real) * ∑ u : ZMod N,
                    (beta ((n : ZMod N) * u) ^ p * (N : Real) ^ 2) := by
                gcongr with u
                exact havg u
              _ = (N : Real) *
                    ((∑ u : ZMod N, beta ((n : ZMod N) * u) ^ p) *
                      (N : Real) ^ 2) := by rw [Finset.sum_mul]
              _ ≤ (N : Real) *
                    ((alpha ^ p * (N : Real)) * (N : Real) ^ 2) := by
                gcongr
              _ = alpha ^ p * ((N : Real) ^ 2) ^ 2 := by ring
          have hroot := le_rpow_mul_of_sq_le ha0 hp0 (norm_nonneg _)
            (by positivity : (0 : Real) ≤ (N : Real) ^ 2) hsq
          have hexp : p / 2 = (1 : Real) / (2 : Real) ^ n := by
            dsimp [p]
            have hpow : (2 : Real) ^ n = (2 : Real) ^ (n - 1) * 2 := by
              calc
                (2 : Real) ^ n = (2 : Real) ^ ((n - 1) + 1) := by congr 1; omega
                _ = (2 : Real) ^ (n - 1) * 2 := by rw [pow_succ]
            rw [hpow]
            ring
          simpa only [Nat.succ_sub_one, hexp] using hroot
      · have ha1' : 1 ≤ alpha := le_of_not_ge ha1
        have hexp0 : 0 ≤ (1 : Real) / (2 : Real) ^ (k - 1) := by positivity
        calc
          ‖progressionAverage f‖ ≤ (N : Real) ^ 2 := progressionAverage_trivial f hf
          _ ≤ alpha ^ ((1 : Real) / (2 : Real) ^ (k - 1)) * (N : Real) ^ 2 := by
            have := Real.one_le_rpow ha1' hexp0
            nlinarith [sq_nonneg ((N : Real) ^ 2)]

/-- **Theorem 3.2.** Generalized von Neumann bound for progression averages,
in the corrected prime-modulus range `2 ≤ k ≤ N`. -/
theorem theorem_3_2_holds : theorem_3_2 := by
  intro N k _ _ hk2 hkN f hf alpha ha0 hu
  exact theorem_3_2_induction hk2 hkN f hf alpha ha0 hu

end LeanProofs.GowersSzemeredi
