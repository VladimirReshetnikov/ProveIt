import GowersSzemeredi.Proofs03LinearPatternStep

/-! Generalized von Neumann bound for distinct linear-pattern coefficients.
The uniform factor is initially placed last; permutation invariance then
allows any position without increasing its uniformity degree. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ZMod
namespace LeanProofs.GowersSzemeredi

theorem linearPatternAverage_trivial {N k : Nat} [NeZero N]
    (c : Fin k → ZMod N) (f : Fin k → ZMod N → Complex) (hf : ∀ i, DiscValued (f i)) :
    ‖linearPatternAverage c f‖ ≤ (N : Real) ^ 2 := by
  calc
    ‖linearPatternAverage c f‖ ≤
        ∑ r : ZMod N, ‖∑ s : ZMod N, ∏ i, f i (s - c i * r)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _r : ZMod N, ∑ _s : ZMod N, (1 : Real) := by
      apply Finset.sum_le_sum
      intro r _
      calc
        ‖∑ s : ZMod N, ∏ i, f i (s - c i * r)‖ ≤
            ∑ s : ZMod N, ‖∏ i, f i (s - c i * r)‖ := norm_sum_le _ _
        _ ≤ ∑ _s : ZMod N, (1 : Real) := by
          apply Finset.sum_le_sum
          intro s _
          rw [norm_prod]
          exact Finset.prod_le_one (fun _ _ ↦ norm_nonneg _)
            (fun i _ ↦ hf i _)
    _ = (N : Real) ^ 2 := by simp [ZMod.card, pow_two]

theorem linearPatternAverage_two_factor {N : Nat} [NeZero N] [Fact N.Prime]
    (c : Fin 2 → ZMod N) (hc : Function.Injective c) (f : Fin 2 → ZMod N → Complex) :
    linearPatternAverage c f = (∑ s, f 0 s) * (∑ t, f 1 t) := by
  have hd : c 1 - c 0 ≠ 0 := sub_ne_zero.mpr (fun h => by simpa using hc h)
  rw [linearPatternAverage_split, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  simp only [linearPatternTailProduct, Fin.prod_univ_one, linearPatternTailCoefficients]
  exact Equiv.sum_comp ((Equiv.mulLeft₀ (c 1 - c 0) hd).trans (Equiv.subLeft s)) (f 1)

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

theorem linearPattern_uniform_last_bound {N k : Nat} [NeZero N] [Fact N.Prime]
    (hk2 : 2 ≤ k)
    (c : Fin k → ZMod N) (hc : Function.Injective c)
    (f : Fin k → ZMod N → Complex) (hf : ∀ i, DiscValued (f i))
    (alpha : Real) (ha0 : 0 ≤ alpha)
    (hu : ∀ i : Fin k, (i : Nat) + 1 = k →
      UniformOfDegree (f i) alpha (k - 2)) :
    ‖linearPatternAverage c f‖ ≤
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
          have hsq : ‖linearPatternAverage c f‖ ^ 2 ≤
              alpha * ((N : Real) ^ 2) ^ 2 := by
            rw [linearPatternAverage_two_factor c hc, norm_mul, mul_pow]
            calc
              ‖∑ s : ZMod N, f 0 s‖ ^ 2 * ‖∑ t : ZMod N, f 1 t‖ ^ 2 ≤
                  (N : Real) ^ 2 * (alpha * (N : Real) ^ 2) :=
                mul_le_mul hfirstSq hlastSum (sq_nonneg _) (by positivity)
              _ = alpha * ((N : Real) ^ 2) ^ 2 := by ring
          have hsq' : ‖linearPatternAverage c f‖ ^ 2 ≤
              alpha ^ (1 : Real) * ((N : Real) ^ 2) ^ 2 := by
            simpa using hsq
          simpa using le_rpow_mul_of_sq_le ha0 (by norm_num : (0 : Real) ≤ 1)
            (norm_nonneg _) (by positivity : (0 : Real) ≤ (N : Real) ^ 2) hsq'
        · have hk3 : 3 ≤ k := by omega
          obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          have hn2 : 2 ≤ n := by omega
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
          have hn0 : c (Fin.last n) - c 0 ≠ 0 := by
            apply sub_ne_zero.mpr
            intro hh
            have hi := congrArg Fin.val (hc hh)
            simp only [Fin.val_last, Fin.val_zero] at hi
            omega
          have hct : Function.Injective (linearPatternTailCoefficients c) := by
            intro i j hij
            exact Fin.succ_injective _ (hc (sub_left_inj.mp hij))
          have hpowerSum :
              (∑ u : ZMod N, beta ((c (Fin.last n) - c 0) * u) ^ p) ≤
                alpha ^ p * N := by
            calc
              (∑ u : ZMod N, beta ((c (Fin.last n) - c 0) * u) ^ p) =
                  ∑ v : ZMod N, beta v ^ p := by
                exact Equiv.sum_comp (Equiv.mulLeft₀ (c (Fin.last n) - c 0) hn0)
                  (fun v : ZMod N ↦ beta v ^ p)
              _ ≤ alpha ^ p * N :=
                sum_rpow_le_rpow_average beta alpha p (fun u ↦ (hbeta u).1)
                  hbetaSum hp0 hp1
          have havg (u : ZMod N) :
              ‖linearPatternAverage (linearPatternTailCoefficients c) (linearPatternTailDifference c f u)‖ ≤
                beta ((c (Fin.last n) - c 0) * u) ^ p * (N : Real) ^ 2 := by
            apply ih n (by omega) hn2 (linearPatternTailCoefficients c) hct
              (linearPatternTailDifference c f u)
              (fun i => difference_discValued (hf i.succ) _)
              (beta ((c (Fin.last n) - c 0) * u)) (hbeta _).1
            intro i hi
            have hisucc : i.succ = Fin.last n := by
              apply Fin.ext
              simp only [Fin.val_succ, Fin.val_last]
              omega
            have hlocal := hbetaUniform ((c (Fin.last n) - c 0) * u)
            simp only [linearPatternTailDifference, linearPatternTailCoefficients, hisucc]
            convert hlocal using 1
            all_goals omega
          have hsq : ‖linearPatternAverage c f‖ ^ 2 ≤
              alpha ^ p * ((N : Real) ^ 2) ^ 2 := by
            calc
              ‖linearPatternAverage c f‖ ^ 2 ≤
                  (N : Real) * ∑ u : ZMod N,
                    ‖linearPatternAverage (linearPatternTailCoefficients c) (linearPatternTailDifference c f u)‖ :=
                linearPattern_cauchy_step c f (hf 0)
              _ ≤ (N : Real) * ∑ u : ZMod N,
                    (beta ((c (Fin.last n) - c 0) * u) ^ p * (N : Real) ^ 2) := by
                gcongr with u
                exact havg u
              _ = (N : Real) *
                    ((∑ u : ZMod N, beta ((c (Fin.last n) - c 0) * u) ^ p) *
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
          ‖linearPatternAverage c f‖ ≤ (N : Real) ^ 2 := linearPatternAverage_trivial c f hf
          _ ≤ alpha ^ ((1 : Real) / (2 : Real) ^ (k - 1)) * (N : Real) ^ 2 := by
            have := Real.one_le_rpow ha1' hexp0
            nlinarith [sq_nonneg ((N : Real) ^ 2)]

end LeanProofs.GowersSzemeredi
