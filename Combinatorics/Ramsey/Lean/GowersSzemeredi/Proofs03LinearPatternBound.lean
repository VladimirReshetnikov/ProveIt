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
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  simp only [linearPatternTailProduct, Fin.prod_univ_one, linearPatternTailCoefficients]
  exact Equiv.sum_comp ((Equiv.mulLeft₀ (c 1 - c 0) hd).trans (Equiv.subLeft s)) (f 1)

theorem linearPattern_uniform_last_bound {N k : Nat} [NeZero N] [Fact N.Prime]
    (hk2 : 2 ≤ k)
    (c : Fin k → ZMod N) (hc : Function.Injective c)
    (f : Fin k → ZMod N → Complex) (hf : ∀ i, DiscValued (f i))
    (alpha : Real) (ha0 : 0 ≤ alpha)
    (hu : ∀ i : Fin k, (i : Nat) + 1 = k →
      UniformOfDegree (f i) alpha (k - 2)) :
    ‖linearPatternAverage c f‖ ≤
      alpha ^ ((1 : Real) / (2 : Real) ^ (k - 1)) * (N : Real) ^ 2 := by
  rcases lt_or_ge 1 alpha with ha1 | ha1
  · exact (linearPatternAverage_trivial c f hf).trans
      (le_mul_of_one_le_left (by positivity) (Real.one_le_rpow ha1.le (by positivity)))
  induction k, hk2 using Nat.le_induction generalizing alpha with
  | base =>
    have h0 : ‖∑ s, f 0 s‖ ≤ N := (norm_sum_le_of_le _ fun s _ => hf 0 s).trans (by simp)
    have h1 : ‖∑ s, f 1 s‖ ^ 2 ≤ alpha * (N : Real) ^ 2 := by
      simpa [UniformOfDegree, Point, cubeDifference, iteratedDifference] using hu 1 (by omega)
    have hsq : ‖linearPatternAverage c f‖ ^ 2 ≤ alpha ^ (1 : Real) * ((N : Real) ^ 2) ^ 2 := by
      rw [linearPatternAverage_two_factor c hc, norm_mul, mul_pow, Real.rpow_one]
      calc _ ≤ (N : Real) ^ 2 * (alpha * (N : Real) ^ 2) := by gcongr
        _ = _ := by ring
    simpa using le_rpow_mul_of_sq_le ha0 zero_le_one (norm_nonneg _) (by positivity) hsq
  | succ n hn ih =>
    have h31 := lemma_3_1_holds N (n - 1) (f (Fin.last n)) (by omega) (hf _) alpha 0 0 ha0 ha1
      le_rfl zero_le_one le_rfl zero_le_one
    obtain ⟨beta, hbeta, hsum, hunif⟩ := h31.2.2.1.mp (h31.1.mp (by
      convert hu (Fin.last n) (by simp) using 1; omega))
    let p : Real := 1 / 2 ^ (n - 1)
    have hn0 : c (Fin.last n) - c 0 ≠ 0 :=
      sub_ne_zero.mpr (hc.ne (Fin.ne_of_val_ne (by simp; omega)))
    have hpow : (∑ u : ZMod N, beta ((c (Fin.last n) - c 0) * u) ^ p) ≤ alpha ^ p * N :=
      (Equiv.sum_comp (Equiv.mulLeft₀ _ hn0) (beta · ^ p)).le.trans
        (sum_rpow_le_rpow_average beta alpha p (fun u => (hbeta u).1) hsum (by positivity)
          (div_le_one_of_le₀ (one_le_pow₀ one_le_two) (by positivity)))
    have havg (u : ZMod N) := ih (linearPatternTailCoefficients c)
      (fun i j hij => Fin.succ_injective _ (hc (sub_left_inj.mp hij)))
      (linearPatternTailDifference c f u) (fun i => difference_discValued (hf i.succ) _)
      (beta ((c (Fin.last n) - c 0) * u)) (hbeta _).1 (fun i hi => by
        simp only [linearPatternTailDifference, linearPatternTailCoefficients,
          show i.succ = Fin.last n from Fin.ext (by simpa using hi)]
        convert hunif ((c (Fin.last n) - c 0) * u) using 1; omega) (hbeta _).2
    have hsq : ‖linearPatternAverage c f‖ ^ 2 ≤ alpha ^ p * ((N : Real) ^ 2) ^ 2 := calc
      _ ≤ (N : Real) * ∑ u : ZMod N, beta ((c (Fin.last n) - c 0) * u) ^ p * (N : Real) ^ 2 :=
        (linearPattern_cauchy_step c f (hf 0)).trans (by gcongr with u; exact havg u)
      _ ≤ (N : Real) * (alpha ^ p * N * (N : Real) ^ 2) := by rw [← Finset.sum_mul]; gcongr
      _ = _ := by ring
    rw [Nat.add_sub_cancel, show (1 : Real) / 2 ^ n = 1 / 2 ^ (n - 1) / 2 by
      rw [div_div, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]]
    exact le_rpow_mul_of_sq_le ha0 (by positivity) (norm_nonneg _) (by positivity) hsq

end LeanProofs.GowersSzemeredi
