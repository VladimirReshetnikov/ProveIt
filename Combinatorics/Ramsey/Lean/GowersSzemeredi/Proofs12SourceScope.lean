import GowersSzemeredi.Proofs12

/-! Source-scope checks for weighted simultaneous additivity. Negative alpha
makes the fourth-power conclusion false; zero alpha is valid and needs no
Fourier argument. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The source reading without any sign restriction on alpha. -/
def proposition_12_1_unrestricted_alpha : Prop :=
  ∀ (N p : Nat) [NeZero N] (lambda : ZMod N → Real)
      (f : Fin p → ZMod N → Complex) (phi : Fin p → ZMod N → ZMod N)
      (alpha : Real),
    (∀ k, 0 ≤ lambda k) → (∀ i, DiscValued (f i)) →
    alpha * (N : Real) ^ (2 * p + 1) ≤
      ∑ k : ZMod N, lambda k *
        ∏ i : Fin p, ‖fourier (difference (f i) k) (phi i k)‖ ^ 2 →
    alpha ^ 4 * (N : Real) ^ 3 ≤
      simultaneouslyAdditiveWeight lambda phi

/-- The sharp nonnegative sign convention, including alpha=0. -/
def proposition_12_1_nonnegative_alpha : Prop :=
  ∀ (N p : Nat) [NeZero N] (lambda : ZMod N → Real)
      (f : Fin p → ZMod N → Complex) (phi : Fin p → ZMod N → ZMod N)
      (alpha : Real),
    0 ≤ alpha → (∀ k, 0 ≤ lambda k) → (∀ i, DiscValued (f i)) →
    alpha * (N : Real) ^ (2 * p + 1) ≤
      ∑ k : ZMod N, lambda k *
        ∏ i : Fin p, ‖fourier (difference (f i) k) (phi i k)‖ ^ 2 →
    alpha ^ 4 * (N : Real) ^ 3 ≤
      simultaneouslyAdditiveWeight lambda phi

/-- At the prime N=2, p=1, zero weights and alpha=-1, the premise holds but
its claimed weighted quadruple count would be at least eight. -/
theorem proposition_12_1_negative_alpha_counterexample :
    ¬ proposition_12_1_unrestricted_alpha := by
  intro h
  have hbad := h 2 1 (fun _ => 0) (fun _ _ => 0)
    (fun _ _ => 0) (-1) (by intro k; norm_num)
    (by intro i; simp [DiscValued]) (by simp)
  norm_num [simultaneouslyAdditiveWeight] at hbad

/-- The positive-alpha theorem extends to the endpoint alpha=0. -/
theorem proposition_12_1_nonnegative_alpha_holds :
    proposition_12_1_nonnegative_alpha := by
  intro N p _ lambda f phi alpha ha hlambda hf hlarge
  rcases eq_or_lt_of_le ha with hzero | hpos
  · subst alpha
    simp only [zero_pow (by norm_num : (4 : Nat) ≠ 0), zero_mul]
    unfold simultaneouslyAdditiveWeight
    apply Finset.sum_nonneg
    intro q _
    split_ifs
    · have h0 := hlambda (q 0)
      have h1 := hlambda (q 1)
      have h2 := hlambda (q 2)
      have h3 := hlambda (q 3)
      positivity
    · exact le_refl 0
  · exact proposition_12_1_holds N p lambda f phi alpha hpos hlambda hf hlarge

end LeanProofs.GowersSzemeredi
