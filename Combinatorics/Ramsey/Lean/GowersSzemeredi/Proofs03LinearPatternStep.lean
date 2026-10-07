import GowersSzemeredi.Proofs03ProgressionAverage

/-! Cauchy--Schwarz reduction for arbitrary distinct progression coefficients.
This permits a uniform factor in any position in the relative counting step. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ZMod
namespace LeanProofs.GowersSzemeredi

def linearPatternAverage {N k : Nat} [NeZero N]
    (c : Fin k → ZMod N) (f : Fin k → ZMod N → Complex) : Complex :=
  ∑ r : ZMod N, ∑ s : ZMod N, ∏ i, f i (s - c i * r)

def linearPatternTailCoefficients {N n : Nat} (c : Fin (n + 1) → ZMod N) : Fin n → ZMod N :=
  fun i => c i.succ - c 0

def linearPatternTailDifference {N n : Nat} (c : Fin (n + 1) → ZMod N)
    (f : Fin (n + 1) → ZMod N → Complex) (u : ZMod N) : Fin n → ZMod N → Complex :=
  fun i => difference (f i.succ) (linearPatternTailCoefficients c i * u)

def linearPatternTailProduct {N n : Nat} (c : Fin (n + 1) → ZMod N)
    (f : Fin (n + 1) → ZMod N → Complex) (s r : ZMod N) : Complex :=
  ∏ i : Fin n, f i.succ (s - linearPatternTailCoefficients c i * r)

theorem linearPatternAverage_split {N n : Nat} [NeZero N]
    (c : Fin (n + 1) → ZMod N) (f : Fin (n + 1) → ZMod N → Complex) :
    linearPatternAverage c f =
      ∑ s : ZMod N, f 0 s * ∑ r : ZMod N, linearPatternTailProduct c f s r := by
  unfold linearPatternAverage
  have hshift (r : ZMod N) :
      (∑ s, ∏ i, f i (s - c i * r)) =
      ∑ s, ∏ i, f i ((s + c 0 * r) - c i * r) :=
    (Equiv.sum_comp (Equiv.addRight (c 0 * r)) (fun s => ∏ i, f i (s - c i * r))).symm
  simp_rw [hshift]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Fin.prod_univ_succ]
  simp only [add_sub_cancel_right]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  dsimp [linearPatternTailCoefficients]
  ring

theorem linearPatternTail_energy {N n : Nat} [NeZero N]
    (c : Fin (n + 1) → ZMod N) (f : Fin (n + 1) → ZMod N → Complex) :
    (∑ s : ZMod N,
        ‖∑ r : ZMod N, linearPatternTailProduct c f s r‖ ^ 2) ≤
      ∑ u : ZMod N, ‖linearPatternAverage (linearPatternTailCoefficients c) (linearPatternTailDifference c f u)‖ := by
  let T : ZMod N → ZMod N → Complex := linearPatternTailProduct c f
  have henergy :
      ((∑ s : ZMod N, ‖∑ r : ZMod N, T s r‖ ^ 2 : Real) : Complex) =
        ∑ u : ZMod N, linearPatternAverage (linearPatternTailCoefficients c) (linearPatternTailDifference c f u) := by
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
      _ = ∑ u : ZMod N,
          linearPatternAverage (linearPatternTailCoefficients c) (linearPatternTailDifference c f u) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u _
        unfold linearPatternAverage
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro s _
        simp only [T, linearPatternTailProduct, linearPatternTailDifference,
          difference, star_prod]
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i _
        congr 2
        ring
  calc
    (∑ s : ZMod N, ‖∑ r : ZMod N, linearPatternTailProduct c f s r‖ ^ 2) =
        ‖∑ u : ZMod N,
          linearPatternAverage (linearPatternTailCoefficients c) (linearPatternTailDifference c f u)‖ := by
      rw [← henergy]
      simp only [T]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      positivity
    _ ≤ ∑ u : ZMod N, ‖linearPatternAverage (linearPatternTailCoefficients c) (linearPatternTailDifference c f u)‖ :=
      norm_sum_le _ _

theorem linearPattern_cauchy_step {N n : Nat} [NeZero N]
    (c : Fin (n + 1) → ZMod N) (f : Fin (n + 1) → ZMod N → Complex) (hf : DiscValued (f 0)) :
    ‖linearPatternAverage c f‖ ^ 2 ≤
      (N : Real) * ∑ u : ZMod N, ‖linearPatternAverage (linearPatternTailCoefficients c) (linearPatternTailDifference c f u)‖ := by
  let B : ZMod N → Complex := fun s ↦
    ∑ r : ZMod N, linearPatternTailProduct c f s r
  have hsplit : linearPatternAverage c f = ∑ s : ZMod N, f 0 s * B s := by
    simpa only [B] using linearPatternAverage_split c f
  have htriangle : ‖∑ s : ZMod N, f 0 s * B s‖ ≤
      ∑ s : ZMod N, ‖f 0 s * B s‖ := norm_sum_le _ _
  have hcauchy := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (ZMod N)))
    (f := fun s : ZMod N ↦ ‖f 0 s * B s‖)
  calc
    ‖linearPatternAverage c f‖ ^ 2 = ‖∑ s : ZMod N, f 0 s * B s‖ ^ 2 := by rw [hsplit]
    _ ≤ (∑ s : ZMod N, ‖f 0 s * B s‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htriangle 2
    _ ≤ (N : Real) * ∑ s : ZMod N, ‖f 0 s * B s‖ ^ 2 := by
      simpa [ZMod.card] using hcauchy
    _ ≤ (N : Real) * ∑ s : ZMod N, ‖B s‖ ^ 2 := by
      gcongr with s
      rw [norm_mul]
      nlinarith [hf s, norm_nonneg (f 0 s), norm_nonneg (B s)]
    _ ≤ (N : Real) *
        ∑ u : ZMod N, ‖linearPatternAverage (linearPatternTailCoefficients c) (linearPatternTailDifference c f u)‖ := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [B] using linearPatternTail_energy c f) (by positivity)


end LeanProofs.GowersSzemeredi
