import GowersSzemeredi.Proofs03Equivalences
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-! Cauchy--Schwarz reduction for arbitrary distinct progression coefficients.
This permits a uniform factor in any position in the relative counting step. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ZMod
namespace LeanProofs.GowersSzemeredi

lemma sum_rpow_le_rpow_average {N : Nat} [NeZero N]
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

lemma le_rpow_mul_of_sq_le {alpha p x C : Real}
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
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Fin.prod_univ_succ]
  simp only [add_sub_cancel_right]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  dsimp [linearPatternTailCoefficients]
  ring

theorem linearPatternTail_energy {N n : Nat} [NeZero N]
    (c : Fin (n + 1) → ZMod N) (f : Fin (n + 1) → ZMod N → Complex) :
    (∑ s : ZMod N,
        ‖∑ r : ZMod N, linearPatternTailProduct c f s r‖ ^ 2) ≤
      ∑ u : ZMod N, ‖linearPatternAverage (linearPatternTailCoefficients c) (linearPatternTailDifference c f u)‖ := by
  let T : ZMod N → ZMod N → Complex := linearPatternTailProduct c f
  -- each difference average is a shifted autocorrelation of `T`
  have hA (u : ZMod N) : linearPatternAverage (linearPatternTailCoefficients c)
      (linearPatternTailDifference c f u) = ∑ r, ∑ s, T s r * star (T s (r + u)) := by
    simp only [linearPatternAverage, linearPatternTailDifference, difference, T,
      linearPatternTailProduct, star_prod, ← Finset.prod_mul_distrib, mul_add, sub_sub]
  -- so the averages add up to `∑ₛ |∑ᵣ T s r|²` (substitute `t = r + u`)
  have henergy : ∑ u, linearPatternAverage (linearPatternTailCoefficients c)
      (linearPatternTailDifference c f u) = ((∑ s, ‖∑ r, T s r‖ ^ 2 : Real) : Complex) := by
    calc _ = ∑ r, ∑ s, ∑ u, T s r * star (T s (r + u)) := by
          simp_rw [hA]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun r _ => Finset.sum_comm
      _ = ∑ r, ∑ s, T s r * star (∑ t, T s t) := by
          refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
          rw [star_sum, Finset.mul_sum]
          exact Fintype.sum_equiv (Equiv.addLeft r) _ _ fun _ => rfl
      _ = _ := by
          rw [Finset.sum_comm]
          push_cast
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [← Finset.sum_mul, Complex.star_def, Complex.mul_conj']
  refine Eq.trans_le ?_ (norm_sum_le _ _)
  rw [henergy, Complex.norm_of_nonneg (Finset.sum_nonneg fun s _ => sq_nonneg ‖∑ r, T s r‖)]

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
