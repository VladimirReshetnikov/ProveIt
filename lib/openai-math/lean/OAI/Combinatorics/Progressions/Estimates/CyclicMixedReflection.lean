/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.AnchoredReflectedFamily
import OAI.Combinatorics.Progressions.Fourier.QuadraticFrequencyCoordinates

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def tripleCyclicEmbed {N : ℕ} (x : ZMod N) : ZMod (3 * N) := (x.val : ℕ)

theorem tripleCyclicEmbed_injective {N : ℕ} [NeZero N] :
    Function.Injective (tripleCyclicEmbed (N := N)) := by
  intro x y hxy
  have hN := NeZero.pos N
  have hx : x.val < 3 * N := by have := x.val_lt; omega
  have hy : y.val < 3 * N := by have := y.val_lt; omega
  have hv := congrArg ZMod.val hxy
  simp only [tripleCyclicEmbed, ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy] at hv
  exact ZMod.val_injective N hv

theorem tripleCyclicEmbed_expect_le {N : ℕ} [NeZero N]
    (a : ZMod (3 * N)) (g : ZMod (3 * N) → ℝ) (hg : ∀ t, 0 ≤ g t) :
    (𝔼 y : ZMod N, g (a - tripleCyclicEmbed y)) ≤ 3 * (𝔼 t, g t) := by
  classical
  have he : Function.Injective (fun y : ZMod N => a - tripleCyclicEmbed y) := by
    intro x y hxy
    apply tripleCyclicEmbed_injective
    exact sub_right_inj.mp hxy
  have hsum : (∑ y : ZMod N, g (a - tripleCyclicEmbed y)) ≤ ∑ t, g t := by
    calc
      _ = ∑ t ∈ Finset.univ.image (fun y : ZMod N => a - tripleCyclicEmbed y), g t := by
        rw [Finset.sum_image he.injOn]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun t _ _ => hg t)
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card, ZMod.card, ZMod.card]
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  calc
    _ ≤ (∑ t, g t) / N := div_le_div_of_nonneg_right hsum hN.le
    _ = _ := by push_cast; field_simp

theorem tripleCyclicEmbed_pair_expect_le {N : ℕ} [NeZero N]
    (z : ZMod N) (g : ZMod (3 * N) → ℝ) (hg : ∀ t, 0 ≤ g t) :
    (𝔼 x : ZMod N, 𝔼 y : ZMod N,
      g (tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y)) ≤ 3 * (𝔼 t, g t) := by
  apply (Finset.expect_le_expect (fun x _ =>
    tripleCyclicEmbed_expect_le (tripleCyclicEmbed z - tripleCyclicEmbed x) g hg)).trans_eq
  exact Fintype.expect_const _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_remove_triple_interval {N : ℕ} [NeZero N]
    (z : ZMod N) (a : ZMod (3 * N)) (L : ℕ) (F : ZMod N → ZMod N → ℂ)
    (hF : ∀ x y, ‖F x y‖ ≤ 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hcorr : ρ ≤ ‖𝔼 x, 𝔼 y, F x y * finiteIndicator (cyclicInterval a L)
      (tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y)‖) :
    ∃ χ : AddChar (ZMod (3 * N)) ℂ, ρ ^ 2 / 48 ≤
      ‖𝔼 x, 𝔼 y, F x y * star (χ (tripleCyclicEmbed x)) * star (χ (tripleCyclicEmbed y))‖ := by
  let δ := ρ / 12
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith
  obtain ⟨v, c, _, herr, hmass, hsum⟩ := exists_cyclic_interval_fourier_smoothing a L hδ hδ1
  let D (x y : ZMod N) := tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y
  let I := finiteIndicator (cyclicInterval a L)
  have herror : ‖𝔼 x, 𝔼 y, F x y * (I (D x y) - v (D x y))‖ ≤ 6 * δ := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    calc
      _ ≤ 𝔼 x, 𝔼 y, ‖I (D x y) - v (D x y)‖ := by
        apply Finset.expect_le_expect
        intro x _
        apply (RCLike.norm_expect_le (K := ℂ)).trans
        apply Finset.expect_le_expect
        intro y _
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hF x y)
      _ ≤ 3 * (𝔼 t, ‖I t - v t‖) :=
        tripleCyclicEmbed_pair_expect_le z (fun t => ‖I t - v t‖) (fun _ => norm_nonneg _)
      _ ≤ 6 * δ := by linarith
  have hdiff : ‖(𝔼 x, 𝔼 y, F x y * I (D x y)) - (𝔼 x, 𝔼 y, F x y * v (D x y))‖ ≤ 6 * δ := by
    simpa only [mul_sub, Finset.expect_sub_distrib] using herror
  have htriangle : ‖𝔼 x, 𝔼 y, F x y * I (D x y)‖ ≤
      ‖𝔼 x, 𝔼 y, F x y * v (D x y)‖ +
        ‖(𝔼 x, 𝔼 y, F x y * I (D x y)) - (𝔼 x, 𝔼 y, F x y * v (D x y))‖ := by
    simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub
      (𝔼 x, 𝔼 y, F x y * v (D x y)) (𝔼 x, 𝔼 y, F x y * I (D x y))
  have hsmoothed : ρ / 2 ≤ ‖𝔼 x, 𝔼 y, F x y * v (D x y)‖ := by
    change ρ ≤ ‖𝔼 x, 𝔼 y, F x y * I (D x y)‖ at hcorr
    dsimp [δ] at hdiff
    linarith
  have heq : (𝔼 x, 𝔼 y, F x y * v (D x y)) =
      ∑ χ, c χ * (𝔼 x, 𝔼 y, F x y * χ (D x y)) := by
    calc
      _ = 𝔼 x, 𝔼 y, ∑ χ, c χ * (F x y * χ (D x y)) := by
        apply Finset.expect_congr rfl
        intro x _
        apply Finset.expect_congr rfl
        intro y _
        rw [hsum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro χ _
        ring
      _ = _ := by simp_rw [Finset.expect_sum_comm, ← Finset.mul_expect]
  obtain ⟨χ, hχ⟩ := exists_large_weighted_term c
    (fun χ => 𝔼 x, 𝔼 y, F x y * χ (D x y)) (by positivity : 0 < ρ / 2)
    (by positivity : 0 < 2 / δ) hmass (by rwa [← heq])
  have hthreshold : (ρ / 2) / (2 / δ) = ρ ^ 2 / 48 := by
    dsimp [δ]
    field_simp
    ring
  rw [hthreshold] at hχ
  have hfactor : (𝔼 x, 𝔼 y, F x y * χ (D x y)) =
      χ (tripleCyclicEmbed z) *
        (𝔼 x, 𝔼 y, F x y * star (χ (tripleCyclicEmbed x)) * star (χ (tripleCyclicEmbed y))) := by
    simp_rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro y _
    simp only [D, addChar_sub_star]
    ring
  rw [hfactor, norm_mul, AddChar.norm_apply, one_mul] at hχ
  exact ⟨χ, hχ⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def tripleCarryStart (N : ℕ) : Fin 3 → ℕ := ![0, 2 * N, N]

def tripleCarryInterval (N : ℕ) (k : Fin 3) : Finset (ZMod (3 * N)) :=
  cyclicInterval (tripleCarryStart N k : ZMod (3 * N)) N

theorem mem_tripleCarryInterval {N : ℕ} [NeZero N] (k : Fin 3) (v : ZMod (3 * N)) :
    v ∈ tripleCarryInterval N k ↔
      tripleCarryStart N k ≤ v.val ∧ v.val < tripleCarryStart N k + N := by
  have hend : tripleCarryStart N k + N ≤ 3 * N := by
    fin_cases k <;> simp [tripleCarryStart] <;> omega
  simpa only [tripleCarryInterval, Nat.add_sub_cancel_left] using
    mem_cyclicInterval_representatives (tripleCarryStart N k) (tripleCarryStart N k + N)
      (by omega) hend v

theorem sum_tripleCarry_indicator {N : ℕ} [NeZero N] (v : ZMod (3 * N)) :
    (∑ k : Fin 3, finiteIndicator (tripleCarryInterval N k) v) = 1 := by
  have hv := v.val_lt
  have hN := NeZero.pos N
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp only [finiteIndicator, mem_tripleCarryInterval]
  change (if 0 ≤ v.val ∧ v.val < 0 + N then (1 : ℂ) else 0) +
    ((if 2 * N ≤ v.val ∧ v.val < 2 * N + N then 1 else 0) +
      (if N ≤ v.val ∧ v.val < N + N then 1 else 0)) = 1
  simp only [Nat.zero_le, true_and, zero_add]
  by_cases h0 : v.val < N
  · have h1 : ¬(2 * N ≤ v.val ∧ v.val < 2 * N + N) := by omega
    have h2 : ¬(N ≤ v.val ∧ v.val < N + N) := by omega
    simp [h0, h1, h2]
  · by_cases h1 : v.val < 2 * N
    · have h2 : N ≤ v.val ∧ v.val < N + N := by omega
      have h3 : ¬(2 * N ≤ v.val ∧ v.val < 2 * N + N) := by omega
      simp [h0, h2, h3]
    · have h2 : 2 * N ≤ v.val ∧ v.val < 2 * N + N := by omega
      have h3 : ¬(N ≤ v.val ∧ v.val < N + N) := by omega
      simp [h0, h2, h3]

theorem triple_difference_val {N : ℕ} [NeZero N] (z x y : ZMod N) :
    ((tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y).val : ℤ) =
      if 0 ≤ (z.val : ℤ) - x.val - y.val then (z.val : ℤ) - x.val - y.val
      else (z.val : ℤ) - x.val - y.val + 3 * N := by
  let t : ℤ := (z.val : ℤ) - x.val - y.val
  have hN := NeZero.pos N
  have hz := z.val_lt
  have hx := x.val_lt
  have hy := y.val_lt
  have hlo : -(2 * (N : ℤ)) < t := by dsimp [t]; omega
  have hhi : t < (N : ℤ) := by dsimp [t]; omega
  have hcast : (t : ZMod (3 * N)) =
      tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y := by
    simp [t, tripleCyclicEmbed]
  rw [← hcast, ZMod.val_intCast]
  change t % (3 * (N : ℤ)) = if 0 ≤ t then t else t + 3 * N
  by_cases ht : 0 ≤ t
  · rw [ite_eq_left ht, Int.emod_eq_of_lt ht (by omega)]
  · rw [ite_eq_right ht]
    calc
      t % (3 * (N : ℤ)) = (t + 3 * N) % (3 * (N : ℤ)) := by simp
      _ = t + 3 * N := Int.emod_eq_of_lt (by omega) (by omega)

theorem tripleCarry_representative {N : ℕ} [NeZero N] (z x y : ZMod N) (k : Fin 3)
    (hk : tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y ∈ tripleCarryInterval N k) :
    ((z - x - y).val : ℤ) = (z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val := by
  let t : ℤ := (z.val : ℤ) - x.val - y.val
  have hN := NeZero.pos N
  have hz := z.val_lt
  have hx := x.val_lt
  have hy := y.val_lt
  have hm := triple_difference_val z x y
  have hk' := (mem_tripleCarryInterval k _).mp hk
  have hvalid : 0 ≤ t + (k.val : ℤ) * N ∧ t + (k.val : ℤ) * N < N := by
    change ((tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y).val : ℤ) =
      (if 0 ≤ t then t else t + 3 * N) at hm
    fin_cases k
    · change 0 ≤ (tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y).val ∧
        (tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y).val < 0 + N at hk'
      change 0 ≤ t + 0 * (N : ℤ) ∧ t + 0 * (N : ℤ) < N
      split_ifs at hm <;> dsimp [t] at * <;> omega
    · change 2 * N ≤ (tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y).val ∧
        (tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y).val < 2 * N + N at hk'
      change 0 ≤ t + 1 * (N : ℤ) ∧ t + 1 * (N : ℤ) < N
      split_ifs at hm <;> dsimp [t] at * <;> omega
    · change N ≤ (tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y).val ∧
        (tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y).val < N + N at hk'
      change 0 ≤ t + 2 * (N : ℤ) ∧ t + 2 * (N : ℤ) < N
      split_ifs at hm <;> dsimp [t] at * <;> omega
  have hcast : ((t + (k.val : ℤ) * N : ℤ) : ZMod N) = z - x - y := by
    simp [t]
  have hv := congrArg (fun v : ZMod N => (v.val : ℤ)) hcast
  rw [ZMod.val_intCast, Int.emod_eq_of_lt hvalid.1 hvalid.2] at hv
  rw [← hv]
  dsimp [t]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_unwrapped_family_reflected_correlation
    {T : Type*} [Fintype T] [Nonempty T] {N : ℕ} [NeZero N] {p : ℝ}
    (hp : 0 ≤ p) (R S : T → ℤ → ℤ → ℂ)
    (hR : ∀ t x n, ‖R t x n‖ ≤ 1) (hS : ∀ t y n, ‖S t y n‖ ≤ 1)
    (z : ZMod N) (b : T → ZMod N → ℂ) (hb : ∀ t x, ‖b t x‖ ≤ 1)
    (hcorr : Real.exp (-p) ≤ ‖𝔼 t, 𝔼 x : ZMod N, 𝔼 y : ZMod N,
      R t x.val (z - x - y).val * star (S t y.val (z - x - y).val) * b t x * star (b t y)‖) :
    ∃ (k : Fin 3) (A B : T → ℤ → ℂ),
      (∀ t n, ‖A t n‖ ≤ 1) ∧ (∀ t n, ‖B t n‖ ≤ 1) ∧
      Real.exp (-(2 * p + 10)) ≤ ‖𝔼 t, 𝔼 x : ZMod N, 𝔼 y : ZMod N,
        R t x.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val) *
          star (S t y.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val)) *
            A t x.val * B t y.val‖ := by
  let F (k : Fin 3) (x y : ZMod N) := 𝔼 t,
    R t x.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val) *
      star (S t y.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val)) * b t x * star (b t y)
  let G (t : T) (x y : ZMod N) :=
    R t x.val (z - x - y).val * star (S t y.val (z - x - y).val) * b t x * star (b t y)
  let D (x y : ZMod N) := tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y
  have hcomm (H : T → ZMod N → ZMod N → ℂ) :
      (𝔼 x, 𝔼 y, 𝔼 t, H t x y) = 𝔼 t, 𝔼 x, 𝔼 y, H t x y := by
    calc
      _ = 𝔼 x, 𝔼 t, 𝔼 y, H t x y := by
        apply Finset.expect_congr rfl
        intro x _
        exact Finset.expect_comm _ _ _
      _ = _ := Finset.expect_comm _ _ _
  have hF (k : Fin 3) (x y : ZMod N) : ‖F k x y‖ ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply (Finset.expect_le_expect (fun t _ => ?_)).trans_eq (Fintype.expect_const (1 : ℝ))
    simp only [norm_mul, norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hb t y)
    apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hb t x)
    exact (mul_le_of_le_one_left (norm_nonneg _) (hR t _ _)).trans (hS t _ _)
  have hterm (k : Fin 3) (x y : ZMod N) :
      F k x y * finiteIndicator (tripleCarryInterval N k) (D x y) =
        (𝔼 t, G t x y) * finiteIndicator (tripleCarryInterval N k) (D x y) := by
    by_cases hk : D x y ∈ tripleCarryInterval N k
    · have hr := tripleCarry_representative z x y k hk
      simp only [finiteIndicator, ite_eq_left hk, mul_one, F, G, hr]
    · simp only [finiteIndicator, ite_eq_right hk, mul_zero]
  have hpoint (x y : ZMod N) :
      (∑ k : Fin 3, F k x y * finiteIndicator (tripleCarryInterval N k) (D x y)) = 𝔼 t, G t x y := by
    simp_rw [hterm]
    rw [← Finset.mul_sum, sum_tripleCarry_indicator, mul_one]
  have hsum : (∑ k : Fin 3, 𝔼 x : ZMod N, 𝔼 y : ZMod N,
      F k x y * finiteIndicator (tripleCarryInterval N k) (D x y)) = 𝔼 t, 𝔼 x, 𝔼 y, G t x y := by
    rw [← hcomm G, ← Finset.expect_sum_comm]
    apply Finset.expect_congr rfl
    intro x _
    rw [← Finset.expect_sum_comm]
    exact Finset.expect_congr rfl (fun y _ => hpoint x y)
  obtain ⟨k, hk⟩ := exists_large_weighted_term (fun _ : Fin 3 => (1 : ℂ))
    (fun k => 𝔼 x : ZMod N, 𝔼 y : ZMod N,
      F k x y * finiteIndicator (tripleCarryInterval N k) (D x y))
    (Real.exp_pos (-p)) (by norm_num : (0 : ℝ) < 3) (by norm_num)
    (by simpa only [one_mul, hsum, G] using hcorr)
  have hρ1 : Real.exp (-p) / 3 ≤ 1 := by
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hp)
    linarith only [he]
  obtain ⟨χ, hχ⟩ := exists_remove_triple_interval z (tripleCarryStart N k) N (F k) (hF k)
    (by positivity : 0 < Real.exp (-p) / 3) hρ1 hk
  let A (t : T) (n : ℤ) := b t (n : ZMod N) * star (χ (n : ZMod (3 * N)))
  let B (t : T) (n : ℤ) := star (b t (n : ZMod N)) * star (χ (n : ZMod (3 * N)))
  have hAe (t : T) (x : ZMod N) : A t (x.val : ℤ) = b t x * star (χ (tripleCyclicEmbed x)) := by
    simp [A, tripleCyclicEmbed]
  have hBe (t : T) (y : ZMod N) : B t (y.val : ℤ) = star (b t y) * star (χ (tripleCyclicEmbed y)) := by
    simp [B, tripleCyclicEmbed]
  have hfinal : (𝔼 x, 𝔼 y, F k x y * star (χ (tripleCyclicEmbed x)) * star (χ (tripleCyclicEmbed y))) =
      𝔼 t, 𝔼 x : ZMod N, 𝔼 y : ZMod N,
        R t x.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val) *
          star (S t y.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val)) * A t x.val * B t y.val := by
    simp_rw [F, Finset.expect_mul, hcomm]
    apply Finset.expect_congr rfl
    intro t _
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro y _
    rw [hAe, hBe]
    ring
  have htwo : Real.exp (-p) ^ 2 = Real.exp (-(2 * p)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  have hthreshold : (Real.exp (-p) / 3) ^ 2 / 48 = Real.exp (-(2 * p)) / 432 := by
    rw [div_pow, htwo]
    ring
  have h432 : (432 : ℝ) ≤ Real.exp 10 :=
    (by norm_num : (432 : ℝ) ≤ 2 ^ 10).trans (two_pow_le_exp_of_le 10 le_rfl)
  have hsmall : Real.exp (-(2 * p + 10)) ≤ (Real.exp (-p) / 3) ^ 2 / 48 := by
    rw [hthreshold]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 432)).mpr
    calc
      _ ≤ Real.exp (-(2 * p + 10)) * Real.exp 10 :=
        mul_le_mul_of_nonneg_left h432 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨k, A, B, ?_, ?_, ?_⟩
  · intro t n
    simpa only [A, norm_mul, norm_star, AddChar.norm_apply, mul_one] using hb t (n : ZMod N)
  · intro t n
    simpa only [B, norm_mul, norm_star, AddChar.norm_apply, mul_one] using hb t (n : ZMod N)
  · rw [hfinal] at hχ
    exact hsmall.trans hχ

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_unwrapped_reflected_correlation {N : ℕ} [NeZero N] {p : ℝ}
    (hp : 0 ≤ p) (R S : ℤ → ℤ → ℂ)
    (hR : ∀ x n, ‖R x n‖ ≤ 1) (hS : ∀ y n, ‖S y n‖ ≤ 1)
    (z : ZMod N) (b : ZMod N → ℂ) (hb : ∀ x, ‖b x‖ ≤ 1)
    (hcorr : Real.exp (-p) ≤ ‖𝔼 x : ZMod N, 𝔼 y : ZMod N,
      R x.val (z - x - y).val * star (S y.val (z - x - y).val) * b x * star (b y)‖) :
    ∃ (k : Fin 3) (A B : ℤ → ℂ), (∀ n, ‖A n‖ ≤ 1) ∧ (∀ n, ‖B n‖ ≤ 1) ∧
      Real.exp (-(2 * p + 10)) ≤ ‖𝔼 x : ZMod N, 𝔼 y : ZMod N,
        R x.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val) *
          star (S y.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val)) * A x.val * B y.val‖ := by
  let F (k : Fin 3) (x y : ZMod N) :=
    R x.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val) *
      star (S y.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val)) * b x * star (b y)
  let G (x y : ZMod N) := R x.val (z - x - y).val * star (S y.val (z - x - y).val) * b x * star (b y)
  let D (x y : ZMod N) := tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y
  have hF (k : Fin 3) (x y : ZMod N) : ‖F k x y‖ ≤ 1 := by
    simp only [F, norm_mul, norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hb y)
    apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hb x)
    exact (mul_le_of_le_one_left (norm_nonneg _) (hR _ _)).trans (hS _ _)
  have hterm (k : Fin 3) (x y : ZMod N) :
      F k x y * finiteIndicator (tripleCarryInterval N k) (D x y) =
        G x y * finiteIndicator (tripleCarryInterval N k) (D x y) := by
    by_cases hk : D x y ∈ tripleCarryInterval N k
    · have hr := tripleCarry_representative z x y k hk
      simp only [finiteIndicator, ite_eq_left hk, mul_one, F, G, hr]
    · simp only [finiteIndicator, ite_eq_right hk, mul_zero]
  have hpoint (x y : ZMod N) :
      (∑ k : Fin 3, F k x y * finiteIndicator (tripleCarryInterval N k) (D x y)) = G x y := by
    simp_rw [hterm]
    rw [← Finset.mul_sum, sum_tripleCarry_indicator, mul_one]
  have hsum : (∑ k : Fin 3, 𝔼 x : ZMod N, 𝔼 y : ZMod N,
      F k x y * finiteIndicator (tripleCarryInterval N k) (D x y)) = 𝔼 x, 𝔼 y, G x y := by
    rw [← Finset.expect_sum_comm]
    apply Finset.expect_congr rfl
    intro x _
    rw [← Finset.expect_sum_comm]
    exact Finset.expect_congr rfl (fun y _ => hpoint x y)
  obtain ⟨k, hk⟩ := exists_large_weighted_term (fun _ : Fin 3 => (1 : ℂ))
    (fun k => 𝔼 x : ZMod N, 𝔼 y : ZMod N,
      F k x y * finiteIndicator (tripleCarryInterval N k) (D x y))
    (Real.exp_pos (-p)) (by norm_num : (0 : ℝ) < 3) (by norm_num)
    (by simpa only [one_mul, hsum, G] using hcorr)
  have hρ1 : Real.exp (-p) / 3 ≤ 1 := by
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hp)
    linarith
  obtain ⟨χ, hχ⟩ := exists_remove_triple_interval z (tripleCarryStart N k) N (F k) (hF k)
    (by positivity : 0 < Real.exp (-p) / 3) hρ1 hk
  let A (n : ℤ) := b (n : ZMod N) * star (χ (n : ZMod (3 * N)))
  let B (n : ℤ) := star (b (n : ZMod N)) * star (χ (n : ZMod (3 * N)))
  have hA (n : ℤ) : ‖A n‖ ≤ 1 := by
    simpa only [A, norm_mul, norm_star, AddChar.norm_apply, mul_one] using hb (n : ZMod N)
  have hB (n : ℤ) : ‖B n‖ ≤ 1 := by
    simpa only [B, norm_mul, norm_star, AddChar.norm_apply, mul_one] using hb (n : ZMod N)
  have hAe (x : ZMod N) : A (x.val : ℤ) = b x * star (χ (tripleCyclicEmbed x)) := by
    simp [A, tripleCyclicEmbed]
  have hBe (y : ZMod N) : B (y.val : ℤ) = star (b y) * star (χ (tripleCyclicEmbed y)) := by
    simp [B, tripleCyclicEmbed]
  have htwo : Real.exp (-p) ^ 2 = Real.exp (-(2 * p)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  have hthreshold : (Real.exp (-p) / 3) ^ 2 / 48 = Real.exp (-(2 * p)) / 432 := by
    rw [div_pow, htwo]
    ring
  have h432 : (432 : ℝ) ≤ Real.exp 10 :=
    (by norm_num : (432 : ℝ) ≤ 2 ^ 10).trans (two_pow_le_exp_of_le 10 le_rfl)
  have hsmall : Real.exp (-(2 * p + 10)) ≤ (Real.exp (-p) / 3) ^ 2 / 48 := by
    rw [hthreshold]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 432)).mpr
    calc
      _ ≤ Real.exp (-(2 * p + 10)) * Real.exp 10 :=
        mul_le_mul_of_nonneg_left h432 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨k, A, B, hA, hB, ?_⟩
  simpa only [F, hAe, hBe, mul_assoc, mul_comm, mul_left_comm] using hsmall.trans hχ

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_cyclic_mixed_reflection (n : ℕ)
    {T : Type} [Fintype T] [Nonempty T] {N : ℕ} [NeZero N] {p : ℝ} (hp : 0 ≤ p)
    (K : T → ℤ → ℤ → (Fin n → ℤ) → ℂ) (hK : ∀ t h m u, ‖K t h m u‖ ≤ 1)
    (f : T → ZMod N → ℂ) (hf : ∀ t x, ‖f t x‖ ≤ 1)
    (A : T → Fin (n + 2) → (Fin (n + 2) → ZMod N) → ℂ)
    (hA : ∀ t i x, ‖A t i x‖ ≤ 1) (hmiss : ∀ t i, MissesBoxCoordinate (A t i) i)
    (hcorr : Real.exp (-p) ≤ ‖𝔼 t, 𝔼 u : Fin n → ZMod N, 𝔼 m : ZMod N, 𝔼 h : ZMod N,
      f t (m + h + ∑ i, u i) * K t h.val m.val (fun i => (u i).val) *
        ∏ i, A t i (Fin.cons h (Fin.cons m u))‖) :
    ∃ (z : ZMod N) (k : Fin 3) (B : T → Fin (n + 2) → (Fin (n + 2) → ℤ) → ℂ),
      (∀ t i x, ‖B t i x‖ ≤ 1) ∧
      (∀ t i x y, (∀ j, j ≠ i → x j = y j) → B t i x = B t i y) ∧
      let c : ℤ := z.val + (k.val : ℤ) * N
      Real.exp (-(2 * ((2 ^ (n + 1) : ℕ) : ℝ) * p + 10)) ≤
        ‖𝔼 t, 𝔼 u : Fin n → ZMod N, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
          (K t h.val (c - h.val - h'.val) (fun i => (u i).val) *
            star (K t h'.val (c - h.val - h'.val) (fun i => (u i).val))) *
              ∏ i, B t i (Fin.cons (h.val : ℤ) (Fin.cons (h'.val : ℤ) (fun j => (u j).val)))‖ := by
  let φ (x : ZMod N) : ℤ := x.val
  let Kcyc (t : T) (h m : ZMod N) (u : Fin n → ZMod N) :=
    K t (φ h) (φ m) (fun i => φ (u i))
  obtain ⟨z, b, hb, hreflect⟩ := exists_mixed_reflected_exp_correlation n Kcyc f A hf hA hmiss hcorr
  let P := ((2 ^ (n + 1) : ℕ) : ℝ) * p
  have hP : 0 ≤ P := mul_nonneg (Nat.cast_nonneg _) hp
  let R (t : T × ((Fin n → ZMod N) × (Fin n → ZMod N))) (h m : ℤ) :=
    mixedTailDifference (K t.1) (fun i => φ (t.2.1 i)) (fun i => φ (t.2.2 i)) h m
  let b' (t : T × ((Fin n → ZMod N) × (Fin n → ZMod N))) (h : ZMod N) :=
    b t.1 t.2.1 t.2.2 h
  have hR : ∀ t h m, ‖R t h m‖ ≤ 1 := fun t h m =>
    mixedTailDifference_norm (K t.1) (hK t.1) _ _ h m
  have hmap (t : T) (u v : Fin n → ZMod N) (h m : ZMod N) :
      mixedTailDifference (Kcyc t) u v h m = R (t, (u, v)) (φ h) (φ m) :=
    mixedTailDifference_map φ (K t) u v h m
  have hinput : Real.exp (-P) ≤
      ‖𝔼 t, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
        R t h.val (z - h - h').val * star (R t h'.val (z - h - h').val) *
          b' t h * star (b' t h')‖ := by
    simpa only [P, neg_mul, b', expect_prod_split, hmap, φ] using
      hreflect.trans (Complex.re_le_norm _)
  obtain ⟨k, B₀, C₀, hB₀, hC₀, hunwrapped⟩ :=
    exists_unwrapped_family_reflected_correlation hP R R hR hR z b'
      (fun t h => hb t.1 t.2.1 t.2.2 h) hinput
  let c : ℤ := z.val + (k.val : ℤ) * N
  have hψ (x : ZMod N) : ((φ x : ℤ) : ZMod N) = x := by
    simp [φ]
  have hanchorInput : Real.exp (-(2 * P + 10)) ≤
      ‖𝔼 t, 𝔼 u : Fin n → ZMod N, 𝔼 v : Fin n → ZMod N, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
        mixedTailDifference (K t) (fun i => φ (u i)) (fun i => φ (v i)) (φ h) (c - φ h - φ h') *
          star (mixedTailDifference (K t) (fun i => φ (u i)) (fun i => φ (v i)) (φ h')
            (c - φ h - φ h')) * B₀ (t, (u, v)) (φ h) * C₀ (t, (u, v)) (φ h')‖ := by
    simpa only [R, c, φ, expect_prod_split] using hunwrapped
  obtain ⟨B, hB, hBind, hfinal⟩ := exists_anchored_reflected_family φ
    (fun x : ℤ => (x : ZMod N)) hψ K hK c
    (fun t u v h => B₀ (t, (u, v)) h) (fun t u v h => C₀ (t, (u, v)) h)
    (fun t u v h => hB₀ (t, (u, v)) h) (fun t u v h => hC₀ (t, (u, v)) h) hanchorInput
  refine ⟨z, k, B, hB, hBind, ?_⟩
  simpa only [P, mul_assoc, c, φ] using hfinal

end Erdos3

end

end OAI
