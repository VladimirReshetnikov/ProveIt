import GowersSzemeredi.Section05
import GowersSzemeredi.Sections06_07
import GowersSzemeredi.Sections08_09
import GowersSzemeredi.Section10
import GowersSzemeredi.ProofInfrastructure
import GowersSzemeredi.Proofs01_03
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Proofs for Gowers (2001), Sections 5--10

This file supplies proofs of those formalized statements from Sections 5--10
that follow directly from general results already available in Mathlib or from
finite combinatorial identities.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod Combinatorics.Additive
open Finset

namespace LeanProofs.GowersSzemeredi

@[simp] private lemma prop61_exponential_add {N : Nat} [NeZero N]
    (x y : ZMod N) : exponential (x + y) = exponential x * exponential y := by
  exact AddChar.map_add_eq_mul (ZMod.stdAddChar (N := N)) x y

@[simp] private lemma prop61_star_exponential {N : Nat} [NeZero N]
    (x : ZMod N) : star (exponential x) = exponential (-x) := by
  simpa only [exponential, starRingEnd_apply] using
    (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := N)) x).symm

/-- Expansion and change of variables at the start of Proposition 6.1. -/
private lemma prop61_energy_expansion {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (B : Finset (ZMod N)) (phi : ZMod N → ZMod N) :
    (((∑ k ∈ B, ‖fourier (difference f k) (phi k)‖ ^ 2 : ℝ)) : Complex) =
      ∑ u : ZMod N, ∑ s : ZMod N,
        f s * star (f (s - u)) *
          ∑ k ∈ B, star (f (s - k)) * f (s - k - u) *
            exponential (-(phi k * u)) := by
  simp only [fourier, difference, ZMod.dft_apply, smul_eq_mul]
  calc
    (((∑ k ∈ B,
        ‖∑ s : ZMod N, exponential (-(s * phi k)) *
          (f s * star (f (s - k)))‖ ^ 2 : ℝ)) : Complex) =
        ∑ k ∈ B,
          (∑ s : ZMod N, exponential (-(s * phi k)) *
            (f s * star (f (s - k)))) *
          star (∑ t : ZMod N, exponential (-(t * phi k)) *
            (f t * star (f (t - k)))) := by
              rw [Complex.ofReal_sum]
              apply Finset.sum_congr rfl
              intro k _
              rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow]
    _ = ∑ k ∈ B, ∑ s : ZMod N, ∑ t : ZMod N,
          (exponential (-(s * phi k)) * (f s * star (f (s - k)))) *
            ((f (t - k) * star (f t)) * exponential (t * phi k)) := by
              apply Finset.sum_congr rfl
              intro k _
              simp only [star_sum, star_mul, star_star, prop61_star_exponential, neg_neg]
              simp_rw [sum_mul, mul_sum]
    _ = ∑ s : ZMod N, ∑ t : ZMod N, ∑ k ∈ B,
          (exponential (-(s * phi k)) * (f s * star (f (s - k)))) *
            ((f (t - k) * star (f t)) * exponential (t * phi k)) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro s _
              rw [Finset.sum_comm]
    _ = ∑ s : ZMod N, ∑ u : ZMod N, ∑ k ∈ B,
          (exponential (-(s * phi k)) * (f s * star (f (s - k)))) *
            ((f (s - u - k) * star (f (s - u))) * exponential ((s - u) * phi k)) := by
              apply Finset.sum_congr rfl
              intro s _
              rw [← (Equiv.subLeft s).sum_comp]
              rfl
    _ = ∑ u : ZMod N, ∑ s : ZMod N,
          f s * star (f (s - u)) *
            ∑ k ∈ B, star (f (s - k)) * f (s - k - u) *
              exponential (-(phi k * u)) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro u _
              apply Finset.sum_congr rfl
              intro s _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              have hphase :
                  exponential (-(s * phi k)) * exponential ((s - u) * phi k) =
                    exponential (-(phi k * u)) := by
                rw [← prop61_exponential_add]
                congr 1
                ring
              rw [← hphase]
              ring

private lemma prop61_initial_bound {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (B : Finset (ZMod N)) (phi : ZMod N → ZMod N)
    (hf : DiscValued f) :
    (∑ k ∈ B, ‖fourier (difference f k) (phi k)‖ ^ 2) ≤
      ∑ u : ZMod N, ∑ s : ZMod N,
        ‖∑ k ∈ B, star (f (s - k)) * f (s - k - u) *
          exponential (-(phi k * u))‖ := by
  let inner : ZMod N → ZMod N → Complex := fun u s =>
    ∑ k ∈ B, star (f (s - k)) * f (s - k - u) * exponential (-(phi k * u))
  have hnonneg : 0 ≤ ∑ k ∈ B, ‖fourier (difference f k) (phi k)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc
    (∑ k ∈ B, ‖fourier (difference f k) (phi k)‖ ^ 2) =
        ‖(((∑ k ∈ B, ‖fourier (difference f k) (phi k)‖ ^ 2 : ℝ)) : Complex)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hnonneg]
    _ = ‖∑ u : ZMod N, ∑ s : ZMod N,
          f s * star (f (s - u)) * inner u s‖ := by
            rw [prop61_energy_expansion f B phi]
    _ ≤ ∑ u : ZMod N, ‖∑ s : ZMod N,
          f s * star (f (s - u)) * inner u s‖ := norm_sum_le _ _
    _ ≤ ∑ u : ZMod N, ∑ s : ZMod N,
          ‖f s * star (f (s - u)) * inner u s‖ := by
            apply Finset.sum_le_sum
            intro u _
            exact norm_sum_le _ _
    _ ≤ ∑ u : ZMod N, ∑ s : ZMod N, ‖inner u s‖ := by
            apply Finset.sum_le_sum
            intro u _
            apply Finset.sum_le_sum
            intro s _
            rw [norm_mul, norm_mul, norm_star]
            have hs := hf s
            have hsu := hf (s - u)
            calc
              ‖f s‖ * ‖f (s - u)‖ * ‖inner u s‖ ≤ 1 * 1 * ‖inner u s‖ := by
                gcongr
              _ = ‖inner u s‖ := by ring

private lemma prop61_l1_cauchy {N : Nat} [NeZero N] (F : ZMod N → ZMod N → ℝ) :
    (∑ u : ZMod N, ∑ s : ZMod N, F u s) ^ 2 ≤
      (N : ℝ) ^ 2 * ∑ u : ZMod N, ∑ s : ZMod N, (F u s) ^ 2 := by
  calc
    (∑ u : ZMod N, ∑ s : ZMod N, F u s) ^ 2 ≤
        (N : ℝ) * ∑ u : ZMod N, (∑ s : ZMod N, F u s) ^ 2 := by
          simpa only [Finset.card_univ, ZMod.card, Nat.cast_ofNat] using
            (sq_sum_le_card_mul_sum_sq
              (s := (Finset.univ : Finset (ZMod N))) (f := fun u => ∑ s, F u s))
    _ ≤ (N : ℝ) * ∑ u : ZMod N,
        ((N : ℝ) * ∑ s : ZMod N, (F u s) ^ 2) := by
          gcongr with u
          simpa only [Finset.card_univ, ZMod.card, Nat.cast_ofNat] using
            (sq_sum_le_card_mul_sum_sq
              (s := (Finset.univ : Finset (ZMod N))) (f := F u))
    _ = (N : ℝ) ^ 2 * ∑ u : ZMod N, ∑ s : ZMod N, (F u s) ^ 2 := by
          rw [← Finset.mul_sum]
          ring

private def prop61F {N : Nat} (f : ZMod N → Complex) (u x : ZMod N) : Complex :=
  star (f (-x)) * f (-x - u)

private def prop61G {N : Nat} [NeZero N] (B : Finset (ZMod N)) (phi : ZMod N → ZMod N)
    (u x : ZMod N) : Complex :=
  indicator B x * exponential (phi x * u)

private lemma prop61_correlation_eq {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (B : Finset (ZMod N)) (phi : ZMod N → ZMod N)
    (u s : ZMod N) :
    correlation (prop61F f u) (prop61G B phi u) (-s) =
      ∑ k ∈ B, star (f (s - k)) * f (s - k - u) *
        exponential (-(phi k * u)) := by
  classical
  simp only [correlation]
  rw [← (Equiv.subRight s).sum_comp]
  simp only [Equiv.subRight_apply, prop61F, prop61G, sub_neg_eq_add, sub_add_cancel,
    neg_sub, indicator, star_mul]
  simp [mul_assoc]

private lemma prop61_mixed_eq_l2 {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (B : Finset (ZMod N)) (phi : ZMod N → ZMod N) :
    (∑ u : ZMod N, ∑ r : ZMod N,
        ‖fourier (prop61F f u) r‖ ^ 2 * ‖fourier (prop61G B phi u) r‖ ^ 2) =
      (N : ℝ) * ∑ u : ZMod N, ∑ s : ZMod N,
        ‖∑ k ∈ B, star (f (s - k)) * f (s - k - u) *
          exponential (-(phi k * u))‖ ^ 2 := by
  calc
    _ = ∑ u : ZMod N, (N : ℝ) * ∑ t : ZMod N,
        ‖correlation (prop61F f u) (prop61G B phi u) t‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro u _
          exact lemma_2_1_holds N (prop61F f u) (prop61G B phi u)
    _ = (N : ℝ) * ∑ u : ZMod N, ∑ s : ZMod N,
        ‖∑ k ∈ B, star (f (s - k)) * f (s - k - u) *
          exponential (-(phi k * u))‖ ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u _
          congr 1
          have hneg :
              (∑ t : ZMod N,
                ‖correlation (prop61F f u) (prop61G B phi u) t‖ ^ 2) =
              ∑ s : ZMod N,
                ‖correlation (prop61F f u) (prop61G B phi u) (-s)‖ ^ 2 := by
            symm
            exact Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ fun _ => rfl
          rw [hneg]
          apply Finset.sum_congr rfl
          intro s _
          rw [prop61_correlation_eq]

private lemma prop61_fourth_moment_le {N : Nat} [NeZero N]
    (h : ZMod N → Complex) (hh : DiscValued h) :
    ∑ r : ZMod N, ‖fourier h r‖ ^ 4 ≤ (N : ℝ) ^ 4 := by
  have hcorr (t : ZMod N) : ‖correlation h h t‖ ≤ (N : ℝ) := by
    calc
      ‖correlation h h t‖ ≤ ∑ s : ZMod N, ‖h s * star (h (s - t))‖ := by
        exact norm_sum_le _ _
      _ ≤ ∑ _s : ZMod N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro s _
        rw [norm_mul, norm_star]
        calc
          ‖h s‖ * ‖h (s - t)‖ ≤ 1 * 1 := by gcongr <;> apply hh
          _ = 1 := one_mul 1
      _ = (N : ℝ) := by simp
  have hid :
      (∑ r : ZMod N, ‖fourier h r‖ ^ 4) =
        (N : ℝ) * ∑ t : ZMod N, ‖correlation h h t‖ ^ 2 := by
    calc
      _ = ∑ r : ZMod N, ‖fourier h r‖ ^ 2 * ‖fourier h r‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ = _ := by simpa [correlation] using lemma_2_1_holds N h h
  rw [hid]
  calc
    (N : ℝ) * ∑ t : ZMod N, ‖correlation h h t‖ ^ 2 ≤
        (N : ℝ) * ∑ _t : ZMod N, (N : ℝ) ^ 2 := by
          gcongr with t
          exact hcorr t
    _ = (N : ℝ) ^ 4 := by simp; ring

private lemma prop61F_disc {N : Nat} (f : ZMod N → Complex) (hf : DiscValued f)
    (u : ZMod N) : DiscValued (prop61F f u) := by
  intro x
  rw [prop61F, norm_mul, norm_star]
  calc
    ‖f (-x)‖ * ‖f (-x - u)‖ ≤ 1 * 1 := by gcongr <;> apply hf
    _ = 1 := one_mul 1

private abbrev prop61QuadMem {N : Nat} (B : Finset (ZMod N))
    (q : Fin 4 → ZMod N) : Prop :=
  q 0 ∈ B ∧ q 1 ∈ B ∧ q 2 ∈ B ∧ q 3 ∈ B

private abbrev prop61AltAdditive {N : Nat} (B : Finset (ZMod N))
    (phi : ZMod N → ZMod N) (q : Fin 4 → ZMod N) : Prop :=
  prop61QuadMem B q ∧ q 0 - q 1 = q 2 - q 3 ∧
    phi (q 0) - phi (q 1) = phi (q 2) - phi (q 3)

private def prop61QuadEquiv (X : Type*) : (Fin 4 → X) ≃ (Fin 4 → X) where
  toFun q := ![q 0, q 3, q 2, q 1]
  invFun q := ![q 0, q 3, q 2, q 1]
  left_inv q := by
    funext i
    fin_cases i <;> rfl
  right_inv q := by
    funext i
    fin_cases i <;> rfl

private lemma prop61_alt_count_eq {N : Nat} [NeZero N] (B : Finset (ZMod N))
    (phi : ZMod N → ZMod N) :
    countWhere (prop61AltAdditive B phi) = phiAdditiveCount B phi := by
  classical
  unfold countWhere phiAdditiveCount
  apply Finset.card_equiv (prop61QuadEquiv (ZMod N))
  intro q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [prop61AltAdditive, prop61QuadMem, IsPhiAdditive, IsAdditiveQuadruple,
    prop61QuadEquiv]
  constructor
  · rintro ⟨⟨h0, h1, h2, h3⟩, hadd, hphi⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> assumption
    · rw [← sub_eq_sub_iff_add_eq_add]
      simpa [add_comm] using hadd
    · rw [← sub_eq_sub_iff_add_eq_add]
      simpa [add_comm] using hphi
  · rintro ⟨hmem, hadd, hphi⟩
    refine ⟨⟨hmem 0, hmem 3, hmem 2, hmem 1⟩, ?_, ?_⟩
    · rw [sub_eq_sub_iff_add_eq_add]
      simpa [add_comm] using hadd
    · rw [sub_eq_sub_iff_add_eq_add]
      simpa [add_comm] using hphi

private lemma prop61_g_product {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N)
    (q : Fin 4 → ZMod N) (u : ZMod N) :
    prop61G B phi u (q 0) *
        star (prop61G B phi u (q 1) * prop61G B phi u (q 2)) *
        prop61G B phi u (q 3) =
      if prop61QuadMem B q then
        exponential ((phi (q 0) - phi (q 1) - phi (q 2) + phi (q 3)) * u)
      else 0 := by
  classical
  simp only [prop61G, indicator, star_mul]
  by_cases h0 : q 0 ∈ B <;> by_cases h1 : q 1 ∈ B <;>
    by_cases h2 : q 2 ∈ B <;> by_cases h3 : q 3 ∈ B
  all_goals simp only [h0, h1, h2, h3, if_true, if_false, one_mul, zero_mul, mul_zero,
    star_zero, star_one, prop61QuadMem, and_self, and_true]
  all_goals try {rfl}
  rw [prop61_star_exponential, prop61_star_exponential]
  calc
    _ = exponential (phi (q 0) * u +
        (-(phi (q 2) * u) + (-(phi (q 1) * u) + phi (q 3) * u))) := by
          rw [prop61_exponential_add, prop61_exponential_add, prop61_exponential_add]
          ring
    _ = _ := by
      congr 1
      ring

private lemma prop61_sum_exponential_mul {N : Nat} [NeZero N] (x : ZMod N) :
    ∑ u : ZMod N, exponential (x * u) = if x = 0 then (N : Complex) else 0 := by
  simpa [exponential, mul_comm] using
    AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar N)

private lemma prop61_sum_g_product {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N) (q : Fin 4 → ZMod N) :
    (∑ u : ZMod N,
      prop61G B phi u (q 0) *
        star (prop61G B phi u (q 1) * prop61G B phi u (q 2)) *
        prop61G B phi u (q 3)) =
      if prop61QuadMem B q ∧
          phi (q 0) - phi (q 1) = phi (q 2) - phi (q 3)
        then (N : Complex) else 0 := by
  simp_rw [prop61_g_product]
  by_cases hmem : prop61QuadMem B q
  · simp_rw [if_pos hmem]
    rw [prop61_sum_exponential_mul]
    by_cases hphi : phi (q 0) - phi (q 1) = phi (q 2) - phi (q 3)
    · have hcond : prop61QuadMem B q ∧
          phi (q 0) - phi (q 1) = phi (q 2) - phi (q 3) := ⟨hmem, hphi⟩
      have hzero : phi (q 0) - phi (q 1) - phi (q 2) + phi (q 3) = 0 := by
        calc
          phi (q 0) - phi (q 1) - phi (q 2) + phi (q 3) =
              (phi (q 0) - phi (q 1)) - (phi (q 2) - phi (q 3)) := by abel
          _ = 0 := by rw [hphi, sub_self]
      rw [if_pos hzero, if_pos hcond]
    · have hne : phi (q 0) - phi (q 1) - phi (q 2) + phi (q 3) ≠ 0 := by
        intro hzero
        apply hphi
        apply sub_eq_zero.mp
        calc
          (phi (q 0) - phi (q 1)) - (phi (q 2) - phi (q 3)) =
              phi (q 0) - phi (q 1) - phi (q 2) + phi (q 3) := by abel
          _ = 0 := hzero
      have hcond : ¬(prop61QuadMem B q ∧
          phi (q 0) - phi (q 1) = phi (q 2) - phi (q 3)) := fun h => hphi h.2
      rw [if_neg hne, if_neg hcond]
  · simp_rw [if_neg hmem]
    rw [if_neg (fun h => hmem h.1)]
    simp

private lemma prop61_g_fourth_eq_count {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N) :
    (∑ u : ZMod N, ∑ r : ZMod N, ‖fourier (prop61G B phi u) r‖ ^ 4) =
      (N : ℝ) ^ 2 * phiAdditiveCount B phi := by
  classical
  have hcomplex :
      (((∑ u : ZMod N, ∑ r : ZMod N,
          ‖fourier (prop61G B phi u) r‖ ^ 4 : ℝ)) : Complex) =
        (((N : ℝ) ^ 2 * countWhere (prop61AltAdditive B phi) : ℝ) : Complex) := by
    rw [Complex.ofReal_sum]
    calc
      (∑ u : ZMod N,
          ((∑ r : ZMod N, ‖fourier (prop61G B phi u) r‖ ^ 4 : ℝ) : Complex)) =
          ∑ u : ZMod N, (N : Complex) * ∑ q : Fin 4 → ZMod N,
            if q 0 - q 1 = q 2 - q 3 then
              prop61G B phi u (q 0) *
                star (prop61G B phi u (q 1) * prop61G B phi u (q 2)) *
                prop61G B phi u (q 3)
            else 0 := by
              apply Finset.sum_congr rfl
              intro u _
              exact identity_2_6_holds N (prop61G B phi u)
      _ = (N : Complex) * (∑ q : Fin 4 → ZMod N,
          if q 0 - q 1 = q 2 - q 3 then
            ∑ u : ZMod N,
              prop61G B phi u (q 0) *
                star (prop61G B phi u (q 1) * prop61G B phi u (q 2)) *
                prop61G B phi u (q 3)
          else 0) := by
            rw [← Finset.mul_sum]
            congr 1
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro q _
            by_cases hadd : q 0 - q 1 = q 2 - q 3 <;> simp [hadd]
      _ = (N : Complex) * (∑ q : Fin 4 → ZMod N,
          if prop61AltAdditive B phi q then (N : Complex) else 0) := by
            congr 1
            apply Finset.sum_congr rfl
            intro q _
            rw [prop61_sum_g_product]
            by_cases hmem : prop61QuadMem B q <;>
              by_cases hadd : q 0 - q 1 = q 2 - q 3 <;>
              by_cases hphi : phi (q 0) - phi (q 1) = phi (q 2) - phi (q 3) <;>
              simp [prop61AltAdditive, hmem, hadd, hphi]
      _ = (((N : ℝ) ^ 2 * countWhere (prop61AltAdditive B phi) : ℝ) : Complex) := by
            push_cast
            unfold countWhere
            rw [← Finset.sum_filter]
            simp only [Finset.sum_const, nsmul_eq_mul]
            ring_nf
            congr 1
            norm_cast
            apply congrArg Finset.card
            ext q
            simp
  rw [prop61_alt_count_eq B phi] at hcomplex
  exact Complex.ofReal_injective hcomplex

private lemma prop61_global_cauchy {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (B : Finset (ZMod N)) (phi : ZMod N → ZMod N) :
    (∑ u : ZMod N, ∑ r : ZMod N,
        ‖fourier (prop61F f u) r‖ ^ 2 * ‖fourier (prop61G B phi u) r‖ ^ 2) ^ 2 ≤
      (∑ u : ZMod N, ∑ r : ZMod N, ‖fourier (prop61F f u) r‖ ^ 4) *
        ∑ u : ZMod N, ∑ r : ZMod N, ‖fourier (prop61G B phi u) r‖ ^ 4 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    ((Finset.univ : Finset (ZMod N)) ×ˢ (Finset.univ : Finset (ZMod N)))
    (fun p => ‖fourier (prop61F f p.1) p.2‖ ^ 2)
    (fun p => ‖fourier (prop61G B phi p.1) p.2‖ ^ 2)
  simpa only [Finset.sum_product, ← pow_mul] using h

/-- Two residues falling in the same one-dimensional grid cell differ by a
Bohr-small residue. -/
private lemma lemma77_centeredAbs_sub_le {N m : Nat} [NeZero N]
    {delta : ℝ} (hdelta : 0 < delta) (hm : 0 < m)
    (hm_lower : delta⁻¹ ≤ (m : ℝ)) {x y : ZMod N}
    (hbin : x.val * m / N = y.val * m / N) :
    (centeredAbs (x - y) : ℝ) ≤ delta * N := by
  have hNnat : 0 < N := NeZero.pos N
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hdelta_m : 1 ≤ delta * (m : ℝ) := by
    calc
      1 = delta * delta⁻¹ := (mul_inv_cancel₀ hdelta.ne').symm
      _ ≤ delta * (m : ℝ) := mul_le_mul_of_nonneg_left hm_lower hdelta.le
  have hNm : (N : ℝ) / m ≤ delta * N := by
    apply (div_le_iff₀ hmreal).2
    nlinarith
  have ordered {a b : ZMod N} (hba : b.val ≤ a.val)
      (habin : a.val * m / N = b.val * m / N) :
      (centeredAbs (a - b) : ℝ) < (N : ℝ) / m := by
    let q := a.val * m / N
    have hhi : a.val * m < N * (q + 1) := by
      simpa only [q] using Nat.lt_mul_div_succ (a.val * m) hNnat
    have hlo : q * N ≤ b.val * m := by
      calc
        q * N = (a.val * m / N) * N := rfl
        _ = (b.val * m / N) * N := by rw [habin]
        _ ≤ b.val * m := Nat.div_mul_le_self _ _
    have hhiR : (a.val : ℝ) * m < (N : ℝ) * ((q : ℝ) + 1) := by
      exact_mod_cast hhi
    have hloR : (q : ℝ) * N ≤ (b.val : ℝ) * m := by
      exact_mod_cast hlo
    have hdiffR : ((a.val - b.val : Nat) : ℝ) * m < (N : ℝ) := by
      rw [Nat.cast_sub hba]
      nlinarith
    have hcenterNat : centeredAbs (a - b) ≤ a.val - b.val := by
      unfold centeredAbs
      rw [ZMod.valMinAbs_natAbs_eq_min, ZMod.val_sub hba]
      exact Nat.min_le_left _ _
    have hcenterR : (centeredAbs (a - b) : ℝ) ≤ (a.val - b.val : Nat) := by
      exact_mod_cast hcenterNat
    apply (lt_div_iff₀ hmreal).2
    exact (mul_le_mul_of_nonneg_right hcenterR hmreal.le).trans_lt hdiffR
  rcases le_total y.val x.val with hyx | hxy
  · exact (ordered hyx hbin).le.trans hNm
  · have hneg : centeredAbs (x - y) = centeredAbs (y - x) := by
      unfold centeredAbs
      rw [show x - y = -(y - x) by abel, ZMod.natAbs_valMinAbs_neg]
    rw [hneg]
    exact (ordered hxy hbin.symm).le.trans hNm

/-- Lemma 5.4 is Mathlib's Dirichlet approximation theorem, with the resulting
rational written in reduced numerator/denominator form. -/
theorem lemma_5_4_holds : lemma_5_4 := by
  intro alpha u hu
  obtain ⟨r, hr, hru⟩ := Real.exists_rat_abs_sub_le_and_den_le alpha (by omega : 0 < u)
  refine ⟨r.num, r.den, r.den_pos, hru, r.reduced, ?_⟩
  have hden : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hu_real : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
  calc
    |alpha - (r.num : ℝ) / (r.den : ℝ)| = |alpha - (r : ℝ)| := by
      congr 2
      exact (Rat.cast_def r).symm
    _ ≤ 1 / (((u : ℝ) + 1) * r.den) := by simpa using hr
    _ ≤ (((r.den : ℝ) * u))⁻¹ := by
      rw [inv_eq_one_div]
      refine one_div_le_one_div_of_le (mul_pos hden hu_real) ?_
      nlinarith

/-- Proposition 6.1 follows by two applications of Cauchy--Schwarz, the
Fourier correlation identity, and character orthogonality. -/
theorem proposition_6_1_holds : proposition_6_1 := by
  intro N _ alpha f B phi hAlpha hf hlarge
  let inner : ZMod N → ZMod N → Complex := fun u s =>
    ∑ k ∈ B, star (f (s - k)) * f (s - k - u) * exponential (-(phi k * u))
  let L1 : ℝ := ∑ u : ZMod N, ∑ s : ZMod N, ‖inner u s‖
  let L2 : ℝ := ∑ u : ZMod N, ∑ s : ZMod N, ‖inner u s‖ ^ 2
  let mixed : ℝ := ∑ u : ZMod N, ∑ r : ZMod N,
    ‖fourier (prop61F f u) r‖ ^ 2 * ‖fourier (prop61G B phi u) r‖ ^ 2
  let fourthF : ℝ := ∑ u : ZMod N, ∑ r : ZMod N,
    ‖fourier (prop61F f u) r‖ ^ 4
  let fourthG : ℝ := ∑ u : ZMod N, ∑ r : ZMod N,
    ‖fourier (prop61G B phi u) r‖ ^ 4
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hN5 : (0 : ℝ) < (N : ℝ) ^ 5 := by positivity
  have hL1 : alpha * (N : ℝ) ^ 3 ≤ L1 := hlarge.trans <| by
    simpa only [L1, inner] using prop61_initial_bound f B phi hf
  have hL1_nonneg : 0 ≤ L1 := by
    dsimp only [L1]
    positivity
  have hbase_nonneg : 0 ≤ alpha * (N : ℝ) ^ 3 :=
    mul_nonneg hAlpha.le (by positivity)
  have hL1sq : (alpha * (N : ℝ) ^ 3) ^ 2 ≤ L1 ^ 2 :=
    (sq_le_sq₀ hbase_nonneg hL1_nonneg).2 hL1
  have hCauchy1 : L1 ^ 2 ≤ (N : ℝ) ^ 2 * L2 := by
    simpa only [L1, L2] using
      (prop61_l1_cauchy (N := N) (fun u s => ‖inner u s‖))
  have hL2 : alpha ^ 2 * (N : ℝ) ^ 4 ≤ L2 := by
    apply le_of_mul_le_mul_left _ hN2
    calc
      (N : ℝ) ^ 2 * (alpha ^ 2 * (N : ℝ) ^ 4) =
          (alpha * (N : ℝ) ^ 3) ^ 2 := by ring
      _ ≤ L1 ^ 2 := hL1sq
      _ ≤ (N : ℝ) ^ 2 * L2 := hCauchy1
  have hmixed_eq : mixed = (N : ℝ) * L2 := by
    simpa only [mixed, L2, inner] using prop61_mixed_eq_l2 f B phi
  have hmixed : alpha ^ 2 * (N : ℝ) ^ 5 ≤ mixed := by
    calc
      alpha ^ 2 * (N : ℝ) ^ 5 =
          (N : ℝ) * (alpha ^ 2 * (N : ℝ) ^ 4) := by ring
      _ ≤ (N : ℝ) * L2 := mul_le_mul_of_nonneg_left hL2 hN.le
      _ = mixed := hmixed_eq.symm
  have hfourthF : fourthF ≤ (N : ℝ) ^ 5 := by
    dsimp only [fourthF]
    calc
      (∑ u : ZMod N, ∑ r : ZMod N, ‖fourier (prop61F f u) r‖ ^ 4) ≤
          ∑ _u : ZMod N, (N : ℝ) ^ 4 := by
            apply Finset.sum_le_sum
            intro u _
            exact prop61_fourth_moment_le (prop61F f u) (prop61F_disc f hf u)
      _ = (N : ℝ) ^ 5 := by simp; ring
  have hmixed_nonneg : 0 ≤ mixed := by
    dsimp only [mixed]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hfourthG_nonneg : 0 ≤ fourthG := by
    dsimp only [fourthG]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      pow_nonneg (norm_nonneg _) 4
  have hmixed_sq : (alpha ^ 2 * (N : ℝ) ^ 5) ^ 2 ≤ mixed ^ 2 := by
    apply (sq_le_sq₀ (mul_nonneg (sq_nonneg _) (pow_nonneg hN.le 5)) hmixed_nonneg).2
    exact hmixed
  have hglobal : mixed ^ 2 ≤ fourthF * fourthG := by
    simpa only [mixed, fourthF, fourthG] using prop61_global_cauchy f B phi
  have hfourthG : alpha ^ 4 * (N : ℝ) ^ 5 ≤ fourthG := by
    apply le_of_mul_le_mul_left _ hN5
    calc
      (N : ℝ) ^ 5 * (alpha ^ 4 * (N : ℝ) ^ 5) =
          (alpha ^ 2 * (N : ℝ) ^ 5) ^ 2 := by ring
      _ ≤ mixed ^ 2 := hmixed_sq
      _ ≤ fourthF * fourthG := hglobal
      _ ≤ (N : ℝ) ^ 5 * fourthG :=
        mul_le_mul_of_nonneg_right hfourthF hfourthG_nonneg
  have hfourthG_eq : fourthG = (N : ℝ) ^ 2 * phiAdditiveCount B phi := by
    simpa only [fourthG] using prop61_g_fourth_eq_count B phi
  apply le_of_mul_le_mul_left _ hN2
  calc
    (N : ℝ) ^ 2 * (alpha ^ 4 * (N : ℝ) ^ 3) =
        alpha ^ 4 * (N : ℝ) ^ 5 := by ring
    _ ≤ fourthG := hfourthG
    _ = (N : ℝ) ^ 2 * phiAdditiveCount B phi := hfourthG_eq

/-- Passing to the graph injects every quadruple respected by `phi` into an
additive-energy quadruple in the product group. -/
theorem lemma_6_2_holds : lemma_6_2 := by
  intro N _ gamma B phi _ hadd
  classical
  unfold GammaAdditive at hadd
  apply hadd.trans
  norm_cast
  unfold phiAdditiveCount countWhere Finset.addEnergy
  let graphPoint : ZMod N → ZMod N × ZMod N := fun x => (x, phi x)
  let toEnergy : (Fin 4 → ZMod N) →
      ((ZMod N × ZMod N) × (ZMod N × ZMod N)) ×
        ((ZMod N × ZMod N) × (ZMod N × ZMod N)) :=
    fun q => ((graphPoint (q 0), graphPoint (q 2)),
      (graphPoint (q 1), graphPoint (q 3)))
  refine Finset.card_le_card_of_injOn toEnergy ?_ ?_
  · intro q hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rcases hq with ⟨hqB, hqadd, hqphi⟩
    constructor
    · simp only [Finset.mem_product]
      repeat' constructor
      all_goals
        simp only [toEnergy, graphPoint, functionGraph, Finset.mem_image]
        exact ⟨_, hqB _, rfl⟩
    · exact Prod.ext hqadd hqphi
  · intro q hq r hr hqr
    simp only [toEnergy, graphPoint, Prod.mk.injEq] at hqr
    funext i
    fin_cases i <;> tauto

/-- Lemma 7.7 is the finite grid/pigeonhole proof of the standard Bohr-set
cardinality bound. -/
theorem lemma_7_7_holds : lemma_7_7 := by
  intro N _ K delta hN hdelta hdelta_one
  classical
  let m : Nat := ⌈delta⁻¹⌉₊
  have hm : 0 < m := by
    dsimp only [m]
    exact Nat.ceil_pos.mpr (inv_pos.mpr hdelta)
  have hm_lower : delta⁻¹ ≤ (m : ℝ) := by
    dsimp only [m]
    exact Nat.le_ceil _
  have hone_le_inv : (1 : ℝ) ≤ delta⁻¹ := (one_le_inv₀ hdelta).2 hdelta_one
  have hm_upper : (m : ℝ) ≤ 2 * delta⁻¹ := by
    have hceil := Nat.ceil_lt_add_one (inv_nonneg.mpr hdelta.le)
    dsimp only [m]
    linarith
  let gridCode : ZMod N → ((r : ↑K) → Fin m) := fun d r =>
    ⟨(r.1 * d).val * m / N, by
      apply (Nat.div_lt_iff_lt_mul (NeZero.pos N)).2
      calc
        (r.1 * d).val * m < N * m :=
          (Nat.mul_lt_mul_right hm).2 (r.1 * d).val_lt
        _ = m * N := Nat.mul_comm _ _⟩
  have hfiber_le (c : (r : ↑K) → Fin m) :
      #(Finset.univ.filter fun d : ZMod N => gridCode d = c) ≤ #(bohr K delta) := by
    let fiber : Finset (ZMod N) := Finset.univ.filter fun d => gridCode d = c
    change #fiber ≤ #(bohr K delta)
    by_cases hnonempty : fiber.Nonempty
    · obtain ⟨a, ha⟩ := hnonempty
      refine Finset.card_le_card_of_injOn (fun d => d - a) ?_ ?_
      · intro d hd
        have hda : gridCode d = gridCode a := by
          have hd' := (Finset.mem_filter.mp hd).2
          have ha' := (Finset.mem_filter.mp ha).2
          exact hd'.trans ha'.symm
        change d - a ∈ bohr K delta
        unfold bohr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro r hr
        have hcoord := congrArg Fin.val (congrFun hda ⟨r, hr⟩)
        dsimp only [gridCode] at hcoord
        rw [mul_sub]
        exact lemma77_centeredAbs_sub_le hdelta hm hm_lower hcoord
      · intro d _ e _ hde
        exact sub_left_injective hde
    · rw [(Finset.not_nonempty_iff_eq_empty.mp hnonempty)]
      exact Nat.zero_le _
  have hcountNat : N ≤ #(bohr K delta) * m ^ K.card := by
    have hcount := Finset.card_le_mul_card_image_of_maps_to
      (s := (Finset.univ : Finset (ZMod N)))
      (t := (Finset.univ : Finset ((r : ↑K) → Fin m)))
      (f := gridCode) (fun _ _ => Finset.mem_univ _) #(bohr K delta)
      (fun c _ => hfiber_le c)
    simpa using hcount
  have hcount : (N : ℝ) ≤ (#(bohr K delta) : ℝ) * (m : ℝ) ^ K.card := by
    exact_mod_cast hcountNat
  have hgrid : (delta / 2) * (m : ℝ) ≤ 1 := by
    calc
      (delta / 2) * (m : ℝ) ≤ (delta / 2) * (2 * delta⁻¹) :=
        mul_le_mul_of_nonneg_left hm_upper (by positivity)
      _ = 1 := by field_simp
  have hgrid_nonneg : 0 ≤ (delta / 2) * (m : ℝ) :=
    mul_nonneg (by positivity) (by positivity)
  have hgrid_pow : ((delta / 2) * (m : ℝ)) ^ K.card ≤ 1 := by
    simpa using pow_le_pow_left₀ hgrid_nonneg hgrid K.card
  have hlower : (delta / 2) ^ K.card * (N : ℝ) ≤ #(bohr K delta) := by
    calc
      (delta / 2) ^ K.card * (N : ℝ) ≤
          (delta / 2) ^ K.card *
            ((#(bohr K delta) : ℝ) * (m : ℝ) ^ K.card) :=
        mul_le_mul_of_nonneg_left hcount (pow_nonneg (by positivity) _)
      _ = (#(bohr K delta) : ℝ) *
          ((delta / 2) * (m : ℝ)) ^ K.card := by
        rw [mul_pow]
        ring
      _ ≤ (#(bohr K delta) : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hgrid_pow (Nat.cast_nonneg _)
      _ = #(bohr K delta) := mul_one _
  refine ⟨hlower, ?_⟩
  intro hK hthreshold
  have hk : 0 < K.card := Finset.card_pos.mpr hK
  have hk_ne : K.card ≠ 0 := hk.ne'
  have hNreal : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hrootlt :
      (N : ℝ) ^ (-(1 / (K.card : ℝ))) < delta / 2 := by
    nlinarith
  have hrootpow :
      ((N : ℝ) ^ (-(1 / (K.card : ℝ)))) ^ K.card = (N : ℝ)⁻¹ := by
    calc
      ((N : ℝ) ^ (-(1 / (K.card : ℝ)))) ^ K.card =
          (N : ℝ) ^ ((-(1 / (K.card : ℝ))) * (K.card : ℝ)) :=
        (Real.rpow_mul_natCast hNreal.le _ _).symm
      _ = (N : ℝ) ^ (-1 : ℝ) := by
        congr 1
        field_simp
      _ = (N : ℝ)⁻¹ := Real.rpow_neg_one _
  have hpowlt : (N : ℝ)⁻¹ < (delta / 2) ^ K.card := by
    rw [← hrootpow]
    exact pow_lt_pow_left₀ hrootlt (Real.rpow_nonneg hNreal.le _) hk_ne
  have hmass : (1 : ℝ) < (delta / 2) ^ K.card * N := by
    calc
      (1 : ℝ) = (N : ℝ)⁻¹ * N := (inv_mul_cancel₀ hNreal.ne').symm
      _ < (delta / 2) ^ K.card * N := mul_lt_mul_of_pos_right hpowlt hNreal
  have hcardReal : (1 : ℝ) < #(bohr K delta) := hmass.trans_le hlower
  have hcard : 1 < #(bohr K delta) := by exact_mod_cast hcardReal
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  by_cases ha0 : a = 0
  · refine ⟨b, hb, ?_⟩
    have hb0 : b ≠ 0 := fun h => hab (ha0.trans h.symm)
    simpa using hb0
  · refine ⟨a, ha, ?_⟩
    simpa using ha0

/-- Lemma 5.15 is a finite averaging argument: mean zero makes the total
positive discrepancy half the total absolute discrepancy, and pigeonholing
then supplies a large cell. -/
theorem lemma_5_15_holds : lemma_5_15 := by
  intro N M _ f P alpha hM hAlpha hf hmean hpart hlarge
  classical
  let S : Fin M → ℝ := fun j => ∑ s ∈ P j, f s
  have hpair : ((Finset.univ : Finset (Fin M)) : Set (Fin M)).PairwiseDisjoint P := by
    intro i _ j _ hij
    apply hpart.2 i j
    simp [hij]
  have hunion : (Finset.univ : Finset (Fin M)).biUnion P = Finset.univ := by
    ext s
    simpa only [Finset.mem_biUnion, Finset.mem_univ, true_and] using (hpart.1 s).symm
  have hsum : ∑ j, S j = 0 := by
    rw [show (∑ j, S j) = ∑ j ∈ (Finset.univ : Finset (Fin M)), ∑ s ∈ P j, f s by
      simp [S]]
    rw [← Finset.sum_biUnion hpair, hunion]
    simpa using hmean
  have hcardsNat : ∑ j, (P j).card = N := by
    rw [show (∑ j, (P j).card) =
        ∑ j ∈ (Finset.univ : Finset (Fin M)), (P j).card by simp]
    rw [← Finset.card_biUnion hpair, hunion]
    simp
  have hcards : (∑ j, ((P j).card : ℝ)) = N := by exact_mod_cast hcardsNat
  have hS_le_card (j : Fin M) : S j ≤ (P j).card := by
    calc
      S j ≤ ∑ s ∈ P j, |f s| := by
        apply Finset.sum_le_sum
        intro s _
        exact le_abs_self (f s)
      _ ≤ ∑ _s ∈ P j, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro s _
        exact hf s
      _ = (P j).card := by simp
  by_cases hAlphaZero : alpha = 0
  · subst alpha
    have hne : (Finset.univ : Finset (Fin M)).Nonempty := by
      exact ⟨⟨0, hM⟩, Finset.mem_univ _⟩
    obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le hne
      (f := fun _ : Fin M => (0 : ℝ)) (g := S) (by simp [hsum])
    exact ⟨j, by simpa using hj, by simp⟩
  · have hAlphaPos : 0 < alpha := lt_of_le_of_ne hAlpha (Ne.symm hAlphaZero)
    have hNPos : 0 < N := NeZero.pos N
    have hNReal : (0 : ℝ) < N := by exact_mod_cast hNPos
    have hMReal : (0 : ℝ) < M := by exact_mod_cast hM
    let T : ℝ := alpha * N / (4 * M)
    have hTPos : 0 < T := by
      dsimp [T]
      positivity
    by_contra hexists
    have hbad (j : Fin M) :
        S j < alpha * (P j).card / 4 ∨ ((P j).card : ℝ) < T := by
      by_cases hdisc : alpha * (P j).card / 4 ≤ S j
      · right
        by_contra hcard
        exact hexists ⟨j, hdisc, le_of_not_gt hcard⟩
      · exact Or.inl (lt_of_not_ge hdisc)
    have hmax (j : Fin M) :
        max (S j) 0 < alpha * (P j).card / 4 + T := by
      rcases hbad j with hdisc | hcard
      · by_cases hS : 0 ≤ S j
        · rw [max_eq_left hS]
          linarith
        · rw [max_eq_right (le_of_not_ge hS)]
          positivity
      · by_cases hS : 0 ≤ S j
        · rw [max_eq_left hS]
          have := hS_le_card j
          nlinarith [mul_nonneg hAlpha (Nat.cast_nonneg (P j).card)]
        · rw [max_eq_right (le_of_not_ge hS)]
          positivity
    have hne : (Finset.univ : Finset (Fin M)).Nonempty := by
      exact ⟨⟨0, hM⟩, Finset.mem_univ _⟩
    have hmaxsum :
        (∑ j, max (S j) 0) < ∑ j, (alpha * (P j).card / 4 + T) :=
      Finset.sum_lt_sum_of_nonempty hne fun j _ => hmax j
    have hright : (∑ j, (alpha * (P j).card / 4 + T)) = alpha * N / 2 := by
      calc
        _ = (∑ j, (alpha / 4) * (P j).card) + ∑ _j : Fin M, T := by
          rw [Finset.sum_add_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = (alpha / 4) * (∑ j, ((P j).card : ℝ)) + (M : ℝ) * T := by
          rw [Finset.mul_sum]
          simp
        _ = alpha * N / 2 := by
          rw [hcards]
          dsimp [T]
          field_simp
          ring
    rw [hright] at hmaxsum
    have habs (j : Fin M) : |S j| = 2 * max (S j) 0 - S j := by
      rcases le_total 0 (S j) with hS | hS
      · rw [abs_of_nonneg hS, max_eq_left hS]
        ring
      · rw [abs_of_nonpos hS, max_eq_right hS]
        ring
    have habssum : (∑ j, |S j|) = 2 * ∑ j, max (S j) 0 := by
      simp_rw [habs, Finset.sum_sub_distrib, Finset.mul_sum]
      rw [hsum, sub_zero]
    have hlargeS : alpha * N ≤ ∑ j, |S j| := by simpa [S] using hlarge
    rw [habssum] at hlargeS
    linarith

/-- Finite Fubini--Markov interchange in the form used by Lemma 10.7. -/
private theorem almostEvery_swap_of_nonneg {X Y : Type*}
    [DecidableEq X] [DecidableEq Y] (theta : ℝ) (U : Finset X) (V : Finset Y)
    (Q : X → Y → Prop) (htheta : 0 ≤ theta)
    (hcol : ∀ y, y ∈ V → AlmostEvery (1 - theta) U fun x => Q x y) :
    AlmostEvery (1 - Real.sqrt theta) U fun x =>
      AlmostEvery (1 - Real.sqrt theta) V fun y => Q x y := by
  classical
  simp only [AlmostEvery] at hcol ⊢
  let t : ℝ := Real.sqrt theta
  let row : X → ℕ := fun x => (V.filter fun y => Q x y).card
  let col : Y → ℕ := fun y => (U.filter fun x => Q x y).card
  let good : X → Prop := fun x => (1 - t) * V.card ≤ row x
  let G : Finset X := U.filter good
  let H : Finset X := U.filter fun x => ¬good x
  change (1 - t) * U.card ≤ (G.card : ℝ)
  by_cases ht_large : 1 ≤ t
  · exact (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht_large)
      (Nat.cast_nonneg U.card)).trans (Nat.cast_nonneg G.card)
  by_cases ht_zero : t = 0
  · have htheta_zero : theta = 0 := by
      exact (Real.sqrt_eq_zero htheta).mp (by simpa [t] using ht_zero)
    have hQ : ∀ x, x ∈ U → ∀ y, y ∈ V → Q x y := by
      intro x hx y hy
      have hc := hcol y hy
      have hcNat : U.card ≤ (U.filter fun x => Q x y).card := by
        exact_mod_cast (by simpa [htheta_zero] using hc)
      have heq : (U.filter fun x => Q x y) = U :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) hcNat
      have hxfilter : x ∈ U.filter (fun z => Q z y) := by
        rw [heq]
        exact hx
      exact (Finset.mem_filter.mp hxfilter).2
    have hGU : G = U := by
      apply Finset.filter_eq_self.2
      intro x hx
      change (1 - t) * (V.card : ℝ) ≤ (row x : ℝ)
      have hrow : row x = V.card := by
        dsimp [row]
        rw [Finset.filter_eq_self.2]
        exact fun y hy => hQ x hx y hy
      rw [hrow, ht_zero]
      simp
    rw [hGU, ht_zero]
    simp
  have ht_pos : 0 < t := lt_of_le_of_ne (by dsimp [t]; positivity) (Ne.symm ht_zero)
  have ht_lt_one : t < 1 := lt_of_not_ge ht_large
  have htheta_sq : t ^ 2 = theta := by
    dsimp [t]
    exact Real.sq_sqrt htheta
  by_cases hV : V = ∅
  · subst V
    have hGU : G = U := by simp [G, good, row]
    rw [hGU]
    have ht_nonneg : 0 ≤ t := by dsimp [t]; positivity
    have hU_nonneg : (0 : ℝ) ≤ U.card := Nat.cast_nonneg U.card
    nlinarith
  have hVposNat : 0 < V.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hV)
  have hVpos : (0 : ℝ) < V.card := by exact_mod_cast hVposNat
  by_contra hgoal
  have hGlt : (G.card : ℝ) < (1 - t) * U.card := lt_of_not_ge hgoal
  have hGHNat : G.card + H.card = U.card := by
    simpa [G, H] using Finset.card_filter_add_card_filter_not (s := U) good
  have hGH : (G.card : ℝ) + H.card = U.card := by exact_mod_cast hGHNat
  have hlower :
      (1 - theta) * U.card * V.card ≤ ∑ y ∈ V, (col y : ℝ) := by
    calc
      _ = ∑ _y ∈ V, ((1 - theta) * U.card) := by simp; ring
      _ ≤ ∑ y ∈ V, (col y : ℝ) := by
        apply Finset.sum_le_sum
        intro y hy
        simpa [col] using hcol y hy
  have hdouble :
      (∑ y ∈ V, (col y : ℝ)) = ∑ x ∈ U, (row x : ℝ) := by
    dsimp [col, row]
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    push_cast
    rw [Finset.sum_comm]
  have hupper :
      (∑ x ∈ U, (row x : ℝ)) ≤
        (G.card : ℝ) * V.card + H.card * ((1 - t) * V.card) := by
    calc
      _ = (∑ x ∈ U with good x, (row x : ℝ)) +
          ∑ x ∈ U with ¬good x, (row x : ℝ) := by
            exact (Finset.sum_filter_add_sum_filter_not U good
              (fun x => (row x : ℝ))).symm
      _ ≤ (∑ _x ∈ U with good _x, (V.card : ℝ)) +
          ∑ _x ∈ U with ¬good _x, ((1 - t) * V.card) := by
            apply add_le_add
            · apply Finset.sum_le_sum
              intro x _
              exact_mod_cast Finset.card_filter_le V (Q x)
            · apply Finset.sum_le_sum
              intro x hx
              exact le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hx).2)
      _ = (G.card : ℝ) * V.card + H.card * ((1 - t) * V.card) := by
        simp [G, H]
  have hbound :
      (1 - theta) * U.card * V.card ≤
        (G.card : ℝ) * V.card + H.card * ((1 - t) * V.card) := by
    exact hlower.trans (hdouble.le.trans hupper)
  have hpositive :
      0 < (((1 - t) * (U.card : ℝ) - G.card) * t * V.card) := by
    exact mul_pos (mul_pos (sub_pos.mpr hGlt) ht_pos) hVpos
  have hid :
      (1 - theta) * (U.card : ℝ) * V.card -
          ((G.card : ℝ) * V.card + H.card * ((1 - t) * V.card)) =
        ((1 - t) * U.card - G.card) * t * V.card := by
    rw [← htheta_sq, ← hGH]
    ring
  nlinarith

/-- Lemma 10.7 is the preceding finite Fubini--Markov interchange applied to
the local difference relation. -/
theorem lemma_10_7_holds : lemma_10_7 := by
  intro N _ X _ _ D phi W B B' psi eta
  dsimp
  intro hmodel
  rcases hmodel with ⟨_, _, hmodel⟩
  apply almostEvery_swap_of_nonneg
  · apply mul_nonneg (by norm_num)
    by_cases heta : 0 ≤ eta
    · exact Real.rpow_nonneg heta _
    · have heta_neg : eta < 0 := lt_of_not_ge heta
      rw [Real.rpow_def_of_neg heta_neg]
      apply mul_nonneg (Real.exp_pos _).le
      exact (Real.cos_pos_of_mem_Ioo (by
        have hpi := Real.pi_pos
        constructor <;> norm_num <;> nlinarith)).le
  · exact hmodel

/-- Lemma 9.1 is the weighted Hölder inequality with weight and function
both equal to `a i ^ 2`, and exponent seven. -/
theorem lemma_9_1_holds : lemma_9_1 := by
  intro n a ha
  have h := Real.inner_le_weight_mul_Lp_of_nonneg
    (s := (Finset.univ : Finset (Fin n))) (p := (7 : ℝ)) (by norm_num)
    (fun i => a i ^ 2) (fun i => a i ^ 2)
    (fun i => sq_nonneg (a i)) (fun i => sq_nonneg (a i))
  have h4 : (∑ i, a i ^ 2 * a i ^ 2) = ∑ i, a i ^ 4 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h4] at h
  norm_num [Real.rpow_natCast] at h
  ring_nf at h
  exact h

end LeanProofs.GowersSzemeredi
