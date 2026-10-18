import GowersSzemeredi.Proofs05PolynomialPartition
import Mathlib.Analysis.Real.Pi.Bounds
import GowersSzemeredi.Proofs00ExponentialBounds

/-!
# Removing polynomial phases on the Section 5 partition

This module isolates the analytic deduction of Corollary 5.7 from the
target-length partition in Corollary 5.6.  Keeping this implication separate
lets the quantitative Weyl/recurrence proof supply the sole remaining input.

`cor57_alpha_le_one`, `cor57_card_partition`, `cor57_scale_lt`,
`cor57_sum_partition` and `corollary_5_7_holds_of_corollary_5_6` are in
`Proofs05PhaseRemovalSide`, outside the final route. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

attribute [simp] cor57_norm_exponential

attribute [simp] exponential_add

alias cor57_exponential_eq_exp_valMinAbs := cor24_exponential_eq_exp_valMinAbs

lemma cor57_centeredAbs_neg_natCast_le {N i : Nat} [NeZero N] :
    centeredAbs (-(i : ZMod N)) ≤ i := by
  rw [centeredAbs, ZMod.natAbs_valMinAbs_neg]
  exact lemma55_centeredAbs_natCast_le

lemma cor57_phase_close_of_mem_interval {N d : Nat} [NeZero N]
    (a y : ZMod N) (hy : y ∈ (modInterval N a (d + 1)).carrier) :
    ‖exponential (-y) - exponential (-a)‖ ≤
      2 * Real.pi * d / N := by
  unfold ModAP.carrier modInterval at hy
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy
  obtain ⟨i, rfl⟩ := hy
  have hi : (i : Nat) ≤ d := by omega
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  simp only [mul_one]
  calc
    ‖exponential (-(a + (i : ZMod N))) - exponential (-a)‖ =
        ‖exponential (-a) * (exponential (-(i : ZMod N)) - 1)‖ := by
      congr 1
      rw [show -(a + (i : ZMod N)) = -a + -(i : ZMod N) by ring, exponential_add]
      ring
    _ = ‖exponential (-(i : ZMod N)) - 1‖ := by
      rw [norm_mul, cor57_norm_exponential, one_mul]
    _ ≤ 2 * Real.pi * centeredAbs (-(i : ZMod N)) / N :=
      cor57_norm_exponential_sub_one_le _
    _ ≤ 2 * Real.pi * d / N := by
      apply div_le_div_of_nonneg_right _ hN.le
      gcongr
      exact_mod_cast
        (cor57_centeredAbs_neg_natCast_le (N := N) (i := (i : Nat))).trans hi

lemma cor57_partition_constant_pos (k : Nat) :
    0 < polynomialPartitionConstant k := by
  unfold polynomialPartitionConstant
  positivity

lemma cor57_cell_norm_le {N : Nat} [NeZero N]
    (S : Finset Nat) (f : ZMod N → Complex) (phi : ZMod N → ZMod N)
    (alpha scale : Real) (hf : DiscValued f)
    (hdiam : diameterAtMostReal (S.image fun x : Nat => phi (x : ZMod N)) scale)
    (hscale : scale ≤ alpha * N / (4 * Real.pi)) :
    ‖∑ s ∈ S, f (s : ZMod N) * exponential (-(phi (s : ZMod N)))‖ ≤
      ‖∑ s ∈ S, f (s : ZMod N)‖ + alpha / 2 * S.card := by
  obtain ⟨d, ⟨a, hsubset⟩, hdscale⟩ := hdiam
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hphase (s : Nat) (hs : s ∈ S) :
      ‖exponential (-(phi (s : ZMod N))) - exponential (-a)‖ ≤ alpha / 2 := by
    have himage : phi (s : ZMod N) ∈
        S.image (fun x : Nat => phi (x : ZMod N)) :=
      Finset.mem_image.mpr ⟨s, hs, rfl⟩
    calc
      _ ≤ 2 * Real.pi * d / N :=
        cor57_phase_close_of_mem_interval a _ (hsubset himage)
      _ ≤ 2 * Real.pi * scale / N := by gcongr
      _ ≤ alpha / 2 := by
        have hpi : (0 : Real) < 4 * Real.pi := by positivity
        have hscaled : scale * (4 * Real.pi) ≤ alpha * N :=
          (le_div_iff₀ hpi).1 hscale
        apply (div_le_iff₀ hN).2
        nlinarith [Real.pi_pos]
  let twisted := ∑ s ∈ S,
    f (s : ZMod N) * exponential (-(phi (s : ZMod N)))
  let plain := ∑ s ∈ S, f (s : ZMod N)
  let err := ∑ s ∈ S,
    f (s : ZMod N) *
      (exponential (-(phi (s : ZMod N))) - exponential (-a))
  have hdecomp : twisted = exponential (-a) * plain + err := by
    dsimp only [twisted, plain, err]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    ring
  have herr : ‖err‖ ≤ alpha / 2 * S.card := by
    dsimp only [err]
    calc
      _ ≤ ∑ s ∈ S,
          ‖f (s : ZMod N) *
            (exponential (-(phi (s : ZMod N))) - exponential (-a))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _s ∈ S, alpha / 2 := by
        apply Finset.sum_le_sum
        intro s hs
        rw [norm_mul]
        calc
          ‖f (s : ZMod N)‖ *
              ‖exponential (-(phi (s : ZMod N))) - exponential (-a)‖ ≤
              1 * (alpha / 2) :=
            mul_le_mul (hf _) (hphase s hs) (norm_nonneg _) (by norm_num)
          _ = alpha / 2 := one_mul _
      _ = alpha / 2 * S.card := by simp [mul_comm]
  change ‖twisted‖ ≤ ‖plain‖ + alpha / 2 * S.card
  rw [hdecomp]
  calc
    ‖exponential (-a) * plain + err‖ ≤
        ‖exponential (-a) * plain‖ + ‖err‖ := norm_add_le _ _
    _ ≤ ‖plain‖ + alpha / 2 * S.card := by
      rw [norm_mul, cor57_norm_exponential, one_mul]
      gcongr

end LeanProofs.GowersSzemeredi
