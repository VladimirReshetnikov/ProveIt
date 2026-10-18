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
  -- every phase on the cell is within `alpha / 2` of `e(-a)`
  have hphase (s : Nat) (hs : s ∈ S) :
      ‖exponential (-(phi (s : ZMod N))) - exponential (-a)‖ ≤ alpha / 2 := by
    refine (cor57_phase_close_of_mem_interval a _
      (hsubset (Finset.mem_image_of_mem _ hs))).trans ?_
    rw [div_le_iff₀ hN]
    rw [le_div_iff₀ (by positivity)] at hscale
    linarith [mul_le_mul_of_nonneg_left hdscale Real.pi_pos.le]
  calc ‖∑ s ∈ S, f (s : ZMod N) * exponential (-(phi (s : ZMod N)))‖ =
        ‖exponential (-a) * ∑ s ∈ S, f (s : ZMod N) + ∑ s ∈ S,
          f (s : ZMod N) * (exponential (-(phi (s : ZMod N))) - exponential (-a))‖ := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact congrArg _ (Finset.sum_congr rfl fun s _ => by ring)
    _ ≤ ‖∑ s ∈ S, f (s : ZMod N)‖ + ∑ s ∈ S,
          ‖f (s : ZMod N) * (exponential (-(phi (s : ZMod N))) - exponential (-a))‖ :=
        (norm_add_le _ _).trans (add_le_add (by rw [norm_mul, cor57_norm_exponential, one_mul])
          (norm_sum_le _ _))
    _ ≤ ‖∑ s ∈ S, f (s : ZMod N)‖ + ∑ _s ∈ S, alpha / 2 := by
        gcongr with s hs
        rw [norm_mul]
        exact (mul_le_mul (hf _) (hphase s hs) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = _ := by simp [mul_comm]

end LeanProofs.GowersSzemeredi
