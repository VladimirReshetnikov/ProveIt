/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import OAI.Combinatorics.Progressions.Geometry.BoxBlockBudget
import OAI.Combinatorics.Progressions.Lattices.ComparableResidueProgressionPartition

namespace OAI

section

namespace Erdos3

noncomputable def exponentialProgressionScale (N q : ℕ) (p : ℝ) : ℕ :=
  ⌊(N : ℝ) / (8 * q * Real.exp (2 * p))⌋₊

theorem exponentialProgressionScale_bounds (N q : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hqexp : (q : ℝ) ≤ Real.exp p)
    (hN : Real.exp (3 * p + 16) ≤ (N : ℝ)) :
    0 < exponentialProgressionScale N q p ∧
      q * exponentialProgressionScale N q p ≤ N ∧
      (N : ℝ) * Real.exp (-(3 * p + 16)) ≤ exponentialProgressionScale N q p ∧
      2 * (q : ℝ) * exponentialProgressionScale N q p / N ≤
        Real.exp (-(2 * p)) / 4 := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have he : 0 < Real.exp (2 * p) := Real.exp_pos _
  have he1 : 1 ≤ Real.exp (2 * p) := Real.one_le_exp (by positivity)
  have hden : 0 < 8 * (q : ℝ) * Real.exp (2 * p) := by positivity
  have hexp16 : (16 : ℝ) ≤ Real.exp 16 := by
    have := Real.add_one_le_exp (16 : ℝ)
    linarith
  have hlarge : 16 * (q : ℝ) * Real.exp (2 * p) ≤ Real.exp (3 * p + 16) := by
    calc
      16 * (q : ℝ) * Real.exp (2 * p) ≤
          Real.exp 16 * Real.exp p * Real.exp (2 * p) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hexp16 hqexp (by positivity) (Real.exp_nonneg _)) he.le
      _ = Real.exp (3 * p + 16) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hnr : (0 : ℝ) < N := (Real.exp_pos _).trans_le hN
  let x : ℝ := N / (8 * q * Real.exp (2 * p))
  have hx2 : 2 ≤ x := (le_div_iff₀ hden).mpr (by nlinarith [hlarge.trans hN])
  have hfloor : (exponentialProgressionScale N q p : ℝ) ≤ x :=
    Nat.floor_le (le_trans (by norm_num) hx2)
  have hhalf : x / 2 ≤ (exponentialProgressionScale N q p : ℝ) := by
    have := Nat.lt_floor_add_one x
    change x < (exponentialProgressionScale N q p : ℝ) + 1 at this
    linarith
  have hH : 0 < exponentialProgressionScale N q p := by
    have : (0 : ℝ) < exponentialProgressionScale N q p := by linarith
    exact_mod_cast this
  have hupper : (exponentialProgressionScale N q p : ℝ) *
      (8 * q * Real.exp (2 * p)) ≤ N := (le_div_iff₀ hden).mp hfloor
  have hfit : q * exponentialProgressionScale N q p ≤ N := by
    have : (q : ℝ) * exponentialProgressionScale N q p ≤ N := by
      have hnonneg : (0 : ℝ) ≤ exponentialProgressionScale N q p := by positivity
      nlinarith
    exact_mod_cast this
  refine ⟨hH, hfit, ?_, ?_⟩
  · calc
      (N : ℝ) * Real.exp (-(3 * p + 16)) = N / Real.exp (3 * p + 16) := by
        rw [Real.exp_neg, div_eq_mul_inv]
      _ ≤ N / (16 * q * Real.exp (2 * p)) :=
        div_le_div_of_nonneg_left hnr.le (by positivity) hlarge
      _ = x / 2 := by dsimp [x]; ring
      _ ≤ _ := hhalf
  · apply (div_le_iff₀ hnr).mpr
    rw [Real.exp_neg]
    have heq : (Real.exp (2 * p))⁻¹ / 4 * (N : ℝ) = N / (4 * Real.exp (2 * p)) := by ring
    rw [heq]
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.exp (2 * p))).mpr
    nlinarith

end Erdos3

end

section

namespace Erdos3.FiniteProgressionPartition

theorem normalized_point_sub_point_le {N q H : ℕ}
    (P : FiniteProgressionPartition N) (k : P.Label)
    (hstep : P.step k = q) (hlen : P.length k < 2 * H) (hN : 0 < N)
    (j l : Fin (P.length k)) :
    |((P.point k j).val : ℝ) / N - ((P.point k l).val : ℝ) / N| ≤
      2 * q * H / N := by
  have hj : (j.val : ℝ) ≤ 2 * H := by exact_mod_cast (by omega : j.val ≤ 2 * H)
  have hl : (l.val : ℝ) ≤ 2 * H := by exact_mod_cast (by omega : l.val ≤ 2 * H)
  have hj0 : 0 ≤ (j.val : ℝ) := Nat.cast_nonneg _
  have hl0 : 0 ≤ (l.val : ℝ) := Nat.cast_nonneg _
  have hdiff : |(j.val : ℝ) - l.val| ≤ 2 * H :=
    abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have hfactor : 0 ≤ (q : ℝ) / N := by positivity
  calc
    _ = (q : ℝ) / N * |(j.val : ℝ) - l.val| := by
      rw [P.point_val, P.point_val, hstep]
      push_cast
      rw [← sub_div, show ((P.start k : ℝ) + q * j.val) -
        (P.start k + q * l.val) = q * ((j.val : ℝ) - l.val) by ring]
      simp only [abs_div, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q),
        abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      ring
    _ ≤ (q : ℝ) / N * (2 * H) := mul_le_mul_of_nonneg_left hdiff hfactor
    _ = 2 * q * H / N := by ring

theorem normalized_point_sub_point_le_of_bound {N q H : ℕ} {ε : ℝ}
    (P : FiniteProgressionPartition N) (k : P.Label)
    (hstep : P.step k = q) (hlen : P.length k < 2 * H) (hN : 0 < N)
    (hbound : (2 : ℝ) * q * H / N ≤ ε) (j l : Fin (P.length k)) :
    |((P.point k j).val : ℝ) / N - ((P.point k l).val : ℝ) / N| ≤ ε :=
  (normalized_point_sub_point_le P k hstep hlen hN j l).trans hbound

theorem normalized_point_sub_start_le {N q H : ℕ}
    (P : FiniteProgressionPartition N) (k : P.Label)
    (hstep : P.step k = q) (hlen : P.length k < 2 * H) (hN : 0 < N)
    (j : Fin (P.length k)) :
    |((P.point k j).val : ℝ) / N - (P.start k : ℝ) / N| ≤ 2 * q * H / N := by
  let z : Fin (P.length k) := ⟨0, Nat.zero_lt_of_lt j.isLt⟩
  have hz : (P.point k z).val = P.start k := by simp [z]
  simpa only [hz] using normalized_point_sub_point_le P k hstep hlen hN j z

theorem normalized_point_sub_start_le_of_bound {N q H : ℕ} {ε : ℝ}
    (P : FiniteProgressionPartition N) (k : P.Label)
    (hstep : P.step k = q) (hlen : P.length k < 2 * H) (hN : 0 < N)
    (hbound : (2 : ℝ) * q * H / N ≤ ε) (j : Fin (P.length k)) :
    |((P.point k j).val : ℝ) / N - (P.start k : ℝ) / N| ≤ ε :=
  (normalized_point_sub_start_le P k hstep hlen hN j).trans hbound

end Erdos3.FiniteProgressionPartition

end

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProgressionPartition

theorem label_card_mul_le_of_length_lower {N : ℕ} (P : FiniteProgressionPartition N)
    {H : ℝ} (hlength : ∀ a, H ≤ (P.length a : ℝ)) :
    (Fintype.card P.Label : ℝ) * H ≤ N := by
  have hsum : (∑ a, P.length a) = N := by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using Fintype.card_congr P.equiv
  calc
    _ = ∑ _a : P.Label, H := by simp
    _ ≤ ∑ a : P.Label, (P.length a : ℝ) := Finset.sum_le_sum (fun a _ => hlength a)
    _ = N := by exact_mod_cast hsum

theorem label_card_le_exp_of_length_lower {N : ℕ} (P : FiniteProgressionPartition N)
    (hN : 0 < N) {A : ℝ} (hlength : ∀ a, (N : ℝ) * Real.exp (-A) ≤ P.length a) :
    (Fintype.card P.Label : ℝ) ≤ Real.exp A := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  apply (mul_le_mul_iff_left₀ (mul_pos hNr (Real.exp_pos (-A)))).mp
  calc
    _ ≤ (N : ℝ) := P.label_card_mul_le_of_length_lower hlength
    _ = (N : ℝ) * (Real.exp A * Real.exp (-A)) := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    _ = Real.exp A * ((N : ℝ) * Real.exp (-A)) := by ring

end FiniteProgressionPartition

theorem exists_normalizedTwist_parameter_partition {I : Type*} [Fintype I]
    [DecidableEq I] (N : I → ℕ) (q : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hqexp : (q : ℝ) ≤ Real.exp p)
    (hN : ∀ i, Real.exp (3 * p + 16) ≤ (N i : ℝ)) :
    ∃ P : ∀ i, FiniteProgressionPartition (N i),
      (∀ i a, (P i).step a = q) ∧
      (∀ i a, 0 < (P i).length a) ∧
      (∀ i a, (N i : ℝ) * Real.exp (-(3 * p + 16)) ≤ (P i).length a) ∧
      (∀ i a (j : Fin ((P i).length a)),
        |((P i).point a j).val / (N i : ℝ) - (P i).start a / (N i : ℝ)| ≤
          Real.exp (-(2 * p)) / 4) ∧
      (∀ i a (j k : Fin ((P i).length a)),
        |((P i).point a j).val / (N i : ℝ) - ((P i).point a k).val / (N i : ℝ)| ≤
          Real.exp (-(2 * p)) / 4) ∧
      (∀ i, (Fintype.card (P i).Label : ℝ) ≤ Real.exp (3 * p + 16)) ∧
      (Fintype.card (∀ i, (P i).Label) : ℝ) ≤
        Real.exp ((Fintype.card I : ℝ) * (3 * p + 16)) := by
  classical
  let H := fun i => exponentialProgressionScale (N i) q p
  have hscale (i : I) := exponentialProgressionScale_bounds (N i) q p hp hq hqexp (hN i)
  let P : ∀ i, FiniteProgressionPartition (N i) := fun i =>
    FiniteProgressionPartition.comparableResidueProgressions (N i) q (H i) hq
      (hscale i).1 (hscale i).2.1
  have hstep (i : I) (a : (P i).Label) : (P i).step a = q :=
    FiniteProgressionPartition.comparableResidueProgressions_step _ _ _ _ _ _ _
  have hlength (i : I) (a : (P i).Label) :
      H i ≤ (P i).length a ∧ (P i).length a < 2 * H i :=
    FiniteProgressionPartition.comparableResidueProgressions_length_bounds _ _ _ _ _ _ _
  have hNpos (i : I) : 0 < N i := by
    exact_mod_cast (Real.exp_pos _).trans_le (hN i)
  have hlower (i : I) (a : (P i).Label) :
      (N i : ℝ) * Real.exp (-(3 * p + 16)) ≤ (P i).length a :=
    (hscale i).2.2.1.trans (by exact_mod_cast (hlength i a).1)
  have hcard (i : I) : (Fintype.card (P i).Label : ℝ) ≤ Real.exp (3 * p + 16) :=
    (P i).label_card_le_exp_of_length_lower (hNpos i) (hlower i)
  refine ⟨P, hstep, fun i a => (hscale i).1.trans_le (hlength i a).1, hlower,
    ?_, ?_, hcard, ?_⟩
  · intro i a j
    exact (P i).normalized_point_sub_start_le_of_bound a (hstep i a)
      (hlength i a).2 (hNpos i) (hscale i).2.2.2 j
  · intro i a j k
    exact (P i).normalized_point_sub_point_le_of_bound a (hstep i a)
      (hlength i a).2 (hNpos i) (hscale i).2.2.2 j k
  · calc
      _ = ∏ i, (Fintype.card (P i).Label : ℝ) := by rw [Fintype.card_pi, Nat.cast_prod]
      _ ≤ ∏ _i : I, Real.exp (3 * p + 16) :=
        Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hcard i)
      _ = Real.exp ((Fintype.card I : ℝ) * (3 * p + 16)) := by
        rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]

end Erdos3

end

end OAI
