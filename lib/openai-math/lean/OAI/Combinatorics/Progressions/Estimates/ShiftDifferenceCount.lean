/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.CorrelationDerivative

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem finite_support_shift_sum {V : Type*} [AddCommMonoid V]
    (Q T : Finset G) (f : G → V) (s : G)
    (hsupport : ∀ x, x ∉ Q → f x = 0)
    (hcover : ∀ x ∈ Q, x + s ∈ T) :
    (∑ x ∈ T, f (x - s)) = ∑ x ∈ Q, f x := by
  have hsub : Q.image (fun x => x + s) ⊆ T := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact hcover y hy
  calc
    _ = ∑ x ∈ Q.image (fun x => x + s), f (x - s) := by
      symm
      apply Finset.sum_subset hsub
      intro x _ hx
      apply hsupport
      intro hq
      exact hx (Finset.mem_image.mpr ⟨x - s, hq, sub_add_cancel x s⟩)
    _ = ∑ x ∈ Q, f x := by
      rw [Finset.sum_image (fun _ _ _ _ h => add_right_cancel h)]
      simp

noncomputable def shiftCorrelation (Q : Finset G) (f : G → ℂ) (h : G) : ℂ :=
  ∑ x ∈ Q, f x * star (f (x + h))

theorem finite_support_shift_pair (Q T : Finset G) (f : G → ℂ) (s t : G)
    (hsupport : ∀ x, x ∉ Q → f x = 0)
    (hcover : ∀ x ∈ Q, x + s ∈ T) :
    (∑ x ∈ T, f (x - s) * star (f (x - t))) = shiftCorrelation Q f (s - t) := by
  have hid (x : G) : x - s + (s - t) = x - t := by abel
  simpa only [shiftCorrelation, hid] using finite_support_shift_sum Q T
    (fun x => f x * star (f (x + (s - t)))) s
    (fun x hx => by rw [hsupport x hx, zero_mul]) hcover

theorem norm_sum_sq_le_card_mul_sum_norm_sq {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    ‖∑ x ∈ S, f x‖ ^ 2 ≤ (S.card : ℝ) * ∑ x ∈ S, ‖f x‖ ^ 2 := by
  have hnorm := norm_sum_le S f
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun x => ‖f x‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans (by simpa only [mul_comm] using hcs)

theorem finite_shift_energy (Q T S : Finset G) (f : G → ℂ)
    (hsupport : ∀ x, x ∉ Q → f x = 0)
    (hcover : ∀ s ∈ S, ∀ x ∈ Q, x + s ∈ T) :
    (∑ x ∈ T, ‖∑ s ∈ S, f (x - s)‖ ^ 2) =
      ∑ s ∈ S, ∑ t ∈ S, (shiftCorrelation Q f (s - t)).re := by
  have heq : (∑ x ∈ T, (∑ s ∈ S, f (x - s)) * star (∑ t ∈ S, f (x - t))) =
      ∑ s ∈ S, ∑ t ∈ S, shiftCorrelation Q f (s - t) := by
    conv_rhs => rw [Finset.sum_comm]
    simp only [star_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    exact finite_support_shift_pair Q T f t s hsupport (hcover t ht)
  simpa only [Complex.re_sum, mul_star_re_eq_norm_sq] using congrArg Complex.re heq

theorem finite_shift_cauchy (Q T S : Finset G) (f : G → ℂ)
    (hsupport : ∀ x, x ∉ Q → f x = 0)
    (hcover : ∀ s ∈ S, ∀ x ∈ Q, x + s ∈ T) :
    (S.card : ℝ) ^ 2 * ‖∑ x ∈ Q, f x‖ ^ 2 ≤
      (T.card : ℝ) * ∑ s ∈ S, ∑ t ∈ S, (shiftCorrelation Q f (s - t)).re := by
  have hsum : (∑ x ∈ T, ∑ s ∈ S, f (x - s)) = (S.card : ℂ) * ∑ x ∈ Q, f x := by
    rw [Finset.sum_comm]
    have hshift : ∀ s ∈ S, (∑ x ∈ T, f (x - s)) = ∑ x ∈ Q, f x :=
      fun s hs => finite_support_shift_sum Q T f s hsupport (hcover s hs)
    rw [Finset.sum_congr rfl hshift]
    simp
  have hcs := norm_sum_sq_le_card_mul_sum_norm_sq T (fun x => ∑ s ∈ S, f (x - s))
  rw [hsum, norm_mul, Complex.norm_natCast, mul_pow,
    finite_shift_energy Q T S f hsupport hcover] at hcs
  exact hcs

theorem finite_shift_cauchy_norm (Q T S : Finset G) (f : G → ℂ)
    (hsupport : ∀ x, x ∉ Q → f x = 0)
    (hcover : ∀ s ∈ S, ∀ x ∈ Q, x + s ∈ T) :
    (S.card : ℝ) ^ 2 * ‖∑ x ∈ Q, f x‖ ^ 2 ≤
      (T.card : ℝ) * ∑ s ∈ S, ∑ t ∈ S, ‖shiftCorrelation Q f (s - t)‖ := by
  apply (finite_shift_cauchy Q T S f hsupport hcover).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro s _
  exact Finset.sum_le_sum (fun t _ => Complex.re_le_norm _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
theorem shiftCorrelation_zero_norm_le (Q : Finset G) (f : G → ℂ)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) : ‖shiftCorrelation Q f 0‖ ≤ Q.card := by
  unfold shiftCorrelation
  calc
    _ ≤ ∑ x ∈ Q, ‖f x * star (f (x + 0))‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ Q, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      simp only [add_zero, norm_mul, norm_star]
      exact (mul_le_mul (hf x hx) (hf x hx) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = (Q.card : ℝ) := by simp

theorem exists_large_shift_pair (Q T S : Finset G) (f : G → ℂ)
    (hQ : Q.Nonempty) (hsupport : ∀ x, x ∉ Q → f x = 0)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1)
    (hcover : ∀ s ∈ S, ∀ x ∈ Q, x + s ∈ T)
    (hT : T.card ≤ 2 * Q.card)
    {δ : ℝ} (hδ : 0 < δ) (hshift : 8 ≤ δ ^ 2 * S.card)
    (hscore : δ * Q.card ≤ ‖∑ x ∈ Q, f x‖) :
    ∃ s ∈ S, ∃ t ∈ S, s ≠ t ∧
      δ ^ 2 * Q.card / 4 ≤ ‖shiftCorrelation Q f (s - t)‖ := by
  have hN : (0 : ℝ) < Q.card := by exact_mod_cast hQ.card_pos
  have hS : S.Nonempty := by
    by_contra hs
    rw [Finset.not_nonempty_iff_eq_empty.mp hs] at hshift
    norm_num at hshift
  have hH : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hTR : (T.card : ℝ) ≤ 2 * Q.card := by exact_mod_cast hT
  by_contra hnone
  push Not at hnone
  have hterm (s : G) (hs : s ∈ S) (t : G) (ht : t ∈ S) :
      ‖shiftCorrelation Q f (s - t)‖ ≤ δ ^ 2 * Q.card / 4 +
        if s = t then (Q.card : ℝ) else 0 := by
    by_cases heq : s = t
    · subst t
      simp only [sub_self, ite_true]
      have hdiag := shiftCorrelation_zero_norm_le Q f hf
      have hnonneg : 0 ≤ δ ^ 2 * Q.card / 4 := by positivity
      linarith
    · simp only [ite_eq_right heq, add_zero]
      exact (hnone s hs t ht heq).le
  have hsum : (∑ s ∈ S, ∑ t ∈ S, ‖shiftCorrelation Q f (s - t)‖) ≤
      (S.card : ℝ) ^ 2 * (δ ^ 2 * Q.card / 4) + S.card * Q.card := by
    calc
      _ ≤ ∑ s ∈ S, ∑ t ∈ S,
          (δ ^ 2 * Q.card / 4 + if s = t then (Q.card : ℝ) else 0) :=
        Finset.sum_le_sum (fun s hs => Finset.sum_le_sum (fun t ht => hterm s hs t ht))
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        simp only [Finset.sum_ite_eq]
        rw [Finset.sum_congr rfl (fun s hs => by rw [ite_eq_left hs])]
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  have hupper := (finite_shift_cauchy_norm Q T S f hsupport hcover).trans
    (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _))
  have hupper' := hupper.trans (mul_le_mul_of_nonneg_right hTR
    (show 0 ≤ (S.card : ℝ) ^ 2 * (δ ^ 2 * Q.card / 4) + S.card * Q.card by positivity))
  have hlower := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (mul_nonneg hδ.le hN.le) hscore 2) (sq_nonneg (S.card : ℝ))
  have hcombined := hlower.trans hupper'
  have hshift' := mul_le_mul_of_nonneg_right hshift
    (mul_nonneg hH.le (sq_nonneg (Q.card : ℝ)))
  have hpos : 0 < (S.card : ℝ) * (Q.card : ℝ) ^ 2 := mul_pos hH (sq_pos_of_pos hN)
  nlinarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem shiftCorrelation_norm_le (Q : Finset G) (f : G → ℂ)
    (hsupport : ∀ x, x ∉ Q → f x = 0) (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (h : G) :
    ‖shiftCorrelation Q f h‖ ≤ Q.card := by
  have hall (x : G) : ‖f x‖ ≤ 1 := by
    by_cases hx : x ∈ Q
    · exact hf x hx
    · simp only [hsupport x hx, norm_zero, zero_le_one]
  unfold shiftCorrelation
  calc
    _ ≤ ∑ x ∈ Q, ‖f x * star (f (x + h))‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ Q, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_mul, norm_star]
      exact (mul_le_mul (hf x hx) (hall (x + h)) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = (Q.card : ℝ) := by simp

theorem many_large_shift_pairs (Q T S : Finset G) (f : G → ℂ)
    (hQ : Q.Nonempty) (hsupport : ∀ x, x ∉ Q → f x = 0)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1)
    (hcover : ∀ s ∈ S, ∀ x ∈ Q, x + s ∈ T)
    (hT : T.card ≤ 2 * Q.card)
    {δ : ℝ} (hδ : 0 < δ) (hshift : 8 ≤ δ ^ 2 * S.card)
    (hscore : δ * Q.card ≤ ‖∑ x ∈ Q, f x‖) :
    δ ^ 2 * (S.card : ℝ) ^ 2 / 8 ≤
      (((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧
        δ ^ 2 * Q.card / 8 ≤ ‖shiftCorrelation Q f (p.1 - p.2)‖)).card : ℝ) := by
  let good := (S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧
    δ ^ 2 * Q.card / 8 ≤ ‖shiftCorrelation Q f (p.1 - p.2)‖)
  have hN : (0 : ℝ) < Q.card := by exact_mod_cast hQ.card_pos
  have hS : S.Nonempty := by
    by_contra hs
    rw [Finset.not_nonempty_iff_eq_empty.mp hs] at hshift
    norm_num at hshift
  have hH : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hTR : (T.card : ℝ) ≤ 2 * Q.card := by exact_mod_cast hT
  have hterm (p : G × G) : ‖shiftCorrelation Q f (p.1 - p.2)‖ ≤
      δ ^ 2 * Q.card / 8 +
        (if p.1 ≠ p.2 ∧ δ ^ 2 * Q.card / 8 ≤ ‖shiftCorrelation Q f (p.1 - p.2)‖
          then (Q.card : ℝ) else 0) +
        (if p.1 = p.2 then (Q.card : ℝ) else 0) := by
    have hbound := shiftCorrelation_norm_le Q f hsupport hf (p.1 - p.2)
    have hnonneg : 0 ≤ δ ^ 2 * Q.card / 8 := by positivity
    by_cases heq : p.1 = p.2
    · simp only [heq, ne_eq, not_true_eq_false, false_and, ite_false, ite_true]
      rw [heq] at hbound
      linarith
    · by_cases hlarge : δ ^ 2 * Q.card / 8 ≤ ‖shiftCorrelation Q f (p.1 - p.2)‖
      · simp only [heq, ne_eq, not_false_eq_true, hlarge, and_self, ite_true, ite_false]
        linarith
      · simp only [heq, ne_eq, not_false_eq_true, hlarge, and_false, ite_false]
        linarith
  have hgood : (∑ p ∈ S ×ˢ S,
      if p.1 ≠ p.2 ∧ δ ^ 2 * Q.card / 8 ≤ ‖shiftCorrelation Q f (p.1 - p.2)‖
        then (Q.card : ℝ) else 0) = good.card * (Q.card : ℝ) := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, good]
  have hdiag : (∑ p ∈ S ×ˢ S, if p.1 = p.2 then (Q.card : ℝ) else 0) =
      (S.card : ℝ) * Q.card := by
    rw [Finset.sum_product]
    simp only [Finset.sum_ite_eq]
    rw [Finset.sum_congr rfl (fun s hs => by rw [ite_eq_left hs])]
    simp
  have hsum : (∑ s ∈ S, ∑ t ∈ S, ‖shiftCorrelation Q f (s - t)‖) ≤
      (S.card : ℝ) ^ 2 * (δ ^ 2 * Q.card / 8) + good.card * (Q.card : ℝ) + S.card * Q.card := by
    rw [← Finset.sum_product S S (fun p : G × G => ‖shiftCorrelation Q f (p.1 - p.2)‖)]
    apply (Finset.sum_le_sum (fun p (_ : p ∈ S ×ˢ S) => hterm p)).trans_eq
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hgood, hdiag]
    simp only [Finset.sum_const, Finset.card_product, Nat.cast_mul, nsmul_eq_mul]
    ring
  have hupper := (finite_shift_cauchy_norm Q T S f hsupport hcover).trans
    (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _))
  have hupper' := hupper.trans (mul_le_mul_of_nonneg_right hTR
    (show 0 ≤ (S.card : ℝ) ^ 2 * (δ ^ 2 * Q.card / 8) + good.card * (Q.card : ℝ) +
      S.card * Q.card by positivity))
  have hlower := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (mul_nonneg hδ.le hN.le) hscore 2) (sq_nonneg (S.card : ℝ))
  have hcombined := hlower.trans hupper'
  have hshift' := mul_le_mul_of_nonneg_right hshift
    (mul_nonneg hH.le (sq_nonneg (Q.card : ℝ)))
  change δ ^ 2 * (S.card : ℝ) ^ 2 / 8 ≤ (good.card : ℝ)
  by_contra hnone
  have hsmall := mul_lt_mul_of_pos_right (lt_of_not_ge hnone) (sq_pos_of_pos hN)
  have hpos : 0 < (S.card : ℝ) * (Q.card : ℝ) ^ 2 := mul_pos hH (sq_pos_of_pos hN)
  nlinarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem card_pairs_le_card_differences_mul (S : Finset G) (A : Finset (G × G))
    (hA : A ⊆ S ×ˢ S) :
    A.card ≤ (A.image (fun p => p.1 - p.2)).card * S.card := by
  let f (p : G × G) := (p.1 - p.2, p.2)
  have hf : Function.Injective f := by
    intro p q heq
    have hdiff := congrArg Prod.fst heq
    have hsecond := congrArg Prod.snd heq
    change p.1 - p.2 = q.1 - q.2 at hdiff
    change p.2 = q.2 at hsecond
    apply Prod.ext
    · rw [hsecond] at hdiff
      have := congrArg (fun x : G => x + q.2) hdiff
      simpa only [sub_add_cancel] using this
    · exact hsecond
  have hsub : A.image f ⊆ (A.image (fun p => p.1 - p.2)) ×ˢ S := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨q, hq, rfl⟩, (Finset.mem_product.mp (hA hq)).2⟩
  calc
    _ = (A.image f).card := (Finset.card_image_of_injective A hf).symm
    _ ≤ ((A.image (fun p => p.1 - p.2)) ×ˢ S).card := Finset.card_le_card hsub
    _ = _ := Finset.card_product _ _

theorem many_large_shift_differences (Q T S : Finset G) (f : G → ℂ)
    (hQ : Q.Nonempty) (hsupport : ∀ x, x ∉ Q → f x = 0)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1)
    (hcover : ∀ s ∈ S, ∀ x ∈ Q, x + s ∈ T)
    (hT : T.card ≤ 2 * Q.card)
    {δ : ℝ} (hδ : 0 < δ) (hshift : 8 ≤ δ ^ 2 * S.card)
    (hscore : δ * Q.card ≤ ‖∑ x ∈ Q, f x‖) :
    ∃ D : Finset G, δ ^ 2 * S.card / 8 ≤ (D.card : ℝ) ∧
      ∀ h ∈ D, h ≠ 0 ∧ (∃ s ∈ S, ∃ t ∈ S, h = s - t) ∧
        δ ^ 2 * Q.card / 8 ≤ ‖shiftCorrelation Q f h‖ := by
  let good := (S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧
    δ ^ 2 * Q.card / 8 ≤ ‖shiftCorrelation Q f (p.1 - p.2)‖)
  let D := good.image (fun p => p.1 - p.2)
  have hS : S.Nonempty := by
    by_contra hs
    rw [Finset.not_nonempty_iff_eq_empty.mp hs] at hshift
    norm_num at hshift
  have hH : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hpairs : δ ^ 2 * (S.card : ℝ) ^ 2 / 8 ≤ (good.card : ℝ) :=
    many_large_shift_pairs Q T S f hQ hsupport hf hcover hT hδ hshift hscore
  have hcount : (good.card : ℝ) ≤ (D.card : ℝ) * S.card := by
    exact_mod_cast card_pairs_le_card_differences_mul S good (Finset.filter_subset _ _)
  refine ⟨D, ?_, ?_⟩
  · apply (mul_le_mul_iff_left₀ hH).mp
    calc
      _ = δ ^ 2 * (S.card : ℝ) ^ 2 / 8 := by ring
      _ ≤ (D.card : ℝ) * S.card := hpairs.trans hcount
  · intro h hh
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
    obtain ⟨hpS, hpne, hpbound⟩ := Finset.mem_filter.mp hp
    obtain ⟨hps, hpt⟩ := Finset.mem_product.mp hpS
    exact ⟨sub_ne_zero.mpr hpne, ⟨p.1, hps, p.2, hpt, rfl⟩, hpbound⟩

end Erdos3

end

end OAI
