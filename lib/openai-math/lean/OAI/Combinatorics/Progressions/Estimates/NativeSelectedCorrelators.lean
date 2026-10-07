/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.NativeResidualMultiplier

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem additiveQuadrupleCorrelation_support (g : G → G → ℂ) (H : Finset G)
    (hg : ∀ h, h ∉ H → ∀ x, g h x = 0) {a h k : G}
    (hpos : 0 < additiveQuadrupleCorrelation g a h k) :
    h ∈ H ∧ h - a ∈ H ∧ k ∈ H ∧ k - a ∈ H := by
  have hmem : h ∈ H := by
    by_contra hn
    simp [additiveQuadrupleCorrelation, hg h hn] at hpos
  have hsub : h - a ∈ H := by
    by_contra hn
    simp [additiveQuadrupleCorrelation, hg (h - a) hn] at hpos
  have hkmem : k ∈ H := by
    by_contra hn
    simp [additiveQuadrupleCorrelation, hg k hn] at hpos
  have hksub : k - a ∈ H := by
    by_contra hn
    simp [additiveQuadrupleCorrelation, hg (k - a) hn] at hpos
  exact ⟨hmem, hsub, hkmem, hksub⟩

theorem exists_many_correlated_additive_quadruples
    (f : G → ℂ) (g : G → G → ℂ) (H : Finset G)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ h x, ‖g h x‖ ≤ 1)
    (hzero : ∀ h, h ∉ H → ∀ x, g h x = 0)
    {alpha delta : ℝ} (halpha : 0 < alpha) (hdelta : 0 < delta)
    (hdense : alpha * Fintype.card G ≤ (H.card : ℝ))
    (hcorr : ∀ h ∈ H, delta ≤ ‖𝔼 x, multiplicativeDerivative f h x * star (g h x)‖) :
    ∃ Q : Finset (G × G × G), Q.Nonempty ∧
      (alpha * delta) ^ 4 / 2 * (Fintype.card G : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧
        t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H ∧
        (alpha * delta) ^ 4 / 2 ≤ additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2 := by
  classical
  have hcardG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hindicator : (𝔼 h : G, if h ∈ H then delta else 0) =
      (H.card : ℝ) * delta / Fintype.card G := by
    rw [Fintype.expect_eq_sum_div_card]
    simp
  have hmean : alpha * delta ≤
      𝔼 h, ‖𝔼 x, multiplicativeDerivative f h x * star (g h x)‖ := by
    calc
      _ ≤ (H.card : ℝ) * delta / Fintype.card G := by
        apply (le_div_iff₀ hcardG).mpr
        nlinarith [mul_le_mul_of_nonneg_right hdense hdelta.le]
      _ = _ := hindicator.symm
      _ ≤ _ := by
        apply Finset.expect_le_expect
        intro h _
        split_ifs with hh
        · exact hcorr h hh
        · exact norm_nonneg _
  have hsplit : (𝔼 t : G × G × G, additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2) =
      𝔼 a, 𝔼 h, 𝔼 k, additiveQuadrupleCorrelation g a h k := by
    simp only [← Finset.univ_product_univ, Finset.expect_product]
  have hquad : (alpha * delta) ^ 4 ≤
      𝔼 t : G × G × G, additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2 := by
    rw [hsplit]
    exact (pow_le_pow_left₀ (mul_pos halpha hdelta).le hmean 4).trans
      (derivative_correlations_force_additive_quadruples f g hf)
  obtain ⟨Q, hQcard, hQ⟩ := exists_dense_level_set
    (fun t : G × G × G => additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2)
    (by positivity : 0 ≤ (alpha * delta) ^ 4)
    (fun t => additiveQuadrupleCorrelation_le_one g hg t.1 t.2.1 t.2.2) hquad
  have hcards : (Fintype.card (G × G × G) : ℝ) = (Fintype.card G : ℝ) ^ 3 := by
    simp only [Fintype.card_prod, Nat.cast_mul]
    ring
  rw [hcards] at hQcard
  have hQnonempty : Q.Nonempty := by
    apply Finset.card_pos.mp
    have : (0 : ℝ) < (Q.card : ℝ) := lt_of_lt_of_le (by positivity) hQcard
    exact_mod_cast this
  refine ⟨Q, hQnonempty, hQcard, fun t ht => ?_⟩
  obtain ⟨h₁, h₂, h₃, h₄⟩ := additiveQuadrupleCorrelation_support g H hzero
    (lt_of_lt_of_le (by positivity) (hQ t ht))
  exact ⟨h₁, h₂, h₃, h₄, hQ t ht⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem additiveQuadrupleCorrelation_real_scale {G : Type*} [AddCommGroup G] [Fintype G]
    (g : G → G → ℂ) (c : ℝ) (hc : 0 ≤ c) (a h k : G) :
    additiveQuadrupleCorrelation (fun h x => (c : ℂ) * g h x) a h k =
      c ^ 4 * additiveQuadrupleCorrelation g a h k := by
  unfold additiveQuadrupleCorrelation
  have hmean : (𝔼 x, star ((c : ℂ) * g h x) * ((c : ℂ) * g (h - a) (x + a)) *
      ((c : ℂ) * g k x) * star ((c : ℂ) * g (k - a) (x + a))) =
      (c : ℂ) ^ 4 * (𝔼 x, star (g h x) * g (h - a) (x + a) * g k x * star (g (k - a) (x + a))) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  rw [hmean, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]

theorem derivative_quadruple_exp_threshold (p : ℝ) :
    (Real.exp (-p) * Real.exp (-(2 * p))) ^ 4 / 2 = Real.exp (-(12 * p)) / 2 := by
  rw [← Real.exp_add, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem cross_correlations_force_additive_quadruples
    (f₀ f₁ : G → ℂ) (g : G → G → ℂ)
    (hf₀ : ∀ x, ‖f₀ x‖ ≤ 1) (hf₁ : ∀ x, ‖f₁ x‖ ≤ 1) :
    (𝔼 h, ‖𝔼 x, (f₀ x * star (f₁ (x + h))) * star (g h x)‖) ^ 4 ≤
      𝔼 a, 𝔼 h, 𝔼 k, additiveQuadrupleCorrelation g a h k := by
  let C (a : G) := 𝔼 h, ‖𝔼 x, multiplicativeDerivative f₀ a x *
    (star (g h x) * g (h - a) (x + a))‖
  have hfirst : (𝔼 h, ‖𝔼 x, (f₀ x * star (f₁ (x + h))) * star (g h x)‖) ^ 2 ≤
      𝔼 a, C a := by
    have hcs := shifted_test_cauchy_schwarz f₀ (fun x => star (f₁ x))
      (fun h x => star (g h x)) (M := 1) (by simpa only [norm_star] using hf₁)
    have hreindex : (𝔼 h, 𝔼 k, ‖𝔼 x, f₀ x * star (f₀ (x + h - k)) *
        star (g h x) * g k (x + h - k)‖) = 𝔼 a, C a := by
      calc
        _ = 𝔼 h, 𝔼 a, ‖𝔼 x, multiplicativeDerivative f₀ a x *
            (star (g h x) * g (h - a) (x + a))‖ := by
          apply Finset.expect_congr rfl
          intro h _
          apply Fintype.expect_equiv (Equiv.subLeft h)
          intro k
          simp only [Equiv.subLeft_apply, sub_sub_cancel, multiplicativeDerivative,
            ← add_sub_assoc, mul_assoc]
        _ = _ := Finset.expect_comm _ _ _
    rw [← hreindex]
    simpa only [one_pow, one_mul, star_star, mul_assoc] using hcs
  have hsecond (a : G) : C a ^ 2 ≤
      𝔼 h, 𝔼 k, additiveQuadrupleCorrelation g a h k := by
    have hcs := finite_absolute_cauchy_schwarz (multiplicativeDerivative f₀ a)
      (fun h x => star (g h x) * g (h - a) (x + a))
      (multiplicativeDerivative_norm_le_one f₀ hf₀ a)
    simpa only [one_pow, one_mul, C, additiveQuadrupleCorrelation, star_mul,
      star_star, mul_assoc, mul_comm, mul_left_comm] using hcs
  calc
    _ = ((𝔼 h, ‖𝔼 x, (f₀ x * star (f₁ (x + h))) * star (g h x)‖) ^ 2) ^ 2 := by ring
    _ ≤ (𝔼 a, C a) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
    _ ≤ 𝔼 a, C a ^ 2 := expect_square_le C
    _ ≤ _ := Finset.expect_le_expect (fun a _ => hsecond a)

theorem exists_many_cross_correlated_quadruples
    (f₀ f₁ : G → ℂ) (g : G → G → ℂ) (H : Finset G)
    (hf₀ : ∀ x, ‖f₀ x‖ ≤ 1) (hf₁ : ∀ x, ‖f₁ x‖ ≤ 1) (hg : ∀ h x, ‖g h x‖ ≤ 1)
    (hzero : ∀ h, h ∉ H → ∀ x, g h x = 0)
    {alpha delta : ℝ} (halpha : 0 < alpha) (hdelta : 0 < delta)
    (hdense : alpha * Fintype.card G ≤ (H.card : ℝ))
    (hcorr : ∀ h ∈ H, delta ≤ ‖𝔼 x, (f₀ x * star (f₁ (x + h))) * star (g h x)‖) :
    ∃ Q : Finset (G × G × G), Q.Nonempty ∧
      (alpha * delta) ^ 4 / 2 * (Fintype.card G : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧
        t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H ∧
        (alpha * delta) ^ 4 / 2 ≤ additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2 := by
  classical
  have hcardG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hindicator : (𝔼 h : G, if h ∈ H then delta else 0) =
      (H.card : ℝ) * delta / Fintype.card G := by
    rw [Fintype.expect_eq_sum_div_card]
    simp
  have hmean : alpha * delta ≤
      𝔼 h, ‖𝔼 x, (f₀ x * star (f₁ (x + h))) * star (g h x)‖ := by
    calc
      _ ≤ (H.card : ℝ) * delta / Fintype.card G := by
        apply (le_div_iff₀ hcardG).mpr
        nlinarith [mul_le_mul_of_nonneg_right hdense hdelta.le]
      _ = _ := hindicator.symm
      _ ≤ _ := by
        apply Finset.expect_le_expect
        intro h _
        split_ifs with hh
        · exact hcorr h hh
        · exact norm_nonneg _
  have hsplit : (𝔼 t : G × G × G, additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2) =
      𝔼 a, 𝔼 h, 𝔼 k, additiveQuadrupleCorrelation g a h k := by
    simp only [← Finset.univ_product_univ, Finset.expect_product]
  have hquad : (alpha * delta) ^ 4 ≤
      𝔼 t : G × G × G, additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2 := by
    rw [hsplit]
    exact (pow_le_pow_left₀ (mul_pos halpha hdelta).le hmean 4).trans
      (cross_correlations_force_additive_quadruples f₀ f₁ g hf₀ hf₁)
  obtain ⟨Q, hQcard, hQ⟩ := exists_dense_level_set
    (fun t : G × G × G => additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2)
    (by positivity : 0 ≤ (alpha * delta) ^ 4)
    (fun t => additiveQuadrupleCorrelation_le_one g hg t.1 t.2.1 t.2.2) hquad
  have hcards : (Fintype.card (G × G × G) : ℝ) = (Fintype.card G : ℝ) ^ 3 := by
    simp only [Fintype.card_prod, Nat.cast_mul]
    ring
  rw [hcards] at hQcard
  have hQnonempty : Q.Nonempty := by
    apply Finset.card_pos.mp
    have : (0 : ℝ) < (Q.card : ℝ) := lt_of_lt_of_le (by positivity) hQcard
    exact_mod_cast this
  refine ⟨Q, hQnonempty, hQcard, fun t ht => ?_⟩
  obtain ⟨h₁, h₂, h₃, h₄⟩ := additiveQuadrupleCorrelation_support g H hzero
    (lt_of_lt_of_le (by positivity) (hQ t ht))
  exact ⟨h₁, h₂, h₃, h₄, hQ t ht⟩

end Erdos3

end

section

namespace Erdos3.NativeCrossWitnesses

open scoped BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f₀ f₁ : ZMod N → ℂ}
  {m : ZMod N → ZMod N → ℂ} {H : Finset (ZMod N)}
  (U : NativeCrossWitnesses s N p f₀ f₁ m H)

theorem exists_quadruples (hf₀ : ∀ x, ‖f₀ x‖ ≤ 1) (hf₁ : ∀ x, ‖f₁ x‖ ≤ 1)
    (hm : ∀ h x, ‖m h x‖ ≤ 1)
    (hdense : Real.exp (-p) * Fintype.card (ZMod N) ≤ (H.card : ℝ)) :
    ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
      Real.exp (-(12 * p)) / 2 * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H ∧
        Real.exp (-(8 * p)) / 2 ≤ additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2 := by
  let g (h x : ZMod N) := (Real.exp (-p) : ℂ) * U.extension h x
  have hg (h x : ZMod N) : ‖g h x‖ ≤ 1 := by
    dsimp only [g]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-p) * Real.exp p :=
        mul_le_mul_of_nonneg_left (U.extension_norm hm h x) (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hzero (h : ZMod N) (hh : h ∉ H) (x : ZMod N) : g h x = 0 := by
    simp only [g, U.extension_of_not_mem h hh, mul_zero]
  have hmean (h : ZMod N) :
      (𝔼 x, (f₀ x * star (f₁ (x + h))) * star (g h x)) =
        (Real.exp (-p) : ℂ) * (𝔼 x, (f₀ x * star (f₁ (x + h))) * star (U.extension h x)) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    simp only [g, star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  have hcorr (h : ZMod N) (hh : h ∈ H) :
      Real.exp (-(2 * p)) ≤ ‖𝔼 x, (f₀ x * star (f₁ (x + h))) * star (g h x)‖ := by
    rw [hmean, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hu : Real.exp (-p) ≤
        ‖𝔼 x, (f₀ x * star (f₁ (x + h))) * star (U.extension h x)‖ := by
      simpa only [U.extension_of_mem h hh] using U.product_correlation ⟨h, hh⟩
    calc
      _ = Real.exp (-p) * Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hu (Real.exp_nonneg _)
  obtain ⟨Q, hQ, hsize, hquad⟩ := exists_many_cross_correlated_quadruples f₀ f₁ g H
    hf₀ hf₁ hg hzero (Real.exp_pos (-p)) (Real.exp_pos (-(2 * p))) hdense hcorr
  have hscale (a h k : ZMod N) : additiveQuadrupleCorrelation g a h k =
      Real.exp (-(4 * p)) * additiveQuadrupleCorrelation U.extension a h k := by
    rw [show g = (fun h x => (Real.exp (-p) : ℂ) * U.extension h x) from rfl,
      additiveQuadrupleCorrelation_real_scale U.extension (Real.exp (-p)) (Real.exp_nonneg _) a h k]
    congr 1
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  refine ⟨Q, hQ, ?_, ?_⟩
  · simpa only [derivative_quadruple_exp_threshold] using hsize
  · intro t ht
    obtain ⟨h₁, h₂, h₃, h₄, hc⟩ := hquad t ht
    refine ⟨h₁, h₂, h₃, h₄, ?_⟩
    rw [derivative_quadruple_exp_threshold, hscale] at hc
    have heq : Real.exp (-(4 * p)) * (Real.exp (-(8 * p)) / 2) = Real.exp (-(12 * p)) / 2 := by
      rw [← mul_div_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [← heq] at hc
    exact le_of_mul_le_mul_left hc (Real.exp_pos _)

theorem exists_quadruples_budget (hH : H.Nonempty)
    (hf₀ : ∀ x, ‖f₀ x‖ ≤ 1) (hf₁ : ∀ x, ‖f₁ x‖ ≤ 1) (hm : ∀ h x, ‖m h x‖ ≤ 1)
    (hdense : Real.exp (-p) * Fintype.card (ZMod N) ≤ (H.card : ℝ)) :
    ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
      Real.exp (-(13 * p + 2)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H ∧
        Real.exp (-(13 * p + 2)) ≤ additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2 := by
  obtain ⟨h, hh⟩ := hH
  have hp : 0 ≤ p := (Nat.cast_nonneg (U ⟨h, hh⟩).dim).trans (U ⟨h, hh⟩).complexity.1.1
  have h12 : Real.exp (-(13 * p + 2)) ≤ Real.exp (-(12 * p)) / 2 :=
    (Real.exp_le_exp.mpr (by linarith only [hp])).trans (exp_sub_one_le_half_exp (-(12 * p)))
  have h8 : Real.exp (-(13 * p + 2)) ≤ Real.exp (-(8 * p)) / 2 :=
    (Real.exp_le_exp.mpr (by linarith only [hp])).trans (exp_sub_one_le_half_exp (-(8 * p)))
  obtain ⟨Q, hQ, hsize, hcorr⟩ := U.exists_quadruples hf₀ hf₁ hm hdense
  refine ⟨Q, hQ, (mul_le_mul_of_nonneg_right h12 (by positivity)).trans hsize, ?_⟩
  intro t ht
  obtain ⟨h₁, h₂, h₃, h₄, hc⟩ := hcorr t ht
  exact ⟨h₁, h₂, h₃, h₄, h8.trans hc⟩

end Erdos3.NativeCrossWitnesses

end

section

namespace Erdos3.NativeCrossWitnesses

variable {s N : ℕ} [NeZero N] {p : ℝ} {f₀ f₁ : ZMod N → ℂ}
  {m : ZMod N → ZMod N → ℂ} {H S : Finset (ZMod N)}
  (U : NativeCrossWitnesses s N p f₀ f₁ m H)

noncomputable def restrict (hSH : S ⊆ H) : NativeCrossWitnesses s N p f₀ f₁ m S :=
  fun h => U ⟨h.val, hSH h.property⟩

theorem restrict_extension_of_mem (hSH : S ⊆ H) (h : ZMod N) (hh : h ∈ S) (x : ZMod N) :
    (U.restrict hSH).extension h x = U.extension h x := by
  rw [extension_of_mem _ h hh, U.extension_of_mem h (hSH hh)]
  rfl

theorem restrict_quadruple (hSH : S ⊆ H) (a h k : ZMod N)
    (h₁ : h ∈ S) (h₂ : h - a ∈ S) (h₃ : k ∈ S) (h₄ : k - a ∈ S) :
    additiveQuadrupleCorrelation (U.restrict hSH).extension a h k =
      additiveQuadrupleCorrelation U.extension a h k := by
  simp only [additiveQuadrupleCorrelation, U.restrict_extension_of_mem hSH h h₁,
    U.restrict_extension_of_mem hSH (h - a) h₂,
    U.restrict_extension_of_mem hSH k h₃, U.restrict_extension_of_mem hSH (k - a) h₄]

theorem exists_short_quadruples (hH : H.Nonempty)
    (hf₀ : ∀ x, ‖f₀ x‖ ≤ 1) (hf₁ : ∀ x, ‖f₁ x‖ ≤ 1) (hm : ∀ h x, ‖m h x‖ ≤ 1)
    (hdense : Real.exp (-p) * Fintype.card (ZMod N) ≤ (H.card : ℝ)) :
    ∃ S : Finset (ZMod N), S ⊆ H ∧ S.Nonempty ∧ CyclicShortShiftSet S ∧
      Real.exp (-(p + 1)) * Fintype.card (ZMod N) ≤ (S.card : ℝ) ∧
      ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
        Real.exp (-(13 * (p + 1) + 2)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
        ∀ t ∈ Q, t.2.1 ∈ S ∧ t.2.1 - t.1 ∈ S ∧ t.2.2 ∈ S ∧ t.2.2 - t.1 ∈ S ∧
          -(t.2.1.val : ℤ) + (t.2.1 - t.1).val + t.2.2.val - (t.2.2 - t.1).val = 0 ∧
          Real.exp (-(13 * (p + 1) + 2)) ≤
            additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2 := by
  obtain ⟨S, hSH, hS, hsize, hshort⟩ := exists_cyclicShortShiftSet H hH
  have hhalf : Real.exp (-(p + 1)) ≤ Real.exp (-p) / 2 := by
    rw [show -(p + 1) = -p - 1 by ring]
    exact exp_sub_one_le_half_exp (-p)
  have hdenseS : Real.exp (-(p + 1)) * Fintype.card (ZMod N) ≤ (S.card : ℝ) := by
    calc
      _ ≤ (Real.exp (-p) / 2) * Fintype.card (ZMod N) :=
        mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg _)
      _ = (Real.exp (-p) * Fintype.card (ZMod N)) / 2 := by ring
      _ ≤ (H.card : ℝ) / 2 := div_le_div_of_nonneg_right hdense (by norm_num)
      _ ≤ _ := hsize
  let V := (U.restrict hSH).mono (show p ≤ p + 1 by linarith)
  obtain ⟨Q, hQ, hQsize, hQcorr⟩ := V.exists_quadruples_budget hS hf₀ hf₁ hm hdenseS
  refine ⟨S, hSH, hS, hshort, hdenseS, Q, hQ, hQsize, ?_⟩
  intro t ht
  obtain ⟨h₁, h₂, h₃, h₄, hc⟩ := hQcorr t ht
  refine ⟨h₁, h₂, h₃, h₄, hshort.quadruple_relation t.1 t.2.1 t.2.2 h₁ h₂ h₃ h₄, ?_⟩
  change Real.exp (-(13 * (p + 1) + 2)) ≤
    additiveQuadrupleCorrelation (U.restrict hSH).extension t.1 t.2.1 t.2.2 at hc
  rwa [U.restrict_quadruple hSH t.1 t.2.1 t.2.2 h₁ h₂ h₃ h₄] at hc

end Erdos3.NativeCrossWitnesses

end

section

namespace Erdos3.NativeCorrelationStructure

open scoped BigOperators

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

theorem exists_bounded_correlator_quadruples (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
      Real.exp (-(12 * p)) / 2 * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.2.1 ∈ W.shifts ∧ t.2.1 - t.1 ∈ W.shifts ∧
        t.2.2 ∈ W.shifts ∧ t.2.2 - t.1 ∈ W.shifts ∧
        Real.exp (-(12 * p)) / 2 ≤ additiveQuadrupleCorrelation W.boundedCorrelator t.1 t.2.1 t.2.2 := by
  obtain ⟨Q, hQ, hdense, hcorr⟩ := exists_many_correlated_additive_quadruples
    f W.boundedCorrelator W.shifts hf W.boundedCorrelator_norm W.boundedCorrelator_of_not_mem
    (Real.exp_pos (-p)) (Real.exp_pos (-(2 * p))) W.density W.boundedCorrelator_correlation
  refine ⟨Q, hQ, ?_, ?_⟩
  · simpa only [derivative_quadruple_exp_threshold] using hdense
  · intro t ht
    simpa only [derivative_quadruple_exp_threshold] using hcorr t ht

end Erdos3.NativeCorrelationStructure

end

section

namespace Erdos3.NativeCorrelationStructure

open scoped BigOperators

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

noncomputable def selectedCorrelator (h x : ZMod N) : ℂ :=
  if hh : h ∈ W.shifts then W.selectedProduct ⟨h, hh⟩ x else 0

theorem selectedCorrelator_of_mem (h : ZMod N) (hh : h ∈ W.shifts) (x : ZMod N) :
    W.selectedCorrelator h x = W.selectedProduct ⟨h, hh⟩ x := by
  simp only [selectedCorrelator, dite_eq_left hh]

theorem selectedCorrelator_of_not_mem (h : ZMod N) (hh : h ∉ W.shifts) (x : ZMod N) :
    W.selectedCorrelator h x = 0 := by
  simp only [selectedCorrelator, dite_eq_right hh]

theorem boundedCorrelator_eq_scale :
    W.boundedCorrelator = fun h x => (Real.exp (-p) : ℂ) * W.selectedCorrelator h x := by
  funext h x
  by_cases hh : h ∈ W.shifts
  · rw [W.boundedCorrelator_of_mem h hh, W.selectedCorrelator_of_mem h hh]
    rfl
  · rw [W.boundedCorrelator_of_not_mem h hh, W.selectedCorrelator_of_not_mem h hh, mul_zero]

theorem boundedCorrelator_quadruple_scale (a h k : ZMod N) :
    additiveQuadrupleCorrelation W.boundedCorrelator a h k =
      Real.exp (-(4 * p)) * additiveQuadrupleCorrelation W.selectedCorrelator a h k := by
  rw [W.boundedCorrelator_eq_scale,
    additiveQuadrupleCorrelation_real_scale W.selectedCorrelator (Real.exp (-p)) (Real.exp_nonneg _) a h k]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem exists_selected_correlator_quadruples (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
      Real.exp (-(12 * p)) / 2 * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.2.1 ∈ W.shifts ∧ t.2.1 - t.1 ∈ W.shifts ∧
        t.2.2 ∈ W.shifts ∧ t.2.2 - t.1 ∈ W.shifts ∧
        Real.exp (-(8 * p)) / 2 ≤ additiveQuadrupleCorrelation W.selectedCorrelator t.1 t.2.1 t.2.2 := by
  obtain ⟨Q, hQ, hdense, hcorr⟩ := W.exists_bounded_correlator_quadruples hf
  refine ⟨Q, hQ, hdense, ?_⟩
  intro t ht
  obtain ⟨h₁, h₂, h₃, h₄, hc⟩ := hcorr t ht
  refine ⟨h₁, h₂, h₃, h₄, ?_⟩
  rw [W.boundedCorrelator_quadruple_scale] at hc
  have heq : Real.exp (-(4 * p)) * (Real.exp (-(8 * p)) / 2) = Real.exp (-(12 * p)) / 2 := by
    rw [← mul_div_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [← heq] at hc
  exact le_of_mul_le_mul_left hc (Real.exp_pos (-(4 * p)))

end Erdos3.NativeCorrelationStructure

end

end OAI
