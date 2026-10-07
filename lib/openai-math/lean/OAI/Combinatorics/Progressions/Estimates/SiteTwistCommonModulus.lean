/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Geometry.PhysicalNormalizedSpatialFactor
import OAI.Combinatorics.Progressions.Sampling.CeilGridScaleRatio

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {A S : Type*} [Fintype A] [Fintype S]
variable {I : A → Type*} [∀ a, Fintype (I a)]

theorem finite_site_product_expansion (c : ∀ a, I a → ℂ)
    (f : ∀ a, I a → S → ℂ) :
    (∏ a, ∑ k, c a k * ∏ s, f a k s) =
      ∑ k : ∀ a, I a, (∏ a, c a (k a)) * ∏ s, ∏ a, f a (k a) s := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.prod_mul_distrib, Finset.prod_comm]

theorem finite_site_product_coefficient_norm (c : ∀ a, I a → ℂ) :
    (∑ k : ∀ a, I a, ‖∏ a, c a (k a)‖) = ∏ a, ∑ k, ‖c a k‖ := by
  simp only [norm_prod, Fintype.prod_sum]

theorem finite_site_product_coefficient_norm_le (c : ∀ a, I a → ℂ)
    (C : A → ℝ) (hc : ∀ a, (∑ k, ‖c a k‖) ≤ C a) :
    (∑ k : ∀ a, I a, ‖∏ a, c a (k a)‖) ≤ ∏ a, C a := by
  rw [finite_site_product_coefficient_norm]
  exact Finset.prod_le_prod₀ (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (fun a _ => hc a)

theorem finite_site_axis_product_lipschitz (f : A → ℝ → ℂ) (L : ℝ≥0)
    (hf : ∀ a, LipschitzWith L (f a)) (hn : ∀ a x, ‖f a x‖ ≤ 1) :
    (∀ x : A → ℝ, ‖∏ a, f a (x a)‖ ≤ 1) ∧
      LipschitzWith (Fintype.card A * L) (fun x : A → ℝ => ∏ a, f a (x a)) := by
  have hl (a : A) : LipschitzWith L (fun x : A → ℝ => f a (x a)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact ((hf a).dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (dist_le_pi_dist x y a) L.coe_nonneg)
  simpa only [NNReal.coe_one, one_pow, mul_one] using
    bounded_lipschitz_fintype_prod (fun a (x : A → ℝ) => f a (x a))
      (B := 1) le_rfl hl (fun a x => hn a (x a))

theorem finite_site_product_approximation (c : ∀ a, I a → ℂ)
    (f : ∀ a, I a → S → ℂ) (g : A → ℂ)
    (N : ℕ) (hcard : Fintype.card A ≤ N) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ)
    (hg : ∀ a, ‖g a‖ ≤ C)
    (he : ∀ a, ‖g a - ∑ k, c a k * ∏ s, f a k s‖ ≤ uniformProductAccuracy N C δ) :
    ‖(∏ a, g a) -
      ∑ k : ∀ a, I a, (∏ a, c a (k a)) * ∏ s, ∏ a, f a (k a) s‖ ≤ δ := by
  rw [← finite_site_product_expansion]
  have h := norm_prod_sub_prod_le_uniform_accuracy N hcard hC hδ
    (fun a => ∑ k, c a k * ∏ s, f a k s) g hg
    (fun a => by simpa only [norm_sub_rev] using he a)
  simpa only [norm_sub_rev] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

universe u v

structure ScalarSiteExpansion (S : Type u) where
  Term : Type v
  [termFinite : Fintype Term]
  period : Term → ℕ
  coefficient : Term → ℂ
  factor : (i : Term) → S → ZMod (period i) → ℝ → ℂ

attribute [local instance] ScalarSiteExpansion.termFinite

namespace ScalarSiteExpansion

variable {S : Type u} [Fintype S]

structure Bounds (e : ScalarSiteExpansion.{u,v} S) (T D C : ℝ) (L : ℝ≥0) (H : ℝ) : Prop where
  card_le : (Fintype.card e.Term : ℝ) ≤ T
  period_pos : ∀ i, 0 < e.period i
  period_le : ∀ i, (e.period i : ℝ) ≤ D
  coefficient_le : (∑ i, ‖e.coefficient i‖) ≤ C
  factor_bound : ∀ i s r x, ‖e.factor i s r x‖ ≤ 1
  lipschitz : ∀ i s r, LipschitzWith L (e.factor i s r)
  support : ∀ i s r x, H ≤ |x| → e.factor i s r x = 0

noncomputable def eval (e : ScalarSiteExpansion.{u,v} S) (y : S → ℤ) (x : S → ℝ) : ℂ :=
  ∑ i, e.coefficient i * ∏ s, e.factor i s (y s : ZMod (e.period i)) (x s)

noncomputable def integerEval (e : ScalarSiteExpansion.{u,v} S) (N : ℕ) (y : S → ℤ) : ℂ :=
  e.eval y (fun s => (y s : ℝ) / N)

theorem eval_norm_le (e : ScalarSiteExpansion.{u,v} S) {T D C H : ℝ} {L : ℝ≥0}
    (h : e.Bounds T D C L H) (y : S → ℤ) (x : S → ℝ) : ‖e.eval y x‖ ≤ C := by
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun i _ => ?_)).trans h.coefficient_le
  rw [norm_mul]
  apply mul_le_of_le_one_right (norm_nonneg _)
  rw [norm_prod]
  exact (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun s _ => h.factor_bound i s _ _)).trans_eq
    Finset.prod_const_one

end ScalarSiteExpansion
end Erdos3

end

section

namespace Erdos3.ScalarSiteExpansion

open scoped NNReal

universe u v

variable {S : Type u} {e : ScalarSiteExpansion.{u,v} S}

theorem Bounds.mono {T D C H T' D' C' H' : ℝ} {L L' : ℝ≥0}
    (h : e.Bounds T D C L H) (hT : T ≤ T') (hD : D ≤ D') (hC : C ≤ C')
    (hL : L ≤ L') (hH : H ≤ H') : e.Bounds T' D' C' L' H' :=
  ⟨h.card_le.trans hT, h.period_pos, fun i => (h.period_le i).trans hD,
    h.coefficient_le.trans hC, h.factor_bound, fun i s r => (h.lipschitz i s r).weaken hL,
    fun i s r x hx => h.support i s r x (hH.trans hx)⟩

end Erdos3.ScalarSiteExpansion

end

section

namespace Erdos3.ScalarSiteExpansion
open scoped BigOperators NNReal Classical
universe u v
variable {S : Type u} [Fintype S]
attribute [local instance] ScalarSiteExpansion.termFinite

noncomputable def rescale (e : ScalarSiteExpansion.{u,v} S) (c : ℂ) (r : ℝ) : ScalarSiteExpansion.{u,v} S where
  Term := e.Term
  period := e.period
  coefficient i := c * e.coefficient i
  factor i s k x := e.factor i s k (r * x)

theorem rescale_eval (e : ScalarSiteExpansion.{u,v} S) (c : ℂ) (r : ℝ) (y : S → ℤ) (x : S → ℝ) :
    (e.rescale c r).eval y x = c * e.eval y (fun s => r * x s) := by
  simp only [eval, rescale, Finset.mul_sum, mul_assoc]
  rfl

omit [Fintype S] in
theorem rescale_bounds [Fintype S] (e : ScalarSiteExpansion.{u,v} S) {T D C H : ℝ} {L : ℝ≥0}
    (h : e.Bounds T D C L H) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (e.rescale c r).Bounds T D (‖c‖ * C) (L * ‖r‖₊) (H / r) := by
  refine ⟨h.card_le, h.period_pos, h.period_le, ?_, ?_, ?_, ?_⟩
  · change (∑ i, ‖c * e.coefficient i‖) ≤ ‖c‖ * C
    simp only [norm_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left h.coefficient_le (norm_nonneg c)
  · intro i s k x
    exact h.factor_bound i s k (r * x)
  · intro i s k
    have hmul : LipschitzWith ‖r‖₊ (fun x : ℝ => r * x) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [Real.dist_eq, ← mul_sub, abs_mul, coe_nnnorm, Real.norm_eq_abs, le_refl]
    exact (h.lipschitz i s k).comp hmul
  · intro i s k x hx
    apply h.support
    rw [abs_mul, abs_of_pos hr]
    exact (div_le_iff₀ hr).mp hx |>.trans_eq (mul_comm _ _)

theorem rescale_integerEval (e : ScalarSiteExpansion.{u,v} S) (c : ℂ) (M N : ℕ)
    (hN : 0 < N) (y : S → ℤ) :
    (e.rescale c ((N : ℝ) / M)).integerEval N y = c * e.integerEval M y := by
  rw [integerEval, rescale_eval, integerEval]
  congr 2
  funext s
  have hN0 : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  simp only [div_eq_mul_inv]
  calc
    _ = ((N : ℝ) * (N : ℝ)⁻¹) * ((y s : ℝ) * (M : ℝ)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hN0, one_mul]

theorem rescale_integer_error (e : ScalarSiteExpansion.{u,v} S) (M N d : ℕ)
    (hM : 0 < M) (hN : 0 < N) (y : S → ℤ) (p ε : ℝ)
    (he : ‖(((M : ℝ) ^ d * p : ℝ) : ℂ) - e.integerEval M y‖ ≤ ε) :
    ‖(((N : ℝ) ^ d * p : ℝ) : ℂ) -
      (e.rescale (((N : ℝ) / M) ^ d : ℂ) ((N : ℝ) / M)).integerEval N y‖ ≤
        ((N : ℝ) / M) ^ d * ε := by
  rw [rescale_integerEval e _ M N hN]
  have hM0 : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
  have hr : ((N : ℝ) / M) * M = N := div_mul_cancel₀ _ hM0
  have hv : ((N : ℝ) / M) ^ d * ((M : ℝ) ^ d * p) = (N : ℝ) ^ d * p := by
    rw [← mul_assoc, ← mul_pow, hr]
  have hvC : (((N : ℝ) ^ d * p : ℝ) : ℂ) =
      (((N : ℝ) / M) ^ d : ℂ) * (((M : ℝ) ^ d * p : ℝ) : ℂ) := by
    exact_mod_cast hv.symm
  rw [hvC, ← mul_sub, norm_mul]
  have hn : ‖(((N : ℝ) / M) ^ d : ℂ)‖ = ((N : ℝ) / M) ^ d := by
    rw [norm_pow]
    norm_cast
  rw [hn]
  exact mul_le_mul_of_nonneg_left he (by positivity)

end Erdos3.ScalarSiteExpansion

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

attribute [local instance] ScalarSiteExpansion.termFinite

universe u v w

variable {A : Type u} {S : Type v} [Fintype A] [Fintype S]
variable (e : A → ScalarSiteExpansion.{v,w} S)

noncomputable def siteFamilyCoefficient (k : ∀ a, (e a).Term) : ℂ :=
  ∏ a, (e a).coefficient (k a)

noncomputable def siteFamilyFactor (k : ∀ a, (e a).Term) (s : S)
    (r : ∀ a, ZMod ((e a).period (k a))) (x : A → ℝ) : ℂ :=
  ∏ a, (e a).factor (k a) s (r a) (x a)

noncomputable def siteFamilyEval (y : S → A → ℤ) (x : S → A → ℝ) : ℂ :=
  ∑ k, siteFamilyCoefficient e k * ∏ s,
    siteFamilyFactor e k s (fun a => (y s a : ZMod ((e a).period (k a)))) (x s)

theorem siteFamilyEval_eq (y : S → A → ℤ) (x : S → A → ℝ) :
    siteFamilyEval e y x = ∏ a, (e a).eval (fun s => y s a) (fun s => x s a) := by
  symm
  exact finite_site_product_expansion (fun a => (e a).coefficient)
    (fun a k s => (e a).factor k s (y s a : ZMod ((e a).period k)) (x s a))

variable {T D C H : A → ℝ} {L : ℝ≥0}
variable (h : ∀ a, (e a).Bounds (T a) (D a) (C a) L (H a))

include h in
omit [Fintype S] in
theorem siteFamily_card_le : (Fintype.card (∀ a, (e a).Term) : ℝ) ≤ ∏ a, T a := by
  rw [Fintype.card_pi, Nat.cast_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun a _ => (h a).card_le)

include h in
omit [Fintype S] in
theorem siteFamily_coefficient_le : (∑ k, ‖siteFamilyCoefficient e k‖) ≤ ∏ a, C a :=
  finite_site_product_coefficient_norm_le (fun a => (e a).coefficient) C
    (fun a => (h a).coefficient_le)

include h in
omit [Fintype S] in
theorem siteFamilyFactor_bounds (k : ∀ a, (e a).Term) (s : S)
    (r : ∀ a, ZMod ((e a).period (k a))) :
    (∀ x, ‖siteFamilyFactor e k s r x‖ ≤ 1) ∧
      LipschitzWith (Fintype.card A * L) (siteFamilyFactor e k s r) := by
  exact finite_site_axis_product_lipschitz (fun a => (e a).factor (k a) s (r a)) L
    (fun a => (h a).lipschitz (k a) s (r a)) (fun a => (h a).factor_bound (k a) s (r a))

include h in
omit [Fintype S] in
theorem siteFamilyFactor_support (k : ∀ a, (e a).Term) (s : S)
    (r : ∀ a, ZMod ((e a).period (k a))) (x : A → ℝ)
    (hx : ∃ a, H a ≤ |x a|) : siteFamilyFactor e k s r x = 0 := by
  obtain ⟨a, ha⟩ := hx
  exact Finset.prod_eq_zero (Finset.mem_univ a) ((h a).support (k a) s (r a) (x a) ha)

theorem siteFamily_approximation (y : S → A → ℤ) (x : S → A → ℝ) (g : A → ℂ)
    (N : ℕ) (hcard : Fintype.card A ≤ N) {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ)
    (hg : ∀ a, ‖g a‖ ≤ B)
    (he : ∀ a, ‖g a - (e a).eval (fun s => y s a) (fun s => x s a)‖ ≤
      uniformProductAccuracy N B δ) :
    ‖(∏ a, g a) - siteFamilyEval e y x‖ ≤ δ := by
  exact finite_site_product_approximation (fun a => (e a).coefficient)
    (fun a k s => (e a).factor k s (y s a : ZMod ((e a).period k)) (x s a))
    g N hcard hB hδ hg he

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {A S : Type*} [Fintype A] (e : A → ScalarSiteExpansion S)

noncomputable def commonSitePeriod (k : ∀ a, (e a).Term) : ℕ := ∏ a, (e a).period (k a)

theorem commonSitePeriod_dvd (k : ∀ a, (e a).Term) (a : A) :
    (e a).period (k a) ∣ commonSitePeriod e k :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ a)

theorem commonSitePeriod_pos {T V C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a)) (k : ∀ a, (e a).Term) :
    0 < commonSitePeriod e k :=
  Finset.prod_pos (fun a _ => (he a).period_pos (k a))

theorem commonSitePeriod_le_pow {T V C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a))
    {D : ℝ} (hD : ∀ a, V a ≤ D) (k : ∀ a, (e a).Term) :
    (commonSitePeriod e k : ℝ) ≤ D ^ Fintype.card A := by
  rw [commonSitePeriod, Nat.cast_prod]
  calc
    _ ≤ ∏ _a : A, D := Finset.prod_le_prod₀ (fun a _ => Nat.cast_nonneg _)
      (fun a _ => ((he a).period_le (k a)).trans (hD a))
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

attribute [local instance] ScalarSiteExpansion.termFinite

variable {A D S : Type*} [Fintype A] [Fintype D]

def scaledSiteCoordinates (selected : A → D) (scale : A → ℝ) (x : D → ℝ) : A → ℝ :=
  fun a => scale a * x (selected a)

theorem scaledSiteCoordinates_lipschitz (selected : A → D) (scale : A → ℝ)
    (Q : ℝ≥0) (hQ : ∀ a, |scale a| ≤ Q) :
    LipschitzWith Q (scaledSiteCoordinates selected scale) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (by positivity)).mpr
  intro a
  change |scale a * x (selected a) - scale a * y (selected a)| ≤ _
  rw [← mul_sub, abs_mul]
  exact (mul_le_mul_of_nonneg_left (dist_le_pi_dist x y (selected a)) (abs_nonneg _)).trans
    (mul_le_mul_of_nonneg_right (hQ a) dist_nonneg)

variable (e : A → ScalarSiteExpansion S) (selected : A → D) (scale : A → ℝ)

noncomputable def scaledSiteFamilyFactor (k : ∀ a, (e a).Term) (s : S)
    (r : ∀ a, ZMod ((e a).period (k a))) (x : D → ℝ) : ℂ :=
  siteFamilyFactor e k s r (scaledSiteCoordinates selected scale x)

theorem scaledSiteFamilyFactor_bounds {T V C H : A → ℝ} {L : ℝ≥0}
    (h : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a))
    (Q : ℝ≥0) (hQ : ∀ a, |scale a| ≤ Q)
    (k : ∀ a, (e a).Term) (s : S) (r : ∀ a, ZMod ((e a).period (k a))) :
    (∀ x, ‖scaledSiteFamilyFactor e selected scale k s r x‖ ≤ 1) ∧
      LipschitzWith ((Fintype.card A * L) * Q) (scaledSiteFamilyFactor e selected scale k s r) := by
  have hf := siteFamilyFactor_bounds e h k s r
  exact ⟨fun x => hf.1 _, hf.2.comp (scaledSiteCoordinates_lipschitz selected scale Q hQ)⟩

omit [Fintype D] in
theorem scaledSiteFamilyFactor_support {T V C H : A → ℝ} {L : ℝ≥0}
    (h : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a))
    (hscale : ∀ a, 0 < scale a) (k : ∀ a, (e a).Term) (s : S)
    (r : ∀ a, ZMod ((e a).period (k a))) (x : D → ℝ)
    (hx : ∃ a, H a / scale a ≤ |x (selected a)|) :
    scaledSiteFamilyFactor e selected scale k s r x = 0 := by
  obtain ⟨a, ha⟩ := hx
  apply siteFamilyFactor_support e h k s r _
  refine ⟨a, ?_⟩
  change H a ≤ |scale a * x (selected a)|
  rw [abs_mul, abs_of_pos (hscale a)]
  exact (div_le_iff₀' (hscale a)).mp ha

omit [Fintype D] in
theorem scaledSiteFamilyFactor_eval [Fintype S]
    (y : S → A → ℤ) (x : S → D → ℝ) :
    (∑ k, siteFamilyCoefficient e k * ∏ s, scaledSiteFamilyFactor e selected scale k s
      (fun a => (y s a : ZMod ((e a).period (k a)))) (x s)) =
      siteFamilyEval e y (fun s => scaledSiteCoordinates selected scale (x s)) := rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

attribute [local instance] ScalarSiteExpansion.termFinite

theorem ScalarSiteExpansion.eval_eq_zero_of_large {S : Type*} [Fintype S]
    (e : ScalarSiteExpansion S) {H : ℝ}
    (he : ∀ i s r x, H ≤ |x| → e.factor i s r x = 0)
    (y : S → ℤ) (x : S → ℝ) (s : S) (hs : H ≤ |x s|) : e.eval y x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [Finset.prod_eq_zero (Finset.mem_univ s) (he i s _ _ hs), mul_zero]

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def reconstructedSiteEval (rows : Finset (Finset α))
    (e : ScalarSiteExpansion (Finset α)) (N : ℕ) (z : rows → ℤ) : ℂ :=
  e.integerEval N (integerBooleanSitesFromRows rows z)

theorem reconstructedSiteEval_zero_off_window (rows : Finset (Finset α))
    (e : ScalarSiteExpansion (Finset α)) {N d : ℕ} (hN : 0 < N)
    (hrows : ∀ t ∈ rows, t.card ≤ d) {H K : ℝ} (hH : 0 ≤ H)
    (hK : (2 : ℝ) ^ d * H ≤ K)
    (he : ∀ i s r x, H ≤ |x| → e.factor i s r x = 0)
    (z : rows → ℤ) (hz : z ∉ naturalScaleIntegerWindow rows K N) :
    reconstructedSiteEval rows e N z = 0 := by
  by_contra hg
  apply hz
  apply mem_naturalScaleIntegerWindow_of_bound
  intro t
  let y := integerBooleanSitesFromRows rows z
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hy (s : Finset α) : |(y s : ℝ)| ≤ H * N := by
    have hs : |(y s : ℝ) / N| < H := lt_of_not_ge (fun h => hg
      (e.eval_eq_zero_of_large he y (fun s => (y s : ℝ) / N) s h))
    rw [abs_div, abs_of_pos hNr] at hs
    exact (div_le_iff₀ hNr).mp hs.le
  have hc := integer_boolean_coefficient_degree_bound y t.val
    (hrows t.val t.property) hH hNr.le hy
  rw [integerBooleanSitesFromRows_coefficient_mem] at hc
  exact hc.trans ((mul_assoc (2 ^ d) H (N : ℝ)).symm.le.trans
    (mul_le_mul_of_nonneg_right hK hNr.le))

end Erdos3

end

section

namespace Erdos3.ScalarSiteExpansion
open scoped BigOperators NNReal Classical
universe u v
variable {S : Type u} [Fintype S]

noncomputable def atCeilScale (e : ScalarSiteExpansion.{u,v} S) (K d : ℕ) (γ : ℝ) :
    ScalarSiteExpansion.{u,v} S :=
  e.rescale (((⌈γ * (K : ℝ)⌉₊ : ℝ) / K) ^ d : ℂ) ((⌈γ * (K : ℝ)⌉₊ : ℝ) / K)

theorem atCeilScale_bounds (e : ScalarSiteExpansion.{u,v} S) (K d : ℕ) {γ T D C H : ℝ} {L : ℝ≥0}
    (hK : 0 < K) (hγ : 0 < γ) (hC : 0 ≤ C) (hH : 0 ≤ H) (he : e.Bounds T D C L H) :
    (e.atCeilScale K d γ).Bounds T D ((γ + 1) ^ d * C)
      (L * Real.toNNReal (γ + 1)) (H * γ⁻¹) := by
  obtain ⟨hN, hlo, hhi, hinv⟩ := ceilGridScale_ratio_bounds K hK hγ
  let r : ℝ := (⌈γ * (K : ℝ)⌉₊ : ℝ) / K
  have hr : 0 < r := div_pos (Nat.cast_pos.mpr hN) (Nat.cast_pos.mpr hK)
  have hnorm : ‖(r ^ d : ℂ)‖ = r ^ d := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hLip : ‖r‖₊ ≤ Real.toNNReal (γ + 1) := by
    apply NNReal.coe_le_coe.mp
    simpa only [coe_nnnorm, Real.norm_eq_abs, abs_of_pos hr,
      Real.coe_toNNReal (γ + 1) (by positivity : 0 ≤ γ + 1)] using hhi
  have hsupport : H / r ≤ H * γ⁻¹ := by
    have hi : r⁻¹ ≤ γ⁻¹ := by simpa only [r, inv_div] using hinv
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hi hH
  have heq : e.atCeilScale K d γ = e.rescale (r ^ d : ℂ) r := by
    simp only [atCeilScale, r, Complex.ofReal_div, Complex.ofReal_natCast]
  rw [heq]
  apply (rescale_bounds e he (r ^ d : ℂ) hr).mono le_rfl le_rfl _ _ hsupport
  · rw [hnorm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hhi d) hC
  · exact mul_le_mul_of_nonneg_left hLip (show 0 ≤ L from zero_le)

theorem atCeilScale_integer_error (e : ScalarSiteExpansion.{u,v} S) (K d : ℕ) {γ : ℝ}
    (hK : 0 < K) (hγ : 0 < γ) (y : S → ℤ) (p : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (he : ‖(((K : ℝ) ^ d * p : ℝ) : ℂ) - e.integerEval K y‖ ≤ ε) :
    ‖(((⌈γ * (K : ℝ)⌉₊ : ℝ) ^ d * p : ℝ) : ℂ) -
      (e.atCeilScale K d γ).integerEval ⌈γ * (K : ℝ)⌉₊ y‖ ≤ (γ + 1) ^ d * ε := by
  obtain ⟨hN, _, hhi, _⟩ := ceilGridScale_ratio_bounds K hK hγ
  exact (rescale_integer_error e K ⌈γ * (K : ℝ)⌉₊ d hK hN y p ε he).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hhi d) hε)

end Erdos3.ScalarSiteExpansion

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {X A V : Type*} [Fintype X] [Fintype A]
variable (spatialPeriod : ℕ) (q : X → ℕ) (e : A → ScalarSiteExpansion V)
variable (k : ∀ a, (e a).Term) (idealPeriod : ℕ)

noncomputable def siteTwistCommonModulus : ℕ :=
  residueRefinedPeriod spatialPeriod q * commonSitePeriod e k * idealPeriod

theorem siteTwistCommonModulus_pos (hs : 0 < spatialPeriod) (hq : ∀ x, 0 < q x)
    (hg : ∀ a, 0 < (e a).period (k a)) (hi : 0 < idealPeriod) :
    0 < siteTwistCommonModulus spatialPeriod q e k idealPeriod :=
  Nat.mul_pos (Nat.mul_pos (residueRefinedPeriod_pos hs q hq)
    (Finset.prod_pos (fun a _ => hg a))) hi

theorem siteTwistCommonModulus_spatial_dvd (x : X) :
    q x * spatialPeriod ∣ siteTwistCommonModulus spatialPeriod q e k idealPeriod :=
  ((stride_mul_dvd_residueRefinedPeriod spatialPeriod q x).trans
    (dvd_mul_right (residueRefinedPeriod spatialPeriod q) (commonSitePeriod e k))).trans
      (dvd_mul_right _ idealPeriod)

theorem siteTwistCommonModulus_grid_dvd (a : A) :
    (e a).period (k a) ∣ siteTwistCommonModulus spatialPeriod q e k idealPeriod :=
  ((commonSitePeriod_dvd e k a).trans
    (dvd_mul_left (commonSitePeriod e k) (residueRefinedPeriod spatialPeriod q))).trans
      (dvd_mul_right _ idealPeriod)

theorem siteTwistCommonModulus_ideal_dvd :
    idealPeriod ∣ siteTwistCommonModulus spatialPeriod q e k idealPeriod :=
  dvd_mul_left idealPeriod _

theorem siteTwistCommonModulus_exp_bound {ES EQ EG EI : ℝ}
    (hs : (spatialPeriod : ℝ) ≤ Real.exp ES)
    (hq : ∀ x, (q x : ℝ) ≤ Real.exp EQ)
    (hg : ∀ a, ((e a).period (k a) : ℝ) ≤ Real.exp EG)
    (hi : (idealPeriod : ℝ) ≤ Real.exp EI) :
    (siteTwistCommonModulus spatialPeriod q e k idealPeriod : ℝ) ≤
      Real.exp (ES + Fintype.card X * EQ + Fintype.card A * EG + EI) := by
  have hgrid : (commonSitePeriod e k : ℝ) ≤ Real.exp (Fintype.card A * EG) := by
    calc
      _ = ∏ a, ((e a).period (k a) : ℝ) := by rw [commonSitePeriod, Nat.cast_prod]
      _ ≤ ∏ _a : A, Real.exp EG := Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun a _ => hg a)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Real.exp_nat_mul]
  have hspatial := residueRefinedPeriod_exp_bound spatialPeriod q hs hq
  have hprod := mul_le_mul (mul_le_mul hspatial hgrid (Nat.cast_nonneg _) (Real.exp_pos _).le)
    hi (Nat.cast_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  simpa only [siteTwistCommonModulus, Nat.cast_mul, Real.exp_add] using hprod

namespace BooleanCubeKernel

variable {K α : Type*} [Fintype K] [Fintype α]
variable (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
variable (residue : Option K × X → ℤ) (q : X → ℕ)
variable (b : ℝ) (r : ℝ≥0) {spatialPeriod M : ℕ}
variable (hM : ∀ x, q x * spatialPeriod ∣ M)
variable (t : X → SpatialSiteLabel α spatialPeriod b r) (s : Finset α)

noncomputable def physicalResidueSpatialMaskMod (u : X → ZMod M) : ℂ :=
  starVertexSiteFactor (fun i u => ∏ x,
    if ZMod.castHom (hM x) (ZMod (q x * spatialPeriod)) (u x) =
      ((physicalCubeVertexValue (physicalCubeRootDifferences root D base residue)
        (spatialStarVertex i) x + (q x : ℤ) * (((t x).1 i).val : ℤ) : ℤ) : ZMod (q x * spatialPeriod))
    then (1 : ℂ) else 0) s u

theorem physicalResidueSpatialMaskMod_eval (u : X → ℤ) :
    physicalResidueSpatialMaskMod root D base residue q b r hM t s (fun x => (u x : ZMod M)) =
      physicalResidueSpatialMask root D base residue q b r t s u := by
  simp only [physicalResidueSpatialMaskMod, physicalResidueSpatialMask, starVertexSiteFactor,
    residueSiteIndicator, map_intCast, apply_ite, Complex.ofReal_one, Complex.ofReal_zero]

theorem physicalResidueSpatialMaskMod_norm (u : X → ZMod M) :
    ‖physicalResidueSpatialMaskMod root D base residue q b r hM t s u‖ ≤ 1 := by
  apply starVertexSiteFactor_bound
  intro i v
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro x _
  split_ifs <;> simp

end BooleanCubeKernel
end Erdos3

end

end OAI
