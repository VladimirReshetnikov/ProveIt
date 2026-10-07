/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.FinsetInj
import OAI.Compat.Core
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Set.Card
import OAI.Combinatorics.Progressions.Geometry.ProductSectionSupport
import OAI.Combinatorics.Progressions.Probability.FiniteExcessMassCap
import OAI.Combinatorics.Progressions.Probability.IntervalDivisorProbability

namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

theorem mean_comm {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y) (F : X → Y → ℝ) :
    p.mean (fun x => q.mean (F x)) = q.mean (fun y => p.mean (fun x => F x y)) := by
  unfold mean
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem mean_sum {X J : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (s : Finset J) (F : J → X → ℝ) :
    p.mean (fun x => ∑ j ∈ s, F j x) = ∑ j ∈ s, p.mean (F j) := by
  unfold mean
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem mean_sub {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X) (f g : X → ℝ) :
    p.mean (fun x => f x - g x) = p.mean f - p.mean g := by
  simp only [mean, mul_sub, Finset.sum_sub_distrib]

theorem mean_mul_const {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (f : X → ℝ) (c : ℝ) : p.mean (fun x => f x * c) = p.mean f * c := by
  simp only [mean, ← mul_assoc, Finset.sum_mul]

end FiniteProbabilityWeights

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)]

theorem productMean_coordinateSwap (μ : ∀ i, FiniteProbabilityWeights (X i))
    (S : Finset I) (F : (∀ i, X i) → (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => (FiniteProbabilityWeights.pi μ).mean
      (fun y => F (productCoordinateMix S x y) (productCoordinateMix S y x))) =
    (FiniteProbabilityWeights.pi μ).mean (fun x => (FiniteProbabilityWeights.pi μ).mean (F x)) := by
  let p := FiniteProbabilityWeights.pi μ
  have h : (∑ z : (∀ i, X i) × (∀ i, X i), p.weight z.1 * p.weight z.2 *
        F (productCoordinateMix S z.1 z.2) (productCoordinateMix S z.2 z.1)) =
      ∑ z : (∀ i, X i) × (∀ i, X i), p.weight z.1 * p.weight z.2 * F z.1 z.2 := by
    apply Fintype.sum_equiv (productCoordinateSwap (X := X) S)
    intro z
    change _ = p.weight (productCoordinateMix S z.1 z.2) *
      p.weight (productCoordinateMix S z.2 z.1) * _
    rw [productCoordinateMix_weight]
    rfl
  simpa only [FiniteProbabilityWeights.mean, Fintype.sum_prod_type,
    Finset.mul_sum, mul_assoc] using h

theorem productMean_coordinateMix (μ : ∀ i, FiniteProbabilityWeights (X i))
    (S : Finset I) (f : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => (FiniteProbabilityWeights.pi μ).mean
      (fun y => f (productCoordinateMix S x y))) = (FiniteProbabilityWeights.pi μ).mean f := by
  have h := productMean_coordinateSwap μ S (fun x _ => f x)
  simpa only [FiniteProbabilityWeights.mean_const] using h

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem exists_code_fiber_mass {Ω I : Type*} [Fintype Ω] [Fintype I] [Nonempty I]
    (p : FiniteProbabilityWeights Ω) (Q : Finset Ω) (code : Ω → I) :
    ∃ i, p.mass Q / Fintype.card I ≤ p.mass (Q.filter (fun x => code x = i)) := by
  have hsum : (∑ i, p.mass (Q.filter (fun x => code x = i))) = p.mass Q := by
    simp only [mass, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  have hmean : (𝔼 i, p.mass (Q.filter (fun x => code x = i))) = p.mass Q / Fintype.card I := by
    rw [Fintype.expect_eq_sum_div_card, hsum]
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean.ge
  exact ⟨i, hi⟩

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem retain_simultaneous_mean_error {Ω J : Type*} [Fintype Ω] [Fintype J]
    (p : FiniteProbabilityWeights Ω) (productive : Finset Ω) (err : J → Ω → ℝ)
    (herr : ∀ j a, 0 ≤ err j a) {tau : ℝ} (htau : 0 < tau) :
    ∃ retained : Finset Ω, retained ⊆ productive ∧
      p.mass productive - (∑ j, p.mean (err j)) / tau ≤ p.mass retained ∧
      ∀ a ∈ retained, ∀ j, err j a ≤ tau := by
  let retained := productive.filter (fun a => ∀ j, err j a ≤ tau)
  have hpoint (a : Ω) :
      tau * ((if a ∈ productive then (1 : ℝ) else 0) -
        (if a ∈ retained then 1 else 0)) ≤ ∑ j, err j a := by
    by_cases ha : a ∈ productive
    · by_cases hg : ∀ j, err j a ≤ tau
      · have hret : a ∈ retained := Finset.mem_filter.mpr ⟨ha, hg⟩
        simp only [ha, hret, ite_true, sub_self, mul_zero]
        exact Finset.sum_nonneg (fun j _ => herr j a)
      · have hret : a ∉ retained := by simpa only [retained, Finset.mem_filter, ha, true_and] using hg
        simp only [ha, hret, ite_true, ite_false, sub_zero, mul_one]
        push Not at hg
        obtain ⟨j, hj⟩ := hg
        exact hj.le.trans (Finset.single_le_sum (fun i _ => herr i a) (Finset.mem_univ j))
    · have hret : a ∉ retained := fun h => ha (Finset.mem_filter.mp h).1
      simp only [ha, hret, ite_false, sub_self, mul_zero]
      exact Finset.sum_nonneg (fun j _ => herr j a)
  have h := p.mean_mono hpoint
  rw [p.mean_const_mul, p.mean_sub, p.mean_indicator, p.mean_indicator, p.mean_sum] at h
  have hdiv : p.mass productive - p.mass retained ≤ (∑ j, p.mean (err j)) / tau :=
    (le_div_iff₀ htau).mpr (by simpa only [mul_comm] using h)
  refine ⟨retained, Finset.filter_subset _ _, by linarith, ?_⟩
  intro a ha
  exact (Finset.mem_filter.mp ha).2

theorem retain_simultaneous_small_mean_error {Ω J : Type*} [Fintype Ω] [Fintype J]
    (p : FiniteProbabilityWeights Ω) (productive : Finset Ω) (err : J → Ω → ℝ)
    (herr : ∀ j a, 0 ≤ err j a) {tau kappa : ℝ} (htau : 0 < tau)
    (hproductive : kappa ≤ p.mass productive)
    (hmean : (∑ j, p.mean (err j)) ≤ kappa * tau / 4) :
    ∃ retained : Finset Ω, retained ⊆ productive ∧
      3 * kappa / 4 ≤ p.mass retained ∧ ∀ a ∈ retained, ∀ j, err j a ≤ tau := by
  obtain ⟨retained, hsub, hmass, hgood⟩ := p.retain_simultaneous_mean_error productive err herr htau
  have hdiv : (∑ j, p.mean (err j)) / tau ≤ kappa / 4 :=
    (div_le_iff₀ htau).mpr (by nlinarith)
  exact ⟨retained, hsub, by linarith, hgood⟩

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

theorem exists_weighted_exponential_constant_fiber {Ω β : Type*} [Fintype Ω]
    (outer : FiniteProbabilityWeights Ω) (S : Finset Ω) (hS : 0 < outer.mass S)
    (f : Ω → β) (A : Set β) (hA : A.Finite) (hf : ∀ x ∈ S, f x ∈ A)
    {C : ℝ} (hcount : (A.ncard : ℝ) ≤ Real.exp C) :
    ∃ y ∈ A, ∃ T : Finset Ω, T ⊆ S ∧ T.Nonempty ∧ (∀ x ∈ T, f x = y) ∧
      Real.exp (-C) * outer.mass S ≤ outer.mass T := by
  classical
  have hSne : S.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty, lt_self_iff_false] at hS
  obtain ⟨x₀, hx₀⟩ := hSne
  let : Fintype A := hA.fintype
  let default : A := ⟨f x₀, hf x₀ hx₀⟩
  let : Nonempty A := ⟨default⟩
  let code : Ω → A := fun x => if hx : x ∈ S then ⟨f x, hf x hx⟩ else default
  obtain ⟨y, hy⟩ := outer.exists_code_fiber_mass S code
  let T := S.filter (fun x => code x = y)
  have hcard : (Fintype.card A : ℝ) ≤ Real.exp C := by
    simpa only [Set.fintypeCard_eq_ncard] using hcount
  have hcardpos : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hmass : Real.exp (-C) * outer.mass S ≤ outer.mass T := by
    calc
      _ = outer.mass S / Real.exp C := by
        rw [Real.exp_neg, div_eq_mul_inv, mul_comm]
      _ ≤ outer.mass S / Fintype.card A :=
        div_le_div_of_nonneg_left hS.le hcardpos hcard
      _ ≤ outer.mass T := by
        convert hy using 1
        apply congrArg outer.mass
        ext x
        simp only [T, Finset.mem_filter]
  have hTpos : 0 < outer.mass T := (mul_pos (Real.exp_pos _) hS).trans_le hmass
  have hTne : T.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty, lt_self_iff_false] at hTpos
  refine ⟨y.val, y.property, T, Finset.filter_subset _ _, hTne, ?_, hmass⟩
  intro x hx
  have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
  have he := congrArg Subtype.val (Finset.mem_filter.mp hx).2
  simpa only [code, dite_eq_left hxS] using he

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_linear_model_partner {V I : Type*}
    [AddCommGroup V] [Module ℂ V] [Fintype I]
    (test : V →ₗ[ℂ] ℂ) (v e : V) (Q : I → V) (c : I → ℂ)
    (hmodel : v = (∑ i, c i • Q i) + e) {delta M : ℝ}
    (hdelta : 0 < delta) (hM : 0 < M) (hc : (∑ i, ‖c i‖) ≤ M)
    (herr : ‖test e‖ ≤ delta / 2) (hscore : delta ≤ ‖test v‖) :
    ∃ i, delta / (2 * M) ≤ ‖test (Q i)‖ := by
  have hid : test v = (∑ i, c i * test (Q i)) + test e := by
    rw [hmodel, map_add, map_sum]
    simp only [map_smul, smul_eq_mul]
  have hsum : delta / 2 ≤ ‖∑ i, c i * test (Q i)‖ := by
    have ht := norm_add_le (∑ i, c i * test (Q i)) (test e)
    rw [← hid] at ht
    linarith
  obtain ⟨i, hi⟩ := exists_large_weighted_term c (fun i => test (Q i))
    (by positivity : 0 < delta / 2) hM hc hsum
  refine ⟨i, ?_⟩
  convert hi using 1; ring

theorem exists_fixed_linear_model_partners {Ω K V : Type*} {I : K → Type*}
    [Fintype Ω] [Fintype K] [∀ k, Fintype (I k)] [∀ k, Nonempty (I k)]
    [AddCommGroup V] [Module ℂ V]
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (v e : K → V) (Q : ∀ k, I k → V) (c : ∀ k, I k → ℂ)
    (test : Ω → K → V →ₗ[ℂ] ℂ) (err : K → Ω → ℝ)
    (hmodel : ∀ k, v k = (∑ i, c k i • Q k i) + e k)
    {delta M kappa : ℝ} (hdelta : 0 < delta) (hM : 0 < M)
    (hc : ∀ k, (∑ i, ‖c k i‖) ≤ M)
    (herr : ∀ k a, 0 ≤ err k a)
    (htest : ∀ a ∈ productive, ∀ k, ‖test a k (e k)‖ ≤ err k a)
    (hproductive : kappa ≤ outer.mass productive)
    (hmean : (∑ k, outer.mean (err k)) ≤ kappa * (delta / 2) / 4)
    (hscore : ∀ a ∈ productive, ∀ k, delta ≤ ‖test a k (v k)‖) :
    ∃ (partner : ∀ k, I k) (retained : Finset Ω),
      retained ⊆ productive ∧
      (3 * kappa / 4) / (∏ k, (Fintype.card (I k) : ℝ)) ≤ outer.mass retained ∧
      ∀ a ∈ retained, ∀ k, delta / (2 * M) ≤ ‖test a k (Q k (partner k))‖ := by
  obtain ⟨good, hgood, hmass, herrors⟩ := outer.retain_simultaneous_small_mean_error
    productive err herr (by positivity : 0 < delta / 2) hproductive hmean
  have hex (a : Ω) (ha : a ∈ good) (k : K) :
      ∃ i, delta / (2 * M) ≤ ‖test a k (Q k i)‖ :=
    exists_linear_model_partner (test a k) (v k) (e k) (Q k) (c k) (hmodel k)
      hdelta hM (hc k) ((htest a (hgood ha) k).trans (herrors a ha k)) (hscore a (hgood ha) k)
  let choice : Ω → ∀ k, I k := fun a k =>
    if ha : a ∈ good then Classical.choose (hex a ha k) else Classical.choice inferInstance
  have hchoice (a : Ω) (ha : a ∈ good) (k : K) :
      delta / (2 * M) ≤ ‖test a k (Q k (choice a k))‖ := by
    dsimp only [choice]
    rw [dite_eq_left ha]
    exact Classical.choose_spec (hex a ha k)
  obtain ⟨partner, hpartner⟩ := outer.exists_code_fiber_mass good choice
  let retained := good.filter (fun a => choice a = partner)
  have hretained : retained ⊆ good := Finset.filter_subset _ _
  refine ⟨partner, retained, fun a ha => hgood (hretained ha), ?_, ?_⟩
  · have hcard : (Fintype.card (∀ k, I k) : ℝ) = ∏ k, (Fintype.card (I k) : ℝ) := by simp
    rw [hcard] at hpartner
    have h := (div_le_div_of_nonneg_right hmass (by positivity : 0 ≤ ∏ k, (Fintype.card (I k) : ℝ))).trans hpartner
    convert h using 1; try rfl
    congr 1
    ext a
    simp only [retained, Finset.mem_filter]
  · intro a ha k
    have he := (Finset.mem_filter.mp ha).2
    rw [← he]
    exact hchoice a (hretained ha) k

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem fixedParameter_observed_tail_of_tests
    {X T A : Type*} [Fintype X] [Fintype T]
    (source : FiniteProbabilityWeights X) (parameter : FiniteProbabilityWeights T)
    (observe : X → A) (value : T → A → ℝ) {gap bound : ℝ} (hgap : 0 < gap)
    (htest : ∀ w : A → ℝ, (∀ x, 0 ≤ w (observe x) ∧ w (observe x) ≤ 1) →
      (parameter.prod source).mean (fun tx => w (observe tx.2) * value tx.1 (observe tx.2)) ≤ gap * bound) :
    source.eventProbability (fun x => gap < parameter.mean (fun t => value t (observe x))) ≤ bound := by
  let w : A → ℝ := fun z => if gap < parameter.mean (fun t => value t z) then 1 else 0
  have hw (x) : 0 ≤ w (observe x) ∧ w (observe x) ≤ 1 := by
    dsimp only [w]
    split_ifs <;> norm_num
  have hup := htest w hw
  rw [FiniteProbabilityWeights.mean_prod, FiniteProbabilityWeights.mean_comm] at hup
  simp only [FiniteProbabilityWeights.mean_const_mul] at hup
  have hlow : gap * source.eventProbability
      (fun x => gap < parameter.mean (fun t => value t (observe x))) ≤
      source.mean (fun x => w (observe x) * parameter.mean (fun t => value t (observe x))) := by
    rw [FiniteProbabilityWeights.eventProbability, ← source.mean_const_mul]
    apply source.mean_mono
    intro x
    dsimp only [w]
    split_ifs with hx
    · simpa only [mul_one, one_mul] using hx.le
    · simp only [mul_zero, zero_mul, le_refl]
  exact (mul_le_mul_iff_right₀ hgap).mp (hlow.trans hup)

theorem fixedParameter_observed_tail_exp
    {X T A : Type*} [Fintype X] [Fintype T]
    (source : FiniteProbabilityWeights X) (parameter : FiniteProbabilityWeights T)
    (observe : X → A) (value : T → A → ℝ) (p dominationLog : ℝ)
    (htest : ∀ w : A → ℝ, (∀ x, 0 ≤ w (observe x) ∧ w (observe x) ≤ 1) →
      (parameter.prod source).mean (fun tx => w (observe tx.2) * value tx.1 (observe tx.2)) ≤
        Real.exp (-(2 * p + dominationLog)) / 2) :
    source.eventProbability (fun x => Real.exp (-p) < parameter.mean (fun t => value t (observe x))) ≤
      Real.exp (-(p + dominationLog)) := by
  apply fixedParameter_observed_tail_of_tests source parameter observe value (Real.exp_pos (-p))
  intro w hw
  apply (htest w hw).trans
  rw [← Real.exp_add]
  have he : -p + -(p + dominationLog) = -(2 * p + dominationLog) := by ring
  rw [he]
  linarith [Real.exp_pos (-(2 * p + dominationLog))]

theorem fixedParameter_observed_tail_dominated
    {X T A : Type*} [Fintype X] [Fintype T]
    (source outer : FiniteProbabilityWeights X) (parameter : FiniteProbabilityWeights T)
    (observe : X → A) (value : T → A → ℝ) (p dominationLog : ℝ)
    (hdom : ∀ x, outer.weight x ≤ Real.exp dominationLog * source.weight x)
    (htest : ∀ w : A → ℝ, (∀ x, 0 ≤ w (observe x) ∧ w (observe x) ≤ 1) →
      (parameter.prod source).mean (fun tx => w (observe tx.2) * value tx.1 (observe tx.2)) ≤
        Real.exp (-(2 * p + dominationLog)) / 2) :
    outer.eventProbability (fun x => Real.exp (-p) < parameter.mean (fun t => value t (observe x))) ≤
      Real.exp (-p) := by
  have ht := fixedParameter_observed_tail_exp source parameter observe value p dominationLog htest
  calc
    _ ≤ Real.exp dominationLog * source.eventProbability
        (fun x => Real.exp (-p) < parameter.mean (fun t => value t (observe x))) :=
      outer.eventProbability_le_of_weight_le source _ hdom _
    _ ≤ Real.exp dominationLog * Real.exp (-(p + dominationLog)) :=
      mul_le_mul_of_nonneg_left ht (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem uniform_injective_mean_le {B X : Type*}
    [Fintype B] [Nonempty B] [Fintype X] [Nonempty X]
    (F : B → X) (hF : Function.Injective F) (φ : X → ℝ) (hφ : ∀ x, 0 ≤ φ x) :
    (uniform B).mean (fun b => φ (F b)) ≤
      ((Fintype.card X : ℝ) / Fintype.card B) * (uniform X).mean φ := by
  have hsum : (∑ b, φ (F b)) ≤ ∑ x, φ x :=
    Finset.sum_le_sum_of_injOn F hF.injOn (Finset.subset_univ _)
      (fun _ _ => le_rfl) (fun x _ _ => hφ x)
  rw [uniform_mean, uniform_mean, Fintype.expect_eq_sum_div_card,
    Fintype.expect_eq_sum_div_card]
  have hX : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ (∑ x, φ x) / Fintype.card B := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)
    _ = _ := by field_simp

theorem uniform_base_reweight_test_le {B Ω X : Type*}
    [Fintype B] [Nonempty B] [Fintype Ω] [Fintype X] [Nonempty X]
    (q : FiniteProbabilityWeights Ω) (D : B × Ω → ℝ) (hD : ∀ z, 0 ≤ D z)
    (hZ : 0 < ((uniform B).prod q).mean D)
    (F : B × Ω → X) (hF : ∀ z, Function.Injective (fun b => F (b, z)))
    (φ : X → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    {M ε a : ℝ} (hM : 0 ≤ M) (ha : 0 < a)
    (hlower : a ≤ ((uniform B).prod q).mean D)
    (hlocal : ∀ b, q.mean (fun z => D (b, z) * φ (F (b, z))) ≤
      M * q.mean (fun z => φ (F (b, z))) + ε) :
    (((uniform B).prod q).reweightPositive D hD hZ).mean (fun z => φ (F z)) ≤
      ((M * ((Fintype.card X : ℝ) / Fintype.card B)) * (uniform X).mean φ + ε) / a := by
  have href : ((uniform B).prod q).mean (fun z => φ (F z)) ≤
      ((Fintype.card X : ℝ) / Fintype.card B) * (uniform X).mean φ := by
    rw [mean_prod, mean_comm]
    exact (q.mean_mono (fun z => uniform_injective_mean_le _ (hF z) φ hφ)).trans_eq
      (q.mean_const _)
  have hraw : ((uniform B).prod q).mean (fun z => D z * φ (F z)) ≤
      M * ((uniform B).prod q).mean (fun z => φ (F z)) + ε := by
    rw [mean_prod, mean_prod]
    exact ((uniform B).mean_mono hlocal).trans_eq (by rw [mean_add, mean_const_mul, mean_const])
  have hnorm := ((uniform B).prod q).reweightPositive_test_le D hD hZ
    (fun z => φ (F z)) (fun z => hφ (F z)) ha hlower hraw
  apply hnorm.trans
  apply div_le_div_of_nonneg_right _ ha.le
  calc
    _ ≤ M * (((Fintype.card X : ℝ) / Fintype.card B) * (uniform X).mean φ) + ε := by
      gcongr
    _ = _ := by ring

theorem siteLaw_excessMass_le_of_test_bound {Ω T X : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    (p : FiniteProbabilityWeights Ω) (r : FiniteProbabilityWeights X) (F : Ω → T → X)
    {C ε : ℝ}
    (htest : ∀ (φ : X → ℝ), (∀ x, φ x ∈ Set.Icc (0 : ℝ) 1) →
      ∀ t, p.mean (fun z => φ (F z t)) ≤ C * r.mean φ + ε) :
    r.excessMass (p.siteLaw F) C ≤ ε := by
  apply excessMass_le_of_mass_le
  intro A
  let φ : X → ℝ := fun x => if x ∈ A then 1 else 0
  have hφ : ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1 := by intro x; dsimp only [φ]; split_ifs <;> norm_num
  have hmean : (p.siteLaw F).mean φ ≤ C * r.mean φ + ε := by
    rw [siteLaw_mean]
    simp_rw [← uniform_mean]
    rw [mean_comm]
    exact ((uniform T).mean_mono (htest φ hφ)).trans_eq ((uniform T).mean_const _)
  have hfilter : Finset.univ.filter (fun x => x ∈ A) = A := by ext x; simp
  simpa only [mean, φ, mul_ite, mul_one, mul_zero, ← Finset.sum_filter, hfilter,
    mass] using hmean

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

theorem fixedParameter_scalar_tail_mono_slack {X T : Type*} [Fintype X] [Fintype T]
    (outer : FiniteProbabilityWeights X) (parameter : FiniteProbabilityWeights T)
    (h g : X → T → ℝ) {level small large gap bound : ℝ}
    (hg : ∀ x t, 0 ≤ g x t) (hlevel : 0 ≤ level) (hslack : small ≤ large)
    (hbound : outer.eventProbability (fun x => gap < parameter.mean
      (fun t => h x t - (1 + small) * level * g x t)) ≤ bound) :
    outer.eventProbability (fun x => gap < parameter.mean
      (fun t => h x t - (1 + large) * level * g x t)) ≤ bound := by
  apply (outer.eventProbability_mono _ _ ?_).trans hbound
  intro x hx
  apply hx.trans_le
  apply parameter.mean_mono
  intro t
  have hs := mul_le_mul_of_nonneg_right hslack (mul_nonneg hlevel (hg x t))
  nlinarith

end Erdos3

end

section

namespace Erdos3

theorem fixedParameter_scalar_tail_dominated_slack {X T : Type*} [Fintype X] [Fintype T]
    (reference outer : FiniteProbabilityWeights X) (parameter : FiniteProbabilityWeights T)
    (h g : X → T → ℝ) {p level small large : ℝ} (hp : 0 ≤ p)
    (hdom : ∀ x, outer.weight x ≤ Real.exp p * reference.weight x)
    (hg : ∀ x t, 0 ≤ g x t) (hlevel : 0 ≤ level) (hslack : small ≤ large)
    (hbound : reference.eventProbability (fun x => Real.exp (-(2 * p)) < parameter.mean
      (fun t => h x t - (1 + small) * level * g x t)) ≤ Real.exp (-(2 * p))) :
    outer.eventProbability (fun x => Real.exp (-p) < parameter.mean
      (fun t => h x t - (1 + large) * level * g x t)) ≤ Real.exp (-p) := by
  have hlarge := fixedParameter_scalar_tail_mono_slack reference parameter h g hg hlevel hslack hbound
  have hgap : Real.exp (-(2 * p)) ≤ Real.exp (-p) := Real.exp_le_exp.mpr (by linarith)
  have hreference : reference.eventProbability (fun x => Real.exp (-p) < parameter.mean
      (fun t => h x t - (1 + large) * level * g x t)) ≤ Real.exp (-(2 * p)) :=
    (reference.eventProbability_mono _ _ (fun _ hx => hgap.trans_lt hx)).trans hlarge
  calc
    _ ≤ Real.exp p * reference.eventProbability (fun x => Real.exp (-p) < parameter.mean
        (fun t => h x t - (1 + large) * level * g x t)) :=
      outer.eventProbability_le_of_weight_le reference (Real.exp p) hdom _
    _ ≤ Real.exp p * Real.exp (-(2 * p)) :=
      mul_le_mul_of_nonneg_left hreference (Real.exp_pos p).le
    _ = Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
