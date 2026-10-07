import OAI.Combinatorics.Progressions.Lattices.UniformBoxResidueMass
import OAI.Combinatorics.Progressions.Sampling.RationalForecastGridTail

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def tupleResidueReduction {A : Type*} {q N : ℕ} (hq : q ∣ N) :
    (A → ZMod N) →+ (A → ZMod q) where
  toFun x a := ZMod.castHom hq (ZMod q) (x a)
  map_zero' := by ext a; simp
  map_add' := by
    intro x y
    ext a
    exact map_add (ZMod.castHom hq (ZMod q)) (x a) (y a)

theorem tupleResidueReduction_surjective {A : Type*} {q N : ℕ} (hq : q ∣ N) :
    Function.Surjective (tupleResidueReduction (A := A) hq) := by
  intro y
  choose x hx using fun a => ZMod.castHom_surjective hq (y a)
  exact ⟨x, funext hx⟩

theorem uniform_residue_reduction_complexMean {A : Type*} [Fintype A] [DecidableEq A]
    {q N : ℕ} [NeZero q] [NeZero N] (hq : q ∣ N) (f : (A → ZMod q) → ℂ) :
    (𝔼 x : A → ZMod N, f (tupleResidueReduction hq x)) = 𝔼 y : A → ZMod q, f y := by
  have hlaw : (FiniteProbabilityWeights.uniform (A → ZMod N)).fiberLaw (tupleResidueReduction hq) =
      FiniteProbabilityWeights.uniform (A → ZMod q) := by
    apply FiniteProbabilityWeights.eq_of_weight_eq
    intro y
    have hh := uniform_mean_surjective_hom_fiber (tupleResidueReduction hq)
      (tupleResidueReduction_surjective hq) y
    change _ = (Fintype.card (A → ZMod q) : ℝ)⁻¹
    convert hh using 1
    unfold FiniteProbabilityWeights.fiberLaw FiniteProbabilityWeights.fiberMean
    congr 1
  have h := (FiniteProbabilityWeights.uniform (A → ZMod N)).fiberLaw_complexMean
    (tupleResidueReduction hq) f
  rw [hlaw] at h
  simpa only [FiniteProbabilityWeights.uniform_complexMean] using h.symm

noncomputable def integerLongPolynomialOutput {A I J : Type*} (poly : J → MvPolynomial (A ⊕ I) ℤ)
    (inactive : I → ℤ) (N : ℕ) (t : A → ZMod N) : J → ℤ :=
  fun j => MvPolynomial.eval (Sum.elim (fun a => ((t a).val : ℤ)) inactive) (poly j)

theorem integerLongPolynomialOutput_reduce {A I J : Type*}
    (poly : J → MvPolynomial (A ⊕ I) ℤ) (inactive : I → ℤ)
    {q N : ℕ} [NeZero N] (hq : q ∣ N) (t : A → ZMod N) :
    (fun j => (integerLongPolynomialOutput poly inactive N t j : ZMod q)) =
      fun j => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
        (Sum.elim (tupleResidueReduction hq t) (fun i => (inactive i : ZMod q))) (poly j) := by
  funext j
  rw [integerLongPolynomialOutput, integerPolynomial_eval_residue]
  congr 1
  funext v
  cases v with
  | inl a =>
    change (((t a).val : ℤ) : ZMod q) = ZMod.castHom hq (ZMod q) (t a)
    have h := congrArg (ZMod.castHom hq (ZMod q)) (ZMod.natCast_zmod_val (t a))
    simpa only [map_natCast, Int.cast_natCast] using h
  | inr i => rfl

theorem rationalPolynomialForecast_marginal {A I J : Type*} [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
    (poly : J → MvPolynomial (A ⊕ I) ℤ) (inactive : I → ℤ)
    {q N : ℕ} [NeZero q] [NeZero N] (hq : q ∣ N) (test : (J → ZMod q) → ℂ) :
    (𝔼 b : J → ZMod N,
      (rationalOutputDensity (FiniteProbabilityWeights.uniform (A → ZMod N))
        (integerLongPolynomialOutput poly inactive N) N b : ℂ) *
        test (fun j => ZMod.castHom hq (ZMod q) (b j))) =
      𝔼 t : A → ZMod q, test (fun j => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
        (Sum.elim t (fun i => (inactive i : ZMod q))) (poly j)) := by
  rw [rationalOutputDensity_divisor_test _ _ hq, FiniteProbabilityWeights.uniform_complexMean]
  simp_rw [integerLongPolynomialOutput_reduce poly inactive hq]
  exact uniform_residue_reduction_complexMean (A := A) (q := q) (N := N) hq
    (fun t => test (fun j => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
      (Sum.elim t (fun i => (inactive i : ZMod q))) (poly j)))

theorem rationalInactivePolynomialForecast_marginal
    {Ω A I J Z : Type*} [Fintype Ω] [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J] [Fintype Z]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (poly : J → MvPolynomial (A ⊕ I) ℤ) (inactiveCoord : Ω → I → ℤ)
    {q N : ℕ} [NeZero q] [NeZero N] (hq : q ∣ N)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0) (test : Z → (J → ZMod q) → ℂ) :
    (∑ z, 𝔼 b : J → ZMod N,
      ((rationalInactiveForecast inactive
        (fun _ => FiniteProbabilityWeights.uniform (A → ZMod N)) gridPoint
        (fun i => integerLongPolynomialOutput poly (inactiveCoord i) N)
        N gridVolume z b / gridVolume : ℝ) : ℂ) *
          test z (fun j => ZMod.castHom hq (ZMod q) (b j))) =
      inactive.complexMean (fun i => 𝔼 t : A → ZMod q,
        test (gridPoint i) (fun j => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
          (Sum.elim t (fun a => (inactiveCoord i a : ZMod q))) (poly j))) := by
  rw [rationalInactiveForecast_divisor_test _ _ _ _ hq hV]
  congr 1
  funext i
  rw [FiniteProbabilityWeights.uniform_complexMean]
  simp_rw [integerLongPolynomialOutput_reduce poly (inactiveCoord i) hq]
  exact uniform_residue_reduction_complexMean (A := A) (q := q) (N := N) hq
    (fun t => test (gridPoint i) (fun j => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
      (Sum.elim t (fun a => (inactiveCoord i a : ZMod q))) (poly j)))

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

private theorem norm_complexMean_sub_uniform_of_relative_error
    {X : Type*} [Fintype X] [Nonempty X] (p : FiniteProbabilityWeights X)
    (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) {E : ℝ}
    (hweight : ∀ x, |(Fintype.card X : ℝ) * p.weight x - 1| ≤ E) :
    ‖p.complexMean f - (𝔼 x, f x)‖ ≤ E := by
  rw [← FiniteProbabilityWeights.uniform_complexMean]
  apply (FiniteProbabilityWeights.norm_complexMean_sub_le_weight_l1
    p (FiniteProbabilityWeights.uniform X) f hf).trans
  have hc : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  calc
    (∑ x, |p.weight x - (FiniteProbabilityWeights.uniform X).weight x|) ≤
        ∑ _x : X, E / (Fintype.card X : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      change |p.weight x - (Fintype.card X : ℝ)⁻¹| ≤ _
      have he : p.weight x - (Fintype.card X : ℝ)⁻¹ =
          ((Fintype.card X : ℝ) * p.weight x - 1) / Fintype.card X := by
        field_simp
      rw [he, abs_div, abs_of_pos hc]
      exact div_le_div_of_nonneg_right (hweight x) hc.le
    _ = E := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_div_cancel₀ E hc.ne'

theorem integerBox_residue_test_error {A : Type*} [Fintype A] [DecidableEq A]
    (lo hi : A → ℤ) (hlen : ∀ a, lo a < hi a)
    (q : ℕ) [NeZero q] (test : (A → ZMod q) → ℂ) (htest : ∀ r, ‖test r‖ ≤ 1)
    (hsmall : (∑ a, (q : ℝ) / ((hi a - lo a : ℤ) : ℝ)) ≤ 1 / 2) :
    ‖(integerBoxUniformWeights lo hi hlen).complexMean
      (fun x => test (integerVectorResidue q (fun a => (x a).val))) -
        (𝔼 r : A → ZMod q, test r)‖ ≤
      2 * ∑ a, (q : ℝ) / ((hi a - lo a : ℤ) : ℝ) := by
  rw [← FiniteProbabilityWeights.fiberLaw_complexMean]
  apply norm_complexMean_sub_uniform_of_relative_error _ test htest
  intro r
  simpa only [Fintype.card_fun, ZMod.card, Nat.cast_pow] using
    integerBox_residue_fiberLaw_relative_error lo hi hlen q r hsmall

theorem rationalPolynomialForecast_box_error
    {A I J : Type*} [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
    (lo hi : A → ℤ) (hlen : ∀ a, lo a < hi a)
    (poly : J → MvPolynomial (A ⊕ I) ℤ) (inactive : I → ℤ)
    {q N : ℕ} [NeZero q] [NeZero N] (hq : q ∣ N)
    (test : (J → ZMod q) → ℂ) (htest : ∀ r, ‖test r‖ ≤ 1)
    (hsmall : (∑ a, (q : ℝ) / ((hi a - lo a : ℤ) : ℝ)) ≤ 1 / 2) :
    ‖(integerBoxUniformWeights lo hi hlen).complexMean
      (fun x => test (fun j => (MvPolynomial.eval
        (Sum.elim (fun a => (x a).val) inactive) (poly j) : ZMod q))) -
      (𝔼 b : J → ZMod N,
        (rationalOutputDensity (FiniteProbabilityWeights.uniform (A → ZMod N))
          (integerLongPolynomialOutput poly inactive N) N b : ℂ) *
            test (fun j => ZMod.castHom hq (ZMod q) (b j)))‖ ≤
      2 * ∑ a, (q : ℝ) / ((hi a - lo a : ℤ) : ℝ) := by
  rw [rationalPolynomialForecast_marginal poly inactive hq test]
  have he (x : ∀ a, Finset.Ico (lo a) (hi a)) :
      (fun j => (MvPolynomial.eval (Sum.elim (fun a => (x a).val) inactive)
        (poly j) : ZMod q)) =
      fun j => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
        (Sum.elim (integerVectorResidue q (fun a => (x a).val))
          (fun i => (inactive i : ZMod q))) (poly j) := by
    funext j
    rw [integerPolynomial_eval_residue]
    congr 1
    funext v
    cases v <;> rfl
  simp_rw [he]
  exact integerBox_residue_test_error lo hi hlen q
    (fun r => test (fun j => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
      (Sum.elim r (fun i => (inactive i : ZMod q))) (poly j))) (fun _ => htest _) hsmall

theorem rationalInactivePolynomialForecast_box_error
    {Ω A I J Z : Type*} [Fintype Ω] [Fintype A] [DecidableEq A]
    [Fintype J] [DecidableEq J] [Fintype Z]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (lo hi : A → ℤ) (hlen : ∀ a, lo a < hi a)
    (poly : J → MvPolynomial (A ⊕ I) ℤ) (inactiveCoord : Ω → I → ℤ)
    {q N : ℕ} [NeZero q] [NeZero N] (hq : q ∣ N)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (test : Z → (J → ZMod q) → ℂ) (htest : ∀ z r, ‖test z r‖ ≤ 1)
    (hsmall : (∑ a, (q : ℝ) / ((hi a - lo a : ℤ) : ℝ)) ≤ 1 / 2) :
    ‖inactive.complexMean (fun i => (integerBoxUniformWeights lo hi hlen).complexMean
      (fun x => test (gridPoint i) (fun j => (MvPolynomial.eval
        (Sum.elim (fun a => (x a).val) (inactiveCoord i)) (poly j) : ZMod q)))) -
      (∑ z, 𝔼 b : J → ZMod N,
        ((rationalInactiveForecast inactive
          (fun _ => FiniteProbabilityWeights.uniform (A → ZMod N)) gridPoint
          (fun i => integerLongPolynomialOutput poly (inactiveCoord i) N)
          N gridVolume z b / gridVolume : ℝ) : ℂ) *
            test z (fun j => ZMod.castHom hq (ZMod q) (b j)))‖ ≤
      2 * ∑ a, (q : ℝ) / ((hi a - lo a : ℤ) : ℝ) := by
  rw [rationalInactiveForecast_divisor_test _ _ _ _ hq hV]
  apply (inactive.norm_complexMean_sub_le _ _ (fun _ =>
    2 * ∑ a, (q : ℝ) / ((hi a - lo a : ℤ) : ℝ)) ?_).trans_eq
      (inactive.mean_const _)
  intro i _
  rw [← rationalOutputDensity_divisor_test
    (FiniteProbabilityWeights.uniform (A → ZMod N))
    (integerLongPolynomialOutput poly (inactiveCoord i) N) hq (test (gridPoint i))]
  exact rationalPolynomialForecast_box_error lo hi hlen poly (inactiveCoord i) hq
    (test (gridPoint i)) (htest _) hsmall

end Erdos3

end

end OAI
