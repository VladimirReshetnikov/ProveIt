/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Use prod_le_prod' for generic product comparisons; mathematical statements are unchanged. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import Mathlib.Data.Nat.Factorization.Basic
import OAI.Combinatorics.Progressions.Estimates.ReweightedFiberDomination
import OAI.Combinatorics.Progressions.Polynomial.CRTPolynomialChargeBound
import OAI.Combinatorics.Progressions.Probability.FiniteProductWitnessProbability

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem badPrimeModulusEvent_probability {Ω : Type*} [Fintype Ω]
    (w : FiniteProbabilityWeights Ω) (S : Finset ℕ) (A : ℕ → ℕ) (Qs : ℕ)
    (bad : ℕ → ℕ → Ω → Prop) {η : ℝ} (hη : 0 ≤ η)
    (hjoint : ∀ (T : Finset ℕ), T ⊆ S → ∀ a : ℕ → ℕ,
      (∀ p ∈ T, 0 < a p ∧ a p ≤ A p ∧ Qs ≤ p ^ a p) →
      w.eventProbability (fun x => ∀ p ∈ T, bad p (a p) x) ≤
        1 / ((∏ p ∈ T, p ^ a p : ℕ) : ℝ) ^ 10 + η)
    {d : ℕ} (hd : 0 < d) :
    w.eventProbability (badPrimeModulusEvent S A Qs bad d) ≤ 1 / (d : ℝ) ^ 10 + η := by
  by_cases hvalid : ∀ p ∈ d.primeFactors, p ∈ S ∧ 0 < d.factorization p ∧
      d.factorization p ≤ A p ∧ Qs ≤ p ^ d.factorization p
  · have h := hjoint d.primeFactors (fun p hp => (hvalid p hp).1) d.factorization
      (fun p hp => (hvalid p hp).2)
    rw [← Nat.prod_primeFactors_pow_factorization hd.ne'] at h
    exact (w.eventProbability_mono _ _ (fun _ hx => hx.2)).trans h
  · rw [w.eventProbability_false _ (fun _ hx => hvalid hx.1)]
    positivity

theorem badPrimeModulusEvent_probability_bounded {Ω : Type*} [Fintype Ω]
    (w : FiniteProbabilityWeights Ω) (S : Finset ℕ) (A : ℕ → ℕ) (Qs B : ℕ)
    (bad : ℕ → ℕ → Ω → Prop) {η : ℝ} (hη : 0 ≤ η)
    (hjoint : ∀ (T : Finset ℕ), T ⊆ S → ∀ a : ℕ → ℕ,
      (∀ p ∈ T, 0 < a p ∧ a p ≤ A p ∧ Qs ≤ p ^ a p) →
      (∏ p ∈ T, p ^ a p) ≤ B →
      w.eventProbability (fun x => ∀ p ∈ T, bad p (a p) x) ≤
        1 / ((∏ p ∈ T, p ^ a p : ℕ) : ℝ) ^ 10 + η)
    {d : ℕ} (hd : 0 < d) (hdB : d ≤ B) :
    w.eventProbability (badPrimeModulusEvent S A Qs bad d) ≤ 1 / (d : ℝ) ^ 10 + η := by
  by_cases hvalid : ∀ p ∈ d.primeFactors, p ∈ S ∧ 0 < d.factorization p ∧
      d.factorization p ≤ A p ∧ Qs ≤ p ^ d.factorization p
  · have hprod := Nat.prod_primeFactors_pow_factorization hd.ne'
    have h := hjoint d.primeFactors (fun p hp => (hvalid p hp).1) d.factorization
      (fun p hp => (hvalid p hp).2) (hprod ▸ hdB)
    rw [← hprod] at h
    exact (w.eventProbability_mono _ _ (fun _ hx => hx.2)).trans h
  · rw [w.eventProbability_false _ (fun _ hx => hvalid hx.1)]
    positivity

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem independent_badPrime_joint_probability
    (S : Finset ℕ) {Ω : S → Type*} [∀ p, Fintype (Ω p)]
    (w : ∀ p, FiniteProbabilityWeights (Ω p))
    (localBad : ∀ p, ℕ → Ω p → Prop)
    (bad : ℕ → ℕ → (∀ p, Ω p) → Prop)
    (hlocal : ∀ (p : S) a x, bad p a x ↔ localBad p a (x p))
    (T : Finset ℕ) (hTS : T ⊆ S) (a : ℕ → ℕ)
    (hprob : ∀ (p : S), p.val ∈ T →
      (w p).eventProbability (localBad p (a p)) ≤ 1 / ((p.val ^ a p : ℕ) : ℝ) ^ 10) :
    (FiniteProbabilityWeights.pi w).eventProbability
      (fun x => ∀ p ∈ T, bad p (a p) x) ≤
        1 / ((∏ p ∈ T, p ^ a p : ℕ) : ℝ) ^ 10 := by
  classical
  have hprod := FiniteProbabilityWeights.eventProbability_pi w
    (fun p y => p.val ∈ T → localBad p (a p) y)
  have hmono := (FiniteProbabilityWeights.pi w).eventProbability_mono
    (fun x => ∀ p ∈ T, bad p (a p) x)
    (fun x => ∀ p : S, p.val ∈ T → localBad p (a p) (x p))
    (fun x hx p hp => (hlocal p (a p) x).mp (hx p hp))
  rw [hprod] at hmono
  calc
    _ ≤ ∏ p : S, (w p).eventProbability
        (fun y => p.val ∈ T → localBad p (a p) y) := hmono
    _ ≤ ∏ p : S, if p.val ∈ T then 1 / ((p.val ^ a p : ℕ) : ℝ) ^ 10 else 1 := by
      apply Finset.prod_le_prod₀
      · intro p _
        exact (w p).eventProbability_nonneg _
      · intro p _
        by_cases hp : p.val ∈ T
        · simpa only [hp, true_implies, ite_true] using hprob p hp
        · simp only [hp, false_implies, ite_false, FiniteProbabilityWeights.eventProbability,
            ite_true, FiniteProbabilityWeights.mean_const, le_refl]
    _ = ∏ p ∈ S, if p ∈ T then 1 / ((p ^ a p : ℕ) : ℝ) ^ 10 else 1 :=
      Finset.prod_coe_sort S (fun p => if p ∈ T then 1 / ((p ^ a p : ℕ) : ℝ) ^ 10 else 1)
    _ = ∏ p ∈ T, 1 / ((p ^ a p : ℕ) : ℝ) ^ 10 := by
      rw [← Finset.prod_subset hTS (fun p _ hp => ite_eq_right hp)]
      exact Finset.prod_congr rfl (fun p hp => ite_eq_left hp)
    _ = _ := by
      simp only [one_div, ← Finset.prod_inv_distrib, ← Finset.prod_pow, Nat.cast_prod]

theorem independent_badPrimeModulusEvent_probability
    (S : Finset ℕ) {Ω : S → Type*} [∀ p, Fintype (Ω p)]
    (w : ∀ p, FiniteProbabilityWeights (Ω p))
    (localBad : ∀ p, ℕ → Ω p → Prop)
    (bad : ℕ → ℕ → (∀ p, Ω p) → Prop)
    (hlocal : ∀ (p : S) a x, bad p a x ↔ localBad p a (x p))
    (A : ℕ → ℕ) (Qs : ℕ)
    (hprob : ∀ (p : S) a, 0 < a → a ≤ A p → Qs ≤ p.val ^ a →
      (w p).eventProbability (localBad p a) ≤ 1 / ((p.val ^ a : ℕ) : ℝ) ^ 10)
    {d : ℕ} (hd : 0 < d) :
    (FiniteProbabilityWeights.pi w).eventProbability
      (badPrimeModulusEvent S A Qs bad d) ≤ 1 / (d : ℝ) ^ 10 := by
  have h := badPrimeModulusEvent_probability (FiniteProbabilityWeights.pi w) S A Qs bad
    (η := 0) le_rfl (fun T hTS a ha => ?_) hd
  · simpa only [add_zero] using h
  · simpa only [add_zero] using independent_badPrime_joint_probability S w localBad bad hlocal T hTS a
      (fun p hp => hprob p (a p) (ha p hp).1 (ha p hp).2.1 (ha p hp).2.2)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem largestBadPrimeProduct_probability {Ω : Type*} [Fintype Ω]
    (w : FiniteProbabilityWeights Ω) (S : Finset ℕ) (A : ℕ → ℕ)
    (bad : ℕ → ℕ → Ω → Prop) {Qs Q R : ℕ}
    (hprime : ∀ p ∈ S, p.Prime) (hQs : 2 ≤ Qs) (hQ : 1 ≤ Q) (hR : 0 < R)
    (hdepth : ∀ p ∈ S, p ^ A p ≤ Q) {η : ℝ} (hη : 0 ≤ η)
    (hjoint : ∀ (T : Finset ℕ), T ⊆ S → ∀ a : ℕ → ℕ,
      (∀ p ∈ T, 0 < a p ∧ a p ≤ A p ∧ Qs ≤ p ^ a p) →
      w.eventProbability (fun x => ∀ p ∈ T, bad p (a p) x) ≤
        1 / ((∏ p ∈ T, p ^ a p : ℕ) : ℝ) ^ 10 + η) :
    w.eventProbability (fun x => smallPrimePowerCorrection Qs * R <
        ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x) ≤
      2 / (9 * (R : ℝ) ^ 9) + ((Q : ℝ) + (R : ℝ) ^ 2) * η := by
  let f := fun x p => if Qs ≤ p ^ largestTestedBadDepth A bad p x then
    p ^ largestTestedBadDepth A bad p x else 1
  let E := badPrimeModulusEvent S A Qs bad
  have hfactor (x p) (hp : p ∈ S) : f x p ≤ Q := by
    dsimp only [f]
    split_ifs
    · exact (Nat.pow_le_pow_right (hprime p hp).pos (largestTestedBadDepth_le A bad p x)).trans
        (hdepth p hp)
    · exact hQ
  have hsingle (x p) (hp : p ∈ S) (_hlarge : R < f x p) : E (f x p) x := by
    simpa only [Finset.prod_singleton] using
      largestBadPrime_subproduct_modulus_event S {p} A bad x hQs hprime
        (Finset.singleton_subset_iff.mpr hp)
  have hcomposite (x T) (hTS : T ⊆ S) (_hlo : R < ∏ p ∈ T, f x p)
      (_hhi : (∏ p ∈ T, f x p) ≤ R ^ 2) : E (∏ p ∈ T, f x p) x :=
    largestBadPrime_subproduct_modulus_event S T A bad x hQs hprime hTS
  have hprob (d : ℕ) (hd : R < d) : w.eventProbability (E d) ≤ 1 / (d : ℝ) ^ 10 + η :=
    badPrimeModulusEvent_probability w S A Qs bad hη hjoint (hR.trans hd)
  have hwitness := finite_product_witness_probability w S f E E hR hfactor hsingle hcomposite hη
    (fun _ hd => hprob _ (Finset.mem_Ioc.mp hd).1)
    (fun _ hd => hprob _ (Finset.mem_Ioc.mp hd).1)
  apply (w.eventProbability_mono _ _ ?_).trans hwitness
  intro x hx
  have hcorrection := prime_power_small_correction S (fun p => largestTestedBadDepth A bad p x) hprime hQs
  change R < ∏ p ∈ S, f x p
  by_contra h
  have hle : (∏ p ∈ S, f x p) ≤ R := Nat.le_of_not_gt h
  have hupper := hcorrection.trans (Nat.mul_le_mul_left (smallPrimePowerCorrection Qs) hle)
  exact (Nat.not_lt_of_ge hupper) hx

theorem largestBadPrimeProduct_probability_exact {Ω : Type*} [Fintype Ω]
    (w : FiniteProbabilityWeights Ω) (S : Finset ℕ) (A : ℕ → ℕ)
    (bad : ℕ → ℕ → Ω → Prop) {Qs Q R : ℕ}
    (hprime : ∀ p ∈ S, p.Prime) (hQs : 2 ≤ Qs) (hQ : 1 ≤ Q) (hR : 0 < R)
    (hdepth : ∀ p ∈ S, p ^ A p ≤ Q)
    (hjoint : ∀ (T : Finset ℕ), T ⊆ S → ∀ a : ℕ → ℕ,
      (∀ p ∈ T, 0 < a p ∧ a p ≤ A p ∧ Qs ≤ p ^ a p) →
      w.eventProbability (fun x => ∀ p ∈ T, bad p (a p) x) ≤
        1 / ((∏ p ∈ T, p ^ a p : ℕ) : ℝ) ^ 10) :
    w.eventProbability (fun x => smallPrimePowerCorrection Qs * R <
        ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x) ≤ 2 / (9 * (R : ℝ) ^ 9) := by
  simpa only [add_zero, mul_zero] using
    largestBadPrimeProduct_probability w S A bad hprime hQs hQ hR hdepth
      (η := 0) le_rfl (by intro T hT a ha; simpa only [add_zero] using hjoint T hT a ha)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

def primeArrayBad (S : Finset ℕ) {Ω : S → Type*}
    (localBad : ∀ p, ℕ → Ω p → Prop) (p a : ℕ) (x : ∀ p, Ω p) : Prop :=
  ∃ hp : p ∈ S, localBad ⟨p, hp⟩ a (x ⟨p, hp⟩)

theorem primeArrayBad_iff (S : Finset ℕ) {Ω : S → Type*}
    (localBad : ∀ p, ℕ → Ω p → Prop) (p : S) (a : ℕ) (x : ∀ p, Ω p) :
    primeArrayBad S localBad p a x ↔ localBad p a (x p) := by
  constructor
  · rintro ⟨hp, hbad⟩
    exact hbad
  · intro hbad
    exact ⟨p.property, hbad⟩

theorem independent_largestBadPrimeProduct_probability
    (S : Finset ℕ) {Ω : S → Type*} [∀ p, Fintype (Ω p)]
    (w : ∀ p, FiniteProbabilityWeights (Ω p))
    (localBad : ∀ p, ℕ → Ω p → Prop) (A : ℕ → ℕ) {Qs Q R : ℕ}
    (hprime : ∀ p ∈ S, p.Prime) (hQs : 2 ≤ Qs) (hQ : 1 ≤ Q) (hR : 0 < R)
    (hdepth : ∀ p ∈ S, p ^ A p ≤ Q)
    (hprob : ∀ (p : S) a, 0 < a → a ≤ A p → Qs ≤ p.val ^ a →
      (w p).eventProbability (localBad p a) ≤ 1 / ((p.val ^ a : ℕ) : ℝ) ^ 10) :
    (FiniteProbabilityWeights.pi w).eventProbability (fun x => smallPrimePowerCorrection Qs * R <
      ∏ p ∈ S, p ^ largestTestedBadDepth A (primeArrayBad S localBad) p x) ≤
        2 / (9 * (R : ℝ) ^ 9) := by
  apply largestBadPrimeProduct_probability_exact (FiniteProbabilityWeights.pi w) S A
    (primeArrayBad S localBad) hprime hQs hQ hR hdepth
  intro T hTS a ha
  exact independent_badPrime_joint_probability S w localBad (primeArrayBad S localBad)
    (primeArrayBad_iff S localBad) T hTS a
    (fun p hp => hprob p (a p) (ha p hp).1 (ha p hp).2.1 (ha p hp).2.2)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem largestBadPrimeProduct_probability_bounded {Ω : Type*} [Fintype Ω]
    (w : FiniteProbabilityWeights Ω) (S : Finset ℕ) (A : ℕ → ℕ)
    (bad : ℕ → ℕ → Ω → Prop) {Qs Q R : ℕ}
    (hprime : ∀ p ∈ S, p.Prime) (hQs : 2 ≤ Qs) (hQ : 1 ≤ Q) (hR : 0 < R)
    (hdepth : ∀ p ∈ S, p ^ A p ≤ Q) {η : ℝ} (hη : 0 ≤ η)
    (hjoint : ∀ (T : Finset ℕ), T ⊆ S → ∀ a : ℕ → ℕ,
      (∀ p ∈ T, 0 < a p ∧ a p ≤ A p ∧ Qs ≤ p ^ a p) →
      (∏ p ∈ T, p ^ a p) ≤ max Q (R ^ 2) →
      w.eventProbability (fun x => ∀ p ∈ T, bad p (a p) x) ≤
        1 / ((∏ p ∈ T, p ^ a p : ℕ) : ℝ) ^ 10 + η) :
    w.eventProbability (fun x => smallPrimePowerCorrection Qs * R <
        ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x) ≤
      2 / (9 * (R : ℝ) ^ 9) + ((Q : ℝ) + (R : ℝ) ^ 2) * η := by
  let f := fun x p => if Qs ≤ p ^ largestTestedBadDepth A bad p x then
    p ^ largestTestedBadDepth A bad p x else 1
  let E := badPrimeModulusEvent S A Qs bad
  have hfactor (x p) (hp : p ∈ S) : f x p ≤ Q := by
    dsimp only [f]
    split_ifs
    · exact (Nat.pow_le_pow_right (hprime p hp).pos (largestTestedBadDepth_le A bad p x)).trans
        (hdepth p hp)
    · exact hQ
  have hsingle (x p) (hp : p ∈ S) (_hlarge : R < f x p) : E (f x p) x := by
    simpa only [Finset.prod_singleton] using
      largestBadPrime_subproduct_modulus_event S {p} A bad x hQs hprime
        (Finset.singleton_subset_iff.mpr hp)
  have hcomposite (x T) (hTS : T ⊆ S) (_hlo : R < ∏ p ∈ T, f x p)
      (_hhi : (∏ p ∈ T, f x p) ≤ R ^ 2) : E (∏ p ∈ T, f x p) x :=
    largestBadPrime_subproduct_modulus_event S T A bad x hQs hprime hTS
  have hprob (d : ℕ) (hd : R < d) (hdB : d ≤ max Q (R ^ 2)) : w.eventProbability (E d) ≤ 1 / (d : ℝ) ^ 10 + η :=
    badPrimeModulusEvent_probability_bounded w S A Qs (max Q (R ^ 2)) bad hη hjoint (hR.trans hd) hdB
  have hwitness := finite_product_witness_probability w S f E E hR hfactor hsingle hcomposite hη
    (fun _ hd => hprob _ (Finset.mem_Ioc.mp hd).1
      ((Finset.mem_Ioc.mp hd).2.trans (le_max_left _ _)))
    (fun _ hd => hprob _ (Finset.mem_Ioc.mp hd).1
      ((Finset.mem_Ioc.mp hd).2.trans (le_max_right _ _)))
  apply (w.eventProbability_mono _ _ ?_).trans hwitness
  intro x hx
  have hcorrection := prime_power_small_correction S (fun p => largestTestedBadDepth A bad p x) hprime hQs
  change R < ∏ p ∈ S, f x p
  by_contra h
  have hle : (∏ p ∈ S, f x p) ≤ R := Nat.le_of_not_gt h
  have hupper := hcorrection.trans (Nat.mul_le_mul_left (smallPrimePowerCorrection Qs) hle)
  exact (Nat.not_lt_of_ge hupper) hx

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem exists_early_badPrime_radius {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℕ, 0 < R ∧ ∀ Q : ℕ, 1 ≤ Q →
      0 < δ / (2 * ((Q : ℝ) + (R : ℝ) ^ 2)) ∧
      2 / (9 * (R : ℝ) ^ 9) + ((Q : ℝ) + (R : ℝ) ^ 2) *
        (δ / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))) ≤ δ := by
  obtain ⟨R, hR⟩ := exists_nat_gt (max 1 (4 / (9 * δ)))
  have hR1 : (1 : ℝ) < R := (le_max_left _ _).trans_lt hR
  have hR0 : (0 : ℝ) < R := lt_trans zero_lt_one hR1
  have hRp : (R : ℝ) ≤ (R : ℝ) ^ 9 := by
    calc
      _ = (R : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hR1.le (by omega)
  have hbound : 4 ≤ 9 * δ * (R : ℝ) := by
    have hb := (le_max_right _ _).trans_lt hR
    have hh := (div_lt_iff₀ (by positivity : 0 < 9 * δ)).mp hb
    nlinarith
  have htail : 2 / (9 * (R : ℝ) ^ 9) ≤ δ / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 9 * (R : ℝ) ^ 9)).mpr
    have := mul_le_mul_of_nonneg_left hRp (by positivity : 0 ≤ 9 * δ)
    nlinarith
  refine ⟨R, by exact_mod_cast hR0, ?_⟩
  intro Q hQ
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hden : 0 < (Q : ℝ) + (R : ℝ) ^ 2 := by positivity
  refine ⟨by positivity, ?_⟩
  have heq : ((Q : ℝ) + (R : ℝ) ^ 2) *
      (δ / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))) = δ / 2 := by
    field_simp
  rw [heq]
  linarith

theorem exists_early_badPrimeProduct_cutoff (Qs : ℕ) (hQs : 2 ≤ Qs)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℕ, 0 < R ∧ ∀ (Ω : Type*) [Fintype Ω]
      (w : FiniteProbabilityWeights Ω) (S : Finset ℕ) (A : ℕ → ℕ)
      (bad : ℕ → ℕ → Ω → Prop) (Q : ℕ),
      (∀ p ∈ S, p.Prime) → 1 ≤ Q → (∀ p ∈ S, p ^ A p ≤ Q) →
      (∀ (T : Finset ℕ), T ⊆ S → ∀ a : ℕ → ℕ,
        (∀ p ∈ T, 0 < a p ∧ a p ≤ A p ∧ Qs ≤ p ^ a p) →
        (∏ p ∈ T, p ^ a p) ≤ max Q (R ^ 2) →
        w.eventProbability (fun x => ∀ p ∈ T, bad p (a p) x) ≤
          1 / ((∏ p ∈ T, p ^ a p : ℕ) : ℝ) ^ 10 +
            δ / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))) →
      w.eventProbability (fun x => smallPrimePowerCorrection Qs * R <
        ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x) ≤ δ := by
  obtain ⟨R, hR, hbound⟩ := exists_early_badPrime_radius hδ
  refine ⟨R, hR, ?_⟩
  intro Ω _ w S A bad Q hprime hQ hdepth hjoint
  exact (largestBadPrimeProduct_probability_bounded w S A bad hprime hQs hQ hR hdepth
    (hbound Q hQ).1.le hjoint).trans (hbound Q hQ).2

end Erdos3

end

section

namespace Erdos3

noncomputable def quantitativeBadPrimeRadius (E : ℝ) : ℕ := ⌈4 * Real.exp E⌉₊ + 1

theorem quantitativeBadPrimeRadius_bounds {E : ℝ} (hE : 0 ≤ E) :
    0 < quantitativeBadPrimeRadius E ∧
      (quantitativeBadPrimeRadius E : ℝ) ≤ Real.exp (E + 3) ∧
      2 / (9 * (quantitativeBadPrimeRadius E : ℝ) ^ 9) ≤ Real.exp (-E) / 2 := by
  let R := quantitativeBadPrimeRadius E
  have hR : 0 < R := Nat.succ_pos _
  have hexp : 1 ≤ Real.exp E := Real.one_le_exp hE
  have hlo : 4 * Real.exp E ≤ (R : ℝ) := by
    have hc := Nat.le_ceil (4 * Real.exp E)
    dsimp [R, quantitativeBadPrimeRadius]
    push_cast
    linarith
  have hhi : (R : ℝ) ≤ 4 * Real.exp E + 2 := by
    have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 * Real.exp E)
    dsimp [R, quantitativeBadPrimeRadius]
    push_cast
    linarith
  have hexp3 : (6 : ℝ) ≤ Real.exp 3 := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have h2 : (4 : ℝ) ≤ Real.exp 1 * Real.exp 1 := by nlinarith
    have h3 : (8 : ℝ) ≤ Real.exp 1 * Real.exp 1 * Real.exp 1 := by nlinarith
    have he : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    rw [he]
    linarith
  have hbudget : (R : ℝ) ≤ Real.exp (E + 3) := by
    rw [Real.exp_add]
    have := mul_le_mul_of_nonneg_left hexp3 (Real.exp_pos E).le
    nlinarith
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hRp : (R : ℝ) ≤ (R : ℝ) ^ 9 := by
    calc
      _ = (R : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hR1 (by omega)
  have hprod : 4 ≤ Real.exp (-E) * (R : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hlo (Real.exp_pos (-E)).le
    have he : Real.exp (-E) * Real.exp E = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have htail : 2 / (9 * (R : ℝ) ^ 9) ≤ Real.exp (-E) / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 9 * (R : ℝ) ^ 9)).mpr
    have hh := mul_le_mul_of_nonneg_left hRp (Real.exp_pos (-E)).le
    nlinarith
  exact ⟨hR, hbudget, htail⟩

theorem quantitativeBadPrimeRadius_error {E : ℝ} (hE : 0 ≤ E) (Q : ℕ) (hQ : 1 ≤ Q) :
    let R := quantitativeBadPrimeRadius E
    0 < Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2)) ∧
    2 / (9 * (R : ℝ) ^ 9) + ((Q : ℝ) + (R : ℝ) ^ 2) *
      (Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))) ≤ Real.exp (-E) := by
  dsimp only
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hden : 0 < (Q : ℝ) + (quantitativeBadPrimeRadius E : ℝ) ^ 2 := by positivity
  refine ⟨by positivity, ?_⟩
  have heq : ((Q : ℝ) + (quantitativeBadPrimeRadius E : ℝ) ^ 2) *
      (Real.exp (-E) / (2 * ((Q : ℝ) + (quantitativeBadPrimeRadius E : ℝ) ^ 2))) =
      Real.exp (-E) / 2 := by field_simp
  rw [heq]
  linarith [(quantitativeBadPrimeRadius_bounds hE).2.2]

theorem quantitativeBadPrimeRadius_witness_budget {E V : ℝ}
    (hE : 0 ≤ E) (hV : 0 ≤ V) (Q : ℕ) (hQ : (Q : ℝ) ≤ Real.exp V) :
    let R := quantitativeBadPrimeRadius E
    (max Q (R ^ 2) : ℕ) ≤ Real.exp (V + 2 * E + 6) ∧
    1 / (Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))) ≤
      Real.exp (V + 3 * E + 8) := by
  dsimp only
  let R := quantitativeBadPrimeRadius E
  have hR := (quantitativeBadPrimeRadius_bounds hE).2.1
  have hR2 : (R : ℝ) ^ 2 ≤ Real.exp (2 * E + 6) := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ R) hR 2
    have he : (Real.exp (E + 3)) ^ 2 = Real.exp (2 * E + 6) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    exact hh.trans_eq he
  have hQbig : (Q : ℝ) ≤ Real.exp (V + 2 * E + 6) :=
    hQ.trans (Real.exp_le_exp.mpr (by linarith))
  have hRbig : (R : ℝ) ^ 2 ≤ Real.exp (V + 2 * E + 6) :=
    hR2.trans (Real.exp_le_exp.mpr (by linarith))
  constructor
  · rw [Nat.cast_max, Nat.cast_pow]
    exact max_le hQbig hRbig
  · have hne : Real.exp (-E) ≠ 0 := ne_of_gt (Real.exp_pos _)
    have hrec : 1 / (Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))) =
        2 * ((Q : ℝ) + (R : ℝ) ^ 2) * Real.exp E := by
      rw [one_div_div, Real.exp_neg, div_inv_eq_mul]
    rw [hrec]
    have h4 : (4 : ℝ) ≤ Real.exp 2 := by
      have h1 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      rw [he]
      nlinarith
    calc
      _ ≤ 4 * Real.exp (V + 2 * E + 6) * Real.exp E := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos E).le
        linarith
      _ ≤ Real.exp 2 * Real.exp (V + 2 * E + 6) * Real.exp E := by
        gcongr
      _ = Real.exp (V + 3 * E + 8) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring

end Erdos3

end

section

namespace Erdos3

open scoped Classical

noncomputable def selectedResidueTiltedFiniteLaw {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D) :
    FiniteProbabilityWeights (rectangularWeightIndices 0 V 1) :=
  (selectedResidueFiniteLaw modulus G V hV hZ).reweightPositive (fun x => D x.val)
    (fun x => hD0 x.val) (by rw [selectedResidueFiniteLaw_densityMass]; exact hD)

theorem selectedResidueTiltedFiniteLaw_mean {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D) (f : (K × I → ℤ) → ℝ) :
    (selectedResidueTiltedFiniteLaw modulus G V hV hZ D hD0 hD).mean (fun x => f x.val) =
      ∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal * f x := by
  rw [selectedResidueTiltedFiniteLaw, FiniteProbabilityWeights.reweightPositive_mean,
    selectedResidueFiniteLaw_densityMass,
    selectedResidueFiniteLaw_mean modulus G V hV hZ (fun x => D x * f x),
    selectedResidueDensityPMF_mean]

theorem selectedResidue_fiber_excess_le {K I Y : Type*} [Fintype K] [Fintype I] [Fintype Y]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D) (F : (K × I → ℤ) → Y)
    {C ε : ℝ}
    (he : ∀ S : Finset Y,
      (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal * (if F x ∈ S then 1 else 0)) ≤
        C * (∑' x, (selectedResidueSmoothPMF modulus G V hV hZ x).toReal * (if F x ∈ S then 1 else 0)) + ε) :
    ((selectedResidueFiniteLaw modulus G V hV hZ).fiberLaw (fun x => F x.val)).excessMass
      ((selectedResidueTiltedFiniteLaw modulus G V hV hZ D hD0 hD).fiberLaw (fun x => F x.val)) C ≤ ε := by
  apply FiniteProbabilityWeights.excessMass_le_of_mass_le
  intro S
  rw [FiniteProbabilityWeights.fiberLaw_mass_indicator, FiniteProbabilityWeights.fiberLaw_mass_indicator,
    selectedResidueTiltedFiniteLaw_mean modulus G V hV hZ D hD0 hD (fun x => if F x ∈ S then 1 else 0),
    selectedResidueFiniteLaw_mean modulus G V hV hZ (fun x => if F x ∈ S then 1 else 0)]
  exact he S

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)

theorem selectedResidueTiltedFiniteLaw_event (E : (K × I → ℤ) → Prop) :
    (selectedResidueTiltedFiniteLaw modulus G V hV hZ D hD0 hD).eventProbability
      (fun x => E x.val) =
      ∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
        (if E x then 1 else 0) := by
  exact selectedResidueTiltedFiniteLaw_mean modulus G V hV hZ D hD0 hD
    (fun x => if E x then 1 else 0)

theorem selectedResidueDensityPMF_badPrimeProduct_probability
    (S : Finset ℕ) (A : ℕ → ℕ) (bad : ℕ → ℕ → (K × I → ℤ) → Prop)
    {Qs Q R : ℕ} (hprime : ∀ p ∈ S, p.Prime) (hQs : 2 ≤ Qs)
    (hQ : 1 ≤ Q) (hR : 0 < R) (hdepth : ∀ p ∈ S, p ^ A p ≤ Q)
    {η : ℝ} (hη : 0 ≤ η)
    (hjoint : ∀ (T : Finset ℕ), T ⊆ S → ∀ a : ℕ → ℕ,
      (∀ p ∈ T, 0 < a p ∧ a p ≤ A p ∧ Qs ≤ p ^ a p) →
      (∏ p ∈ T, p ^ a p) ≤ max Q (R ^ 2) →
      (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
        (if ∀ p ∈ T, bad p (a p) x then 1 else 0)) ≤
        1 / ((∏ p ∈ T, p ^ a p : ℕ) : ℝ) ^ 10 + η) :
    (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
      (if smallPrimePowerCorrection Qs * R <
        ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x then 1 else 0)) ≤
      2 / (9 * (R : ℝ) ^ 9) + ((Q : ℝ) + (R : ℝ) ^ 2) * η := by
  have h := largestBadPrimeProduct_probability_bounded
    (selectedResidueTiltedFiniteLaw modulus G V hV hZ D hD0 hD) S A
    (fun p a x => bad p a x.val) hprime hQs hQ hR hdepth hη
    (fun T hT a ha hbound => by
      rw [selectedResidueTiltedFiniteLaw_event modulus G V hV hZ D hD0 hD
        (fun x => ∀ p ∈ T, bad p (a p) x)]
      convert hjoint T hT a ha hbound using 1
      apply tsum_congr
      intro x
      by_cases hx : ∀ p ∈ T, bad p (a p) x <;> simp [hx])
  change (selectedResidueTiltedFiniteLaw modulus G V hV hZ D hD0 hD).eventProbability
    (fun x => smallPrimePowerCorrection Qs * R <
      ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x.val) ≤ _ at h
  rw [selectedResidueTiltedFiniteLaw_event modulus G V hV hZ D hD0 hD
    (fun x => smallPrimePowerCorrection Qs * R <
      ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x)] at h
  convert h using 1
  apply tsum_congr
  intro x
  by_cases hx : smallPrimePowerCorrection Qs * R <
    ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x <;> simp [hx]

theorem exists_early_selectedResidueDensityPMF_badPrimeProduct_cutoff
    (Qs : ℕ) (hQs : 2 ≤ Qs) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℕ, 0 < R ∧ ∀ (K I : Type*) [Fintype K] [Fintype I]
      (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
      (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
      (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
      (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
      (hD : 0 < selectedResidueDensityMass modulus G V D)
      (S : Finset ℕ) (A : ℕ → ℕ) (bad : ℕ → ℕ → (K × I → ℤ) → Prop) (Q : ℕ),
      (∀ p ∈ S, p.Prime) → 1 ≤ Q → (∀ p ∈ S, p ^ A p ≤ Q) →
      (∀ (T : Finset ℕ), T ⊆ S → ∀ a : ℕ → ℕ,
        (∀ p ∈ T, 0 < a p ∧ a p ≤ A p ∧ Qs ≤ p ^ a p) →
        (∏ p ∈ T, p ^ a p) ≤ max Q (R ^ 2) →
        (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
          (if ∀ p ∈ T, bad p (a p) x then 1 else 0)) ≤
          1 / ((∏ p ∈ T, p ^ a p : ℕ) : ℝ) ^ 10 +
            δ / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))) →
      (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
        (if smallPrimePowerCorrection Qs * R <
          ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x then 1 else 0)) ≤ δ := by
  obtain ⟨R, hR, hbound⟩ := exists_early_badPrime_radius hδ
  refine ⟨R, hR, ?_⟩
  intro K I _ _ modulus G V hV hZ D hD0 hD S A bad Q hprime hQ hdepth hjoint
  exact (selectedResidueDensityPMF_badPrimeProduct_probability modulus G V hV hZ D hD0 hD
    S A bad hprime hQs hQ hR hdepth (hbound Q hQ).1.le hjoint).trans (hbound Q hQ).2

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

def prescribedDeepBad {Ω : Type*} (b : ℕ → ℕ)
    (bad : ℕ → ℕ → Ω → Prop) (p a : ℕ) (x : Ω) : Prop := b p < a ∧ bad p a x

theorem largestTestedBadDepth_le_prescribed_max {Ω : Type*}
    (A b : ℕ → ℕ) (bad : ℕ → ℕ → Ω → Prop) (p : ℕ) (x : Ω) :
    largestTestedBadDepth A bad p x ≤
      max (b p) (largestTestedBadDepth A (prescribedDeepBad b bad) p x) := by
  apply Finset.sup_le
  intro a ha
  obtain ⟨ha, hbad⟩ := Finset.mem_filter.mp ha
  by_cases h : b p < a
  · exact (Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨ha, h, hbad⟩)).trans
      (le_max_right _ _)
  · exact (Nat.le_of_not_gt h).trans (le_max_left _ _)

theorem largestBadPrimeProduct_le_prescribed {Ω : Type*}
    (S : Finset ℕ) (A b : ℕ → ℕ) (bad : ℕ → ℕ → Ω → Prop)
    (hprime : ∀ p ∈ S, p.Prime) (x : Ω) :
    (∏ p ∈ S, p ^ largestTestedBadDepth A bad p x) ≤
      (∏ p ∈ S, p ^ b p) *
        ∏ p ∈ S, p ^ largestTestedBadDepth A (prescribedDeepBad b bad) p x := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod'
  intro p hp
  rw [← pow_add]
  exact Nat.pow_le_pow_right (hprime p hp).pos
    ((largestTestedBadDepth_le_prescribed_max A b bad p x).trans (by omega))

theorem selectedResidueDensityPMF_prescribed_badPrimeProduct
    {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    (S : Finset ℕ) (A b : ℕ → ℕ) (bad : ℕ → ℕ → (K × I → ℤ) → Prop)
    {Qs Q R : ℕ} (hprime : ∀ p ∈ S, p.Prime) (hQs : 2 ≤ Qs)
    (hQ : 1 ≤ Q) (hR : 0 < R) (hdepth : ∀ p ∈ S, p ^ A p ≤ Q)
    {η : ℝ} (hη : 0 ≤ η)
    (hjoint : ∀ (T : Finset ℕ), T ⊆ S → ∀ a : ℕ → ℕ,
      (∀ p ∈ T, 0 < a p ∧ a p ≤ A p ∧ Qs ≤ p ^ a p ∧ b p < a p) →
      (∏ p ∈ T, p ^ a p) ≤ max Q (R ^ 2) →
      (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
        (if ∀ p ∈ T, bad p (a p) x then 1 else 0)) ≤
        1 / ((∏ p ∈ T, p ^ a p : ℕ) : ℝ) ^ 10 + η) :
    (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
      (if (∏ p ∈ S, p ^ b p) * (smallPrimePowerCorrection Qs * R) <
        ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x then 1 else 0)) ≤
      2 / (9 * (R : ℝ) ^ 9) + ((Q : ℝ) + (R : ℝ) ^ 2) * η := by
  let w := selectedResidueTiltedFiniteLaw modulus G V hV hZ D hD0 hD
  have ht := selectedResidueDensityPMF_badPrimeProduct_probability modulus G V hV hZ D hD0 hD
    S A (prescribedDeepBad b bad) hprime hQs hQ hR hdepth hη
    (fun T hT a ha hbound => by
      by_cases hb : ∀ p ∈ T, b p < a p
      · have hh := hjoint T hT a (fun p hp => ⟨(ha p hp).1, (ha p hp).2.1,
          (ha p hp).2.2, hb p hp⟩) hbound
        convert hh using 1
        apply tsum_congr
        intro x
        have he : (∀ p ∈ T, prescribedDeepBad b bad p (a p) x) ↔
            ∀ p ∈ T, bad p (a p) x := by
          simp only [prescribedDeepBad]
          exact ⟨fun h p hp => (h p hp).2, fun h p hp => ⟨hb p hp, h p hp⟩⟩
        simp only [he]
      · have he (x : K × I → ℤ) : ¬ ∀ p ∈ T, prescribedDeepBad b bad p (a p) x :=
          fun h => hb (fun p hp => (h p hp).1)
        simp only [he, ite_false, mul_zero, tsum_zero]
        positivity)
  have hmono := w.eventProbability_mono
    (fun x => (∏ p ∈ S, p ^ b p) * (smallPrimePowerCorrection Qs * R) <
      ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x.val)
    (fun x => smallPrimePowerCorrection Qs * R <
      ∏ p ∈ S, p ^ largestTestedBadDepth A (prescribedDeepBad b bad) p x.val)
    (fun x hx => by
      by_contra h
      have hh := Nat.mul_le_mul_left (∏ p ∈ S, p ^ b p) (Nat.le_of_not_gt h)
      exact (not_lt_of_ge ((largestBadPrimeProduct_le_prescribed S A b bad hprime x.val).trans hh)) hx)
  dsimp only [w] at hmono
  rw [selectedResidueTiltedFiniteLaw_event modulus G V hV hZ D hD0 hD
    (fun x => (∏ p ∈ S, p ^ b p) * (smallPrimePowerCorrection Qs * R) <
      ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x),
    selectedResidueTiltedFiniteLaw_event modulus G V hV hZ D hD0 hD
    (fun x => smallPrimePowerCorrection Qs * R <
      ∏ p ∈ S, p ^ largestTestedBadDepth A (prescribedDeepBad b bad) p x)] at hmono
  refine le_trans ?_ ht
  convert hmono using 1 <;> first | rfl | (apply tsum_congr; intro x; split_ifs <;> rfl)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem selected_factorization_product_dvd (S : Finset ℕ) (n : ℕ) :
    (∏ p ∈ S, p ^ n.factorization p) ∣ n := by
  by_cases hn : n = 0
  · simp [hn]
  have he : (∏ p ∈ S ∩ n.factorization.support, p ^ n.factorization p) =
      ∏ p ∈ S, p ^ n.factorization p := by
    apply Finset.prod_subset Finset.inter_subset_left
    intro p hp hnot
    have hzero : n.factorization p = 0 := by
      apply Finsupp.notMem_support_iff.mp
      exact fun hs => hnot (Finset.mem_inter.mpr ⟨hp, hs⟩)
    simp [hzero]
  rw [← he]
  exact (Finset.prod_dvd_prod_of_subset (S ∩ n.factorization.support)
    n.factorization.support (fun p => p ^ n.factorization p) Finset.inter_subset_right).trans
      (dvd_of_eq (Nat.prod_factorization_pow_eq_self hn))

theorem selected_double_factorization_product_dvd (S : Finset ℕ) (n : ℕ) :
    (∏ p ∈ S, p ^ (2 * n.factorization p)) ∣ n ^ 2 := by
  simp_rw [Nat.mul_comm 2, pow_mul]
  rw [Finset.prod_pow]
  exact pow_dvd_pow_of_dvd (selected_factorization_product_dvd S n) 2

theorem selected_double_factorization_product_le (S : Finset ℕ) {n : ℕ}
    (hn : 0 < n) :
    (∏ p ∈ S, p ^ (2 * n.factorization p)) ≤ n ^ 2 :=
  Nat.le_of_dvd (pow_pos hn 2) (selected_double_factorization_product_dvd S n)

theorem largestBadPrimeProduct_le_stride_sq {Ω : Type*}
    (S : Finset ℕ) (A : ℕ → ℕ) (bad : ℕ → ℕ → Ω → Prop)
    (hprime : ∀ p ∈ S, p.Prime) {stride : ℕ} (hstride : 0 < stride) (x : Ω) :
    (∏ p ∈ S, p ^ largestTestedBadDepth A bad p x) ≤
      stride ^ 2 * ∏ p ∈ S, p ^ largestTestedBadDepth A
        (prescribedDeepBad (fun p => 2 * stride.factorization p) bad) p x := by
  exact (largestBadPrimeProduct_le_prescribed S A
    (fun p => 2 * stride.factorization p) bad hprime x).trans
      (Nat.mul_le_mul_right _ (selected_double_factorization_product_le S hstride))

theorem crtPolynomialCharge_le_of_deep_bad_product {Ω : Type*}
    (S : Finset ℕ) (A e : ℕ → ℕ) (bad : ℕ → ℕ → Ω → Prop)
    (hprime : ∀ p ∈ S, p.Prime) {stride : ℕ} (hstride : 0 < stride)
    (x : Ω) (s : ℕ) {C : ℝ} (hC : 0 ≤ C) {R : ℕ}
    (hdeep : (∏ p ∈ S, p ^ largestTestedBadDepth A
      (prescribedDeepBad (fun p => 2 * stride.factorization p) bad) p x) ≤ R) :
    crtPolynomialCharge (fun p : S => p.val)
      (fun p => largestTestedBadDepth A bad p.val x) (fun p => e p.val) s C ≤
      (((stride ^ 2 * R) * ∏ p : S, p.val ^ e p.val : ℕ) : ℝ) ^
        (modularRankDecayExponent s C * modularRankChargeFactor s) := by
  apply crtPolynomialCharge_le_of_bad_product _ _ _ s hC
  rw [← Finset.prod_subtype S (fun _ => Iff.rfl)
    (fun p : ℕ => p ^ largestTestedBadDepth A bad p x)]
  exact (largestBadPrimeProduct_le_stride_sq S A bad hprime hstride x).trans
      (Nat.mul_le_mul_left (stride ^ 2) hdeep)

theorem column_stride_factorization_le_product {X : Type*} [Fintype X]
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x) (x : X) (p : ℕ) :
    (stride x).factorization p ≤ (∏ x, stride x).factorization p := by
  have hprod : (∏ x, stride x) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun x _ => (hstride x).ne')
  exact (Nat.factorization_le_iff_dvd (hstride x).ne' hprod).mpr
    (Finset.dvd_prod_of_mem stride (Finset.mem_univ x)) p

theorem column_stride_depth_lt_of_product_stride {X : Type*} [Fintype X]
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x) {p a : ℕ}
    (ha : 2 * (∏ x, stride x).factorization p < a) (x : X) :
    2 * (stride x).factorization p < a :=
  (Nat.mul_le_mul_left 2 (column_stride_factorization_le_product stride hstride x p)).trans_lt ha

theorem column_stride_depth_le_of_product_stride {X : Type*} [Fintype X]
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x) {p a : ℕ}
    (ha : 2 * (∏ x, stride x).factorization p < a) (x : X) :
    2 * (stride x).factorization p ≤ a :=
  (column_stride_depth_lt_of_product_stride stride hstride ha x).le

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem selectedResidueDensityPMF_stride_badPrimeProduct
    {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    (S : Finset ℕ) (A : ℕ → ℕ) (bad : ℕ → ℕ → (K × I → ℤ) → Prop)
    {stride Qs Q R : ℕ} (hstride : 0 < stride)
    (hprime : ∀ p ∈ S, p.Prime) (hQs : 2 ≤ Qs)
    (hQ : 1 ≤ Q) (hR : 0 < R) (hdepth : ∀ p ∈ S, p ^ A p ≤ Q)
    {η : ℝ} (hη : 0 ≤ η)
    (hjoint : ∀ (T : Finset ℕ), T ⊆ S → ∀ a : ℕ → ℕ,
      (∀ p ∈ T, 0 < a p ∧ a p ≤ A p ∧ Qs ≤ p ^ a p ∧
        2 * stride.factorization p < a p) →
      (∏ p ∈ T, p ^ a p) ≤ max Q (R ^ 2) →
      (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
        (if ∀ p ∈ T, bad p (a p) x then 1 else 0)) ≤
        1 / ((∏ p ∈ T, p ^ a p : ℕ) : ℝ) ^ 10 + η) :
    (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
      (if stride ^ 2 * (smallPrimePowerCorrection Qs * R) <
        ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x then 1 else 0)) ≤
      2 / (9 * (R : ℝ) ^ 9) + ((Q : ℝ) + (R : ℝ) ^ 2) * η := by
  have hprescribed := selectedResidueDensityPMF_prescribed_badPrimeProduct
    modulus G V hV hZ D hD0 hD S A (fun p => 2 * stride.factorization p) bad
    hprime hQs hQ hR hdepth hη hjoint
  let w := selectedResidueTiltedFiniteLaw modulus G V hV hZ D hD0 hD
  have hmono := w.eventProbability_mono
    (fun x => stride ^ 2 * (smallPrimePowerCorrection Qs * R) <
      ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x.val)
    (fun x => (∏ p ∈ S, p ^ (2 * stride.factorization p)) *
      (smallPrimePowerCorrection Qs * R) <
        ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x.val)
    (fun _ hx => (Nat.mul_le_mul_right _
      (selected_double_factorization_product_le S hstride)).trans_lt hx)
  dsimp only [w] at hmono
  rw [selectedResidueTiltedFiniteLaw_event modulus G V hV hZ D hD0 hD
    (fun x => stride ^ 2 * (smallPrimePowerCorrection Qs * R) <
      ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x),
    selectedResidueTiltedFiniteLaw_event modulus G V hV hZ D hD0 hD
    (fun x => (∏ p ∈ S, p ^ (2 * stride.factorization p)) *
      (smallPrimePowerCorrection Qs * R) <
        ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x)] at hmono
  refine le_trans ?_ hprescribed
  convert hmono using 1 <;> first | rfl | (apply tsum_congr; intro x; split_ifs <;> rfl)

end Erdos3

end

end OAI
