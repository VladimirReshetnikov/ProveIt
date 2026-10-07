/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Use prod_le_prod' for generic product comparisons; mathematical statements are unchanged. -/
import OAI.Compat.Core
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem selected_primePower_factorization (T : Finset ℕ) (a : ℕ → ℕ)
    (hprime : ∀ p ∈ T, Nat.Prime p) (p : ℕ) :
    (∏ q ∈ T, q ^ a q).factorization p = if p ∈ T then a p else 0 := by
  rw [Nat.factorization_prod_apply (fun q hq => pow_ne_zero _ (hprime q hq).ne_zero)]
  calc
    ∑ q ∈ T, (q ^ a q).factorization p =
        ∑ q ∈ T, if p = q then a q else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [(hprime q hq).factorization_pow]
      simp only [Finsupp.single_apply, eq_comm]
    _ = _ := by simp

theorem selected_primePower_primeFactors (T : Finset ℕ) (a : ℕ → ℕ)
    (hprime : ∀ p ∈ T, Nat.Prime p) (ha : ∀ p ∈ T, 0 < a p) :
    (∏ p ∈ T, p ^ a p).primeFactors = T := by
  ext p
  rw [← Nat.support_factorization, Finsupp.mem_support_iff,
    selected_primePower_factorization T a hprime]
  by_cases hp : p ∈ T
  · simp only [hp, ↓reduceIte, iff_true]
    exact (ha p hp).ne'
  · simp only [hp, ↓reduceIte, ne_eq, not_true_eq_false]

theorem selected_primePower_factorization_of_mem (T : Finset ℕ) (a : ℕ → ℕ)
    (hprime : ∀ p ∈ T, Nat.Prime p) {p : ℕ} (hp : p ∈ T) :
    (∏ q ∈ T, q ^ a q).factorization p = a p := by
  rw [selected_primePower_factorization T a hprime, ite_eq_left hp]

def badPrimeModulusEvent {Ω : Type*} (S : Finset ℕ) (A : ℕ → ℕ) (Qs : ℕ)
    (bad : ℕ → ℕ → Ω → Prop) (d : ℕ) (x : Ω) : Prop :=
  (∀ p ∈ d.primeFactors, p ∈ S ∧ 0 < d.factorization p ∧
    d.factorization p ≤ A p ∧ Qs ≤ p ^ d.factorization p) ∧
  (∀ p ∈ d.primeFactors, bad p (d.factorization p) x)

theorem selected_primePower_badPrimeModulusEvent {Ω : Type*}
    (S T : Finset ℕ) (A a : ℕ → ℕ) (Qs : ℕ) (bad : ℕ → ℕ → Ω → Prop)
    (x : Ω) (hprime : ∀ p ∈ T, Nat.Prime p) (hTS : T ⊆ S)
    (ha : ∀ p ∈ T, 0 < a p) (hA : ∀ p ∈ T, a p ≤ A p)
    (hQs : ∀ p ∈ T, Qs ≤ p ^ a p) (hbad : ∀ p ∈ T, bad p (a p) x) :
    badPrimeModulusEvent S A Qs bad (∏ p ∈ T, p ^ a p) x := by
  constructor
  · intro p hp
    have hpT : p ∈ T := by rwa [selected_primePower_primeFactors T a hprime ha] at hp
    rw [selected_primePower_factorization_of_mem T a hprime hpT]
    exact ⟨hTS hpT, ha p hpT, hA p hpT, hQs p hpT⟩
  · intro p hp
    have hpT : p ∈ T := by rwa [selected_primePower_primeFactors T a hprime ha] at hp
    rw [selected_primePower_factorization_of_mem T a hprime hpT]
    exact hbad p hpT

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def largestTestedBadDepth {Ω : Type*} (A : ℕ → ℕ)
    (bad : ℕ → ℕ → Ω → Prop) (p : ℕ) (x : Ω) : ℕ :=
  ((Finset.Icc 1 (A p)).filter (fun a => bad p a x)).sup id

theorem largestTestedBadDepth_le {Ω : Type*} (A : ℕ → ℕ)
    (bad : ℕ → ℕ → Ω → Prop) (p : ℕ) (x : Ω) :
    largestTestedBadDepth A bad p x ≤ A p := by
  exact Finset.sup_le (fun _ ha => (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2)

theorem largestTestedBadDepth_bad {Ω : Type*} (A : ℕ → ℕ)
    (bad : ℕ → ℕ → Ω → Prop) (p : ℕ) (x : Ω)
    (hpos : 0 < largestTestedBadDepth A bad p x) :
    bad p (largestTestedBadDepth A bad p x) x := by
  obtain ⟨a, ha, hle⟩ := (Finset.le_sup_iff hpos).mp
    (le_refl (largestTestedBadDepth A bad p x))
  have hge : a ≤ largestTestedBadDepth A bad p x := Finset.le_sup (f := id) ha
  have heq : a = largestTestedBadDepth A bad p x := le_antisymm hge hle
  exact heq ▸ (Finset.mem_filter.mp ha).2

noncomputable def smallPrimePowerCorrection (Qs : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range Qs).filter Nat.Prime, p ^ Nat.log p (Qs - 1)

theorem prime_power_small_correction (S : Finset ℕ) (b : ℕ → ℕ) {Qs : ℕ}
    (hprime : ∀ p ∈ S, p.Prime) (hQs : 2 ≤ Qs) :
    (∏ p ∈ S, p ^ b p) ≤ smallPrimePowerCorrection Qs *
      ∏ p ∈ S, (if Qs ≤ p ^ b p then p ^ b p else 1) := by
  let small := (Finset.range Qs).filter Nat.Prime
  let g := fun p => p ^ Nat.log p (Qs - 1)
  have hg (p) (hp : p.Prime) : 1 ≤ g p := one_le_pow₀ hp.one_le
  have hlocal (p) (hp : p ∈ S) : p ^ b p ≤ g p * (if Qs ≤ p ^ b p then p ^ b p else 1) := by
    by_cases hlarge : Qs ≤ p ^ b p
    · simp only [hlarge, ite_true]
      simpa only [one_mul] using Nat.mul_le_mul_right (p ^ b p) (hg p (hprime p hp))
    · simp only [hlarge, ite_false, mul_one]
      exact Nat.pow_le_pow_right (hprime p hp).pos
        (Nat.le_log_of_pow_le (hprime p hp).one_lt (by omega))
  have hout (p) (hp : p ∈ S ∪ small) (hnot : p ∉ small) : g p = 1 := by
    have hpp : p.Prime := by
      rcases Finset.mem_union.mp hp with hp | hp
      · exact hprime p hp
      · exact (Finset.mem_filter.mp hp).2
    have hcut : Qs ≤ p := by
      by_contra h
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpp⟩)
    dsimp only [g]
    rw [Nat.log_eq_zero_iff.mpr (Or.inl (by omega)), pow_zero]
  have hbase : (∏ p ∈ S, g p) ≤ smallPrimePowerCorrection Qs := by
    calc
      _ ≤ ∏ p ∈ S ∪ small, g p :=
        Finset.prod_le_prod_of_subset_of_one_le Finset.subset_union_left (fun p hp _ => by
          apply hg
          rcases Finset.mem_union.mp hp with hp | hp
          · exact hprime p hp
          · exact (Finset.mem_filter.mp hp).2)
      _ = ∏ p ∈ small, g p := (Finset.prod_subset Finset.subset_union_right hout).symm
      _ = _ := rfl
  calc
    _ ≤ ∏ p ∈ S, g p * (if Qs ≤ p ^ b p then p ^ b p else 1) :=
      Finset.prod_le_prod' hlocal
    _ = (∏ p ∈ S, g p) * ∏ p ∈ S, (if Qs ≤ p ^ b p then p ^ b p else 1) :=
      Finset.prod_mul_distrib
    _ ≤ _ := Nat.mul_le_mul_right _ hbase

theorem largestBadPrime_large_valid {Ω : Type*} (S : Finset ℕ) (A : ℕ → ℕ)
    (bad : ℕ → ℕ → Ω → Prop) (x : Ω) {Qs p : ℕ} (hQs : 2 ≤ Qs)
    (_hp : p ∈ S) (hlarge : Qs ≤ p ^ largestTestedBadDepth A bad p x) :
    0 < largestTestedBadDepth A bad p x ∧
      largestTestedBadDepth A bad p x ≤ A p ∧
      bad p (largestTestedBadDepth A bad p x) x := by
  have hb : 0 < largestTestedBadDepth A bad p x := by
    by_contra hn
    have heq : largestTestedBadDepth A bad p x = 0 := by omega
    simp only [heq, pow_zero] at hlarge
    omega
  exact ⟨hb, largestTestedBadDepth_le A bad p x, largestTestedBadDepth_bad A bad p x hb⟩

theorem largestBadPrime_subproduct_modulus_event {Ω : Type*}
    (S T : Finset ℕ) (A : ℕ → ℕ) (bad : ℕ → ℕ → Ω → Prop)
    (x : Ω) {Qs : ℕ} (hQs : 2 ≤ Qs) (hprime : ∀ p ∈ S, p.Prime) (hTS : T ⊆ S) :
    badPrimeModulusEvent S A Qs bad
      (∏ p ∈ T, if Qs ≤ p ^ largestTestedBadDepth A bad p x then
        p ^ largestTestedBadDepth A bad p x else 1) x := by
  let U := T.filter (fun p => Qs ≤ p ^ largestTestedBadDepth A bad p x)
  have hUS : U ⊆ S := (Finset.filter_subset _ _).trans hTS
  have hvalid (p) (hp : p ∈ U) := largestBadPrime_large_valid S A bad x hQs
    (hUS hp) (Finset.mem_filter.mp hp).2
  have heq : (∏ p ∈ T, if Qs ≤ p ^ largestTestedBadDepth A bad p x then
      p ^ largestTestedBadDepth A bad p x else 1) =
      ∏ p ∈ U, p ^ largestTestedBadDepth A bad p x := (Finset.prod_filter _ _).symm
  rw [heq]
  exact selected_primePower_badPrimeModulusEvent S U A
    (fun p => largestTestedBadDepth A bad p x) Qs bad x
    (fun p hp => hprime p (hUS hp)) hUS (fun p hp => (hvalid p hp).1)
    (fun p hp => (hvalid p hp).2.1) (fun _ hp => (Finset.mem_filter.mp hp).2)
    (fun p hp => (hvalid p hp).2.2)

end Erdos3

end

end OAI
