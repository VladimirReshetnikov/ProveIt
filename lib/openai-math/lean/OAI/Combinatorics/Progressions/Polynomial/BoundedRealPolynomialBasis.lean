import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.Replicate
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

noncomputable def paddedExponentWord {K : Type*} (m : K →₀ ℕ) (h : ℕ)
    (hm : m.sum (fun _ n => n) ≤ h) : List.Vector (Option K) h :=
  ⟨(m.toMultiset.map some + Multiset.replicate (h - m.sum (fun _ n => n)) none).toList, by
    rw [Multiset.length_toList, Multiset.card_add, Multiset.card_map, Multiset.card_replicate,
      Finsupp.card_toMultiset]
    exact Nat.add_sub_of_le hm⟩

theorem paddedExponentWord_count {K : Type*} [DecidableEq K] (m : K →₀ ℕ) (h : ℕ)
    (hm : m.sum (fun _ n => n) ≤ h) (k : K) :
    ((paddedExponentWord m h hm).val : Multiset (Option K)).count (some k) = m k := by
  change Multiset.count (some k)
    ((m.toMultiset.map some + Multiset.replicate (h - m.sum (fun _ n => n)) none).toList :
      Multiset (Option K)) = m k
  rw [Multiset.coe_toList, Multiset.count_add,
    Multiset.count_map_eq_count' _ _ (Option.some_injective _)]
  simp [Multiset.mem_replicate]

theorem boundedExponentSet_card_le {K : Type*} [Fintype K] (s : Finset (K →₀ ℕ)) (h : ℕ)
    (hs : ∀ m ∈ s, m.sum (fun _ n => n) ≤ h) : s.card ≤ (Fintype.card K + 1) ^ h := by
  classical
  let f : s → List.Vector (Option K) h := fun m => paddedExponentWord m.val h (hs m.val m.property)
  have hf : Function.Injective f := by
    intro m n he
    apply Subtype.ext
    apply Finsupp.ext
    intro k
    have hc := congrArg (fun v : List.Vector (Option K) h => (v.val : Multiset (Option K)).count (some k)) he
    simpa only [f, paddedExponentWord_count] using hc
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, card_vector, Fintype.card_option] using hc

theorem monomialArray_card_le {K T : Type*} [Fintype K] (s : Finset T)
    (exponent : T → K →₀ ℕ) (hinj : Set.InjOn exponent s) (h : ℕ)
    (hs : ∀ t ∈ s, (exponent t).sum (fun _ n => n) ≤ h) : s.card ≤ (Fintype.card K + 1) ^ h := by
  classical
  rw [← Finset.card_image_of_injOn hinj]
  apply boundedExponentSet_card_le
  intro m hm
  rcases Finset.mem_image.mp hm with ⟨t, ht, rfl⟩
  exact hs t ht

theorem mvPolynomial_support_card_le_totalDegree {K : Type*} [Fintype K]
    (p : MvPolynomial K ℝ) {h : ℕ} (hp : p.totalDegree ≤ h) :
    p.support.card ≤ (Fintype.card K + 1) ^ h :=
  boundedExponentSet_card_le p.support h (fun _ hm => (MvPolynomial.le_totalDegree hm).trans hp)

open scoped BigOperators

theorem monomialArray_abs_sum_le {K T : Type*} [Fintype K] (s : Finset T)
    (exponent : T → K →₀ ℕ) (hinj : Set.InjOn exponent s) (h : ℕ)
    (hs : ∀ t ∈ s, (exponent t).sum (fun _ n => n) ≤ h)
    (weight : T → ℝ) {M : ℝ} (hM : 0 ≤ M) (hw : ∀ t ∈ s, |weight t| ≤ M) :
    (∑ t ∈ s, |weight t|) ≤ ((Fintype.card K : ℝ) + 1) ^ h * M := by
  have hc : (s.card : ℝ) ≤ ((Fintype.card K : ℝ) + 1) ^ h := by
    exact_mod_cast monomialArray_card_le s exponent hinj h hs
  calc
    _ ≤ ∑ _t ∈ s, M := Finset.sum_le_sum hw
    _ = (s.card : ℝ) * M := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hM

theorem coefficientArray_slot_count {D K : Type*} [Fintype D] [Fintype K]
    {T : D → Type*} (terms : ∀ d, Finset (T d)) (exponent : ∀ d, T d → K →₀ ℕ)
    (hinj : ∀ d, Set.InjOn (exponent d) (terms d)) (h : ℕ)
    (hs : ∀ d t, t ∈ terms d → (exponent d t).sum (fun _ n => n) ≤ h) :
    Fintype.card (Σ d, {t // t ∈ terms d}) ≤ Fintype.card D * (Fintype.card K + 1) ^ h := by
  classical
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _d : D, (Fintype.card K + 1) ^ h := by
      apply Finset.sum_le_sum
      intro d _
      simpa only [Fintype.card_coe] using monomialArray_card_le (terms d) (exponent d) (hinj d) h (hs d)
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev BoundedIntegerExponent (K : Type*) (h : ℕ) :=
  {e : K →₀ ℕ // e.sum (fun _ n => n) ≤ h}

noncomputable instance boundedIntegerExponentFintype (K : Type*) [Fintype K] (h : ℕ) :
    Fintype (BoundedIntegerExponent K h) := by
  classical
  let f : BoundedIntegerExponent K h → List.Vector (Option K) h :=
    fun e => paddedExponentWord e.val h e.property
  apply Fintype.ofInjective f
  intro e d hed
  apply Subtype.ext
  apply Finsupp.ext
  intro k
  have hc := congrArg (fun v : List.Vector (Option K) h =>
    (v.val : Multiset (Option K)).count (some k)) hed
  simpa only [f, paddedExponentWord_count] using hc

theorem boundedIntegerPolynomial_expansion {K : Type*} [Fintype K]
    (p : MvPolynomial K ℤ) (h : ℕ) (hp : p.totalDegree ≤ h) :
    (∑ e : BoundedIntegerExponent K h,
      MvPolynomial.C (p.coeff e.val) * MvPolynomial.monomial e.val 1) = p := by
  classical
  simp only [MvPolynomial.C_mul_monomial, mul_one]
  ext m
  rw [MvPolynomial.coeff_sum]
  by_cases hm : m.sum (fun _ n => n) ≤ h
  · let e : BoundedIntegerExponent K h := ⟨m, hm⟩
    rw [Finset.sum_eq_single e]
    · simp [e, MvPolynomial.coeff_monomial]
    · intro d _ hde
      have hdm : d.val ≠ m := fun heq => hde (Subtype.ext heq)
      simp [MvPolynomial.coeff_monomial, hdm]
    · simp
  · have hzero : p.coeff m = 0 := by
      apply MvPolynomial.notMem_support_iff.mp
      intro hmem
      exact hm ((MvPolynomial.le_totalDegree hmem).trans hp)
    rw [hzero]
    apply Finset.sum_eq_zero
    intro e _
    have hem : e.val ≠ m := fun heq => hm (heq ▸ e.property)
    simp [MvPolynomial.coeff_monomial, hem]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

instance boundedIntegerExponentInhabited (K : Type*) (h : ℕ) :
    Inhabited (BoundedIntegerExponent K h) := ⟨⟨0, by simp⟩⟩

theorem boundedRealPolynomial_expansion {K : Type*} [Fintype K]
    (p : MvPolynomial K ℝ) (h : ℕ) (hp : p.totalDegree ≤ h) :
    (∑ e : BoundedIntegerExponent K h,
      MvPolynomial.C (p.coeff e.val) * MvPolynomial.monomial e.val 1) = p := by
  classical
  simp only [MvPolynomial.C_mul_monomial, mul_one]
  ext m
  rw [MvPolynomial.coeff_sum]
  by_cases hm : m.sum (fun _ n => n) ≤ h
  · let e : BoundedIntegerExponent K h := ⟨m, hm⟩
    rw [Finset.sum_eq_single e]
    · simp [e, MvPolynomial.coeff_monomial]
    · intro d _ hde
      have hdm : d.val ≠ m := fun heq => hde (Subtype.ext heq)
      simp [MvPolynomial.coeff_monomial, hdm]
    · simp
  · have hzero : p.coeff m = 0 := by
      apply MvPolynomial.notMem_support_iff.mp
      intro hmem
      exact hm ((MvPolynomial.le_totalDegree hmem).trans hp)
    rw [hzero]
    apply Finset.sum_eq_zero
    intro e _
    have hem : e.val ≠ m := fun heq => hm (heq ▸ e.property)
    simp [MvPolynomial.coeff_monomial, hem]

theorem boundedIntegerExponent_card_le (K : Type*) [Fintype K] (h : ℕ) :
    Fintype.card (BoundedIntegerExponent K h) ≤ (Fintype.card K + 1) ^ h := by
  classical
  let f : BoundedIntegerExponent K h → List.Vector (Option K) h :=
    fun e => paddedExponentWord e.val h e.property
  have hf : Function.Injective f := by
    intro e d hed
    apply Subtype.ext
    apply Finsupp.ext
    intro k
    have hc := congrArg (fun v : List.Vector (Option K) h =>
      (v.val : Multiset (Option K)).count (some k)) hed
    simpa only [f, paddedExponentWord_count] using hc
  simpa using Fintype.card_le_of_injective f hf

end Erdos3

end

end OAI
