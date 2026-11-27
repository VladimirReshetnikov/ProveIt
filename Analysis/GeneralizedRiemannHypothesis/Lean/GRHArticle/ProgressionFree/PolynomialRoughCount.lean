import GRHArticle.ProgressionFree.PolynomialRoughDensity

/-!
# Counting monic rough polynomials

Excluding a monic irreducible deletes a degree-shifted copy of the polynomials
allowed so far. Beyond the total degree of the excluded primes, the normalized
count is exactly the finite Euler product.
-/

namespace GRHArticle.ProgressionFree

open Polynomial UniqueFactorizationMonoid Filter Topology
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F]

private noncomputable def primeExcludingLayer (S : Finset (Polynomial F)) (n : ℕ) :
    Finset (Polynomial F) :=
  (monicLayer F n).filter fun f ↦ ∀ p ∈ S, ¬ p ∣ f

private theorem mem_primeExcludingLayer {S : Finset (Polynomial F)} {n : ℕ} {f : Polynomial F} :
    f ∈ primeExcludingLayer S n ↔ f.Monic ∧ f.natDegree = n ∧ ∀ p ∈ S, ¬ p ∣ f := by
  simp only [primeExcludingLayer, Finset.mem_filter, mem_monicLayer, and_assoc]

private theorem card_primeExcludingLayer_empty (n : ℕ) :
    (primeExcludingLayer (F := F) ∅ n).card = Fintype.card F ^ n := by
  simp [primeExcludingLayer, card_monicLayer]

private theorem card_primeExcludingLayer_insert (S : Finset (Polynomial F)) {p : Polynomial F}
    (hp : p.Monic) (hirr : Irreducible p) (hpS : p ∉ S)
    (hS : ∀ r ∈ S, r.Monic ∧ Irreducible r) {n : ℕ} (hn : p.natDegree ≤ n) :
    (primeExcludingLayer S n).card =
      (primeExcludingLayer (insert p S) n).card +
        (primeExcludingLayer S (n-p.natDegree)).card := by
  let A := primeExcludingLayer S n
  have hnot : A.filter (fun f ↦ ¬ p ∣ f) = primeExcludingLayer (insert p S) n := by
    ext f
    simp only [A, Finset.mem_filter, mem_primeExcludingLayer, Finset.forall_mem_insert]
    tauto
  have hdiv : (primeExcludingLayer S (n-p.natDegree)).card = (A.filter fun f ↦ p ∣ f).card := by
    apply Finset.card_bij (fun f _ ↦ p*f)
    · intro f hf
      obtain ⟨hfm, hfd, hav⟩ := mem_primeExcludingLayer.mp hf
      refine Finset.mem_filter.mpr ⟨mem_primeExcludingLayer.mpr ⟨hp.mul hfm, ?_, ?_⟩, dvd_mul_right p f⟩
      · rw [natDegree_mul hp.ne_zero hfm.ne_zero, hfd, Nat.add_sub_of_le hn]
      · intro r hr hrd
        obtain ⟨hrm, hri⟩ := hS r hr
        rcases hri.prime.dvd_mul.mp hrd with hrp | hrf
        · exact hpS (eq_of_monic_of_associated hrm hp (hri.associated_of_dvd hirr hrp) ▸ hr)
        · exact hav r hr hrf
    · intro f _ g _ h
      exact mul_left_cancel₀ hp.ne_zero h
    · intro f hf
      obtain ⟨hfA, g, rfl⟩ := Finset.mem_filter.mp hf
      obtain ⟨hfm, hfd, hav⟩ := mem_primeExcludingLayer.mp hfA
      have hgm := hp.of_mul_monic_left hfm
      refine ⟨g, mem_primeExcludingLayer.mpr ⟨hgm, ?_, ?_⟩, rfl⟩
      · rw [natDegree_mul hp.ne_zero hgm.ne_zero] at hfd
        omega
      · exact fun r hr hrg ↦ hav r hr (dvd_mul_of_dvd_right hrg p)
  rw [hdiv, ← hnot, add_comm, Finset.card_filter_add_card_filter_not]

private theorem normalized_primeExcludingLayer (S : Finset (Polynomial F))
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) {n : ℕ}
    (hn : ∑ p ∈ S, p.natDegree ≤ n) :
    ((primeExcludingLayer S n).card : ℝ) / (Fintype.card F : ℝ)^n =
      ∏ p ∈ S, (1 - (Fintype.card F : ℝ)⁻¹ ^ p.natDegree) := by
  let q := (Fintype.card F : ℝ)
  have hq : 0 < q := by
    change 0 < (Fintype.card F : ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  induction S using Finset.induction_on generalizing n with
  | empty =>
    rw [card_primeExcludingLayer_empty, Nat.cast_pow, Finset.prod_empty, div_self (pow_ne_zero _ hq.ne')]
  | @insert p S hpS ih =>
    obtain ⟨hp, hi⟩ := hS p (Finset.mem_insert_self _ _)
    have hS' := fun r hr ↦ hS r (Finset.mem_insert_of_mem hr)
    rw [Finset.sum_insert hpS] at hn
    have hpn : p.natDegree ≤ n := by omega
    have h₁ := ih hS' (n := n) (by omega)
    have h₂ := ih hS' (n := n-p.natDegree) (by omega)
    have hc : ((primeExcludingLayer S n).card : ℝ) =
        ((primeExcludingLayer (insert p S) n).card : ℝ) +
          ((primeExcludingLayer S (n-p.natDegree)).card : ℝ) := by
      exact_mod_cast card_primeExcludingLayer_insert S hp hi hpS hS' hpn
    rw [Finset.prod_insert hpS]
    calc
      _ = ((primeExcludingLayer S n).card : ℝ) / q^n -
          ((primeExcludingLayer S (n-p.natDegree)).card : ℝ) / q^n := by
        rw [← sub_div, hc, add_sub_cancel_right]
      _ = ((primeExcludingLayer S n).card : ℝ) / q^n -
          ((primeExcludingLayer S (n-p.natDegree)).card : ℝ) / q^(n-p.natDegree) * q⁻¹^p.natDegree := by
        have hsplit : q^n = q^(n-p.natDegree) * q^p.natDegree := by
          rw [← pow_add, Nat.sub_add_cancel hpn]
        have hshift : ((primeExcludingLayer S (n-p.natDegree)).card : ℝ) / q^n =
            ((primeExcludingLayer S (n-p.natDegree)).card : ℝ) / q^(n-p.natDegree) * q⁻¹^p.natDegree := by
          rw [hsplit, div_mul_eq_div_div, inv_pow]
          rfl
        rw [hshift]
      _ = _ := by
        change ((primeExcludingLayer S n).card : ℝ) / (Fintype.card F : ℝ)^n -
            ((primeExcludingLayer S (n-p.natDegree)).card : ℝ) / (Fintype.card F : ℝ)^(n-p.natDegree) *
              (Fintype.card F : ℝ)⁻¹^p.natDegree = _
        rw [h₁, h₂]
        ring

/-- All monic degree-`n` polynomials with no irreducible factor of degree at most `T`. -/
noncomputable def polynomialRoughLayer (F : Type*) [Field F] [Fintype F] (T n : ℕ) :
    Finset (Polynomial F) :=
  primeExcludingLayer (polynomialSmoothPrimes F T) n

theorem mem_polynomialRoughLayer {T n : ℕ} {f : Polynomial F} :
    f ∈ polynomialRoughLayer F T n ↔
      f.Monic ∧ f.natDegree = n ∧ ∀ p ∈ normalizedFactors f, T < p.natDegree := by
  rw [polynomialRoughLayer, mem_primeExcludingLayer]
  refine and_congr_right fun hm ↦ and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · intro hf p hp
    obtain ⟨hi, hpm, hpd⟩ := (Polynomial.mem_normalizedFactors_iff hm.ne_zero).mp hp
    exact lt_of_not_ge fun hdeg ↦ hf p (mem_polynomialSmoothPrimes.mpr ⟨hpm, hi, hdeg⟩) hpd
  · intro hf p hp hpd
    obtain ⟨hpm, hi, hdeg⟩ := mem_polynomialSmoothPrimes.mp hp
    exact (not_lt_of_ge hdeg) (hf p ((Polynomial.mem_normalizedFactors_iff hm.ne_zero).mpr
      ⟨hi, hpm, hpd⟩))

theorem polynomialRoughLayer_card_le_pow (T n : ℕ) :
    (polynomialRoughLayer F T n).card ≤ Fintype.card F ^ n := by
  rw [← card_primeExcludingLayer_empty (F := F)]
  exact Finset.card_le_card fun f hf ↦ mem_primeExcludingLayer.mpr
    ⟨(mem_polynomialRoughLayer.mp hf).1, (mem_polynomialRoughLayer.mp hf).2.1, by simp⟩

/-- The normalized rough count is exactly the local product once there is enough
room for every excluded prime in the degree budget. -/
theorem polynomialRoughLayer_card_div_pow_of_le (T : ℕ) {n : ℕ}
    (hn : ∑ p ∈ polynomialSmoothPrimes F T, p.natDegree ≤ n) :
    ((polynomialRoughLayer F T n).card : ℝ) / (Fintype.card F : ℝ)^n =
      ∏ p ∈ polynomialSmoothPrimes F T, (1 - (Fintype.card F : ℝ)⁻¹^p.natDegree) :=
  normalized_primeExcludingLayer _ (fun _ hp ↦
    ⟨(mem_polynomialSmoothPrimes.mp hp).1, (mem_polynomialSmoothPrimes.mp hp).2.1⟩) hn

/-- The Euler limit of the unrestricted rough layers used in the upper bound. -/
theorem tendsto_polynomialRoughLayer_card_div_pow (T : ℕ) :
    Tendsto (fun n ↦ ((polynomialRoughLayer F T n).card : ℝ) /
      (Fintype.card F : ℝ)^n) atTop
      (𝓝 (∏ p ∈ polynomialSmoothPrimes F T, (1 - (Fintype.card F : ℝ)⁻¹^p.natDegree))) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (∑ p ∈ polynomialSmoothPrimes F T, p.natDegree)] with n hn
  exact (polynomialRoughLayer_card_div_pow_of_le T hn).symm

end GRHArticle.ProgressionFree
