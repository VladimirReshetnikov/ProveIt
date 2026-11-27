import GRHArticle.ProgressionFree.PolynomialPrimeExclusion
import GRHArticle.ProgressionFree.PolynomialReplacementCount

/-!
# Density of squarefree rough polynomials

Squarefree–square factorization gives the total squarefree count. Excluding
one monic irreducible gives a two-term coefficient recurrence, whose
normalized limit removes that prime's Euler factor.
-/

namespace GRHArticle.ProgressionFree

open Polynomial UniqueFactorizationMonoid Filter Topology
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F]

/-- All monic polynomials over the finite field of degree exactly `n`. -/
noncomputable def monicLayer (F : Type*) [Field F] [Fintype F] (n : ℕ) :
    Finset (Polynomial F) :=
  (polynomialDegreeLayer F n).filter Monic

theorem mem_monicLayer {n : ℕ} {f : Polynomial F} :
    f ∈ monicLayer F n ↔ f.Monic ∧ f.natDegree = n := by
  simp only [monicLayer, Finset.mem_filter, mem_polynomialDegreeLayer]
  exact ⟨fun ⟨⟨_, hd⟩, hm⟩ ↦ ⟨hm, hd⟩, fun ⟨hm, hd⟩ ↦ ⟨⟨hm.ne_zero, hd⟩, hm⟩⟩

theorem card_monicLayer (n : ℕ) :
    (monicLayer F n).card = Fintype.card F ^ n := by
  let e : ↥(monicLayer F n) ≃ (Fin n → F) :=
    (Equiv.subtypeEquivRight (fun _ ↦ mem_monicLayer)).trans
      ((monicEquivDegreeLT n).trans (degreeLTEquiv F n).toEquiv)
  simpa [Fintype.card_fun] using Fintype.card_congr e

private noncomputable def squarefreeLayer (F : Type*) [Field F] [Fintype F]
    (S : Finset (Polynomial F)) (n : ℕ) : Finset (Polynomial F) :=
  (monicLayer F n).filter fun f ↦ Squarefree f ∧ ∀ p ∈ S, ¬ p ∣ f

private theorem mem_squarefreeLayer {S : Finset (Polynomial F)} {n : ℕ} {f : Polynomial F} :
    f ∈ squarefreeLayer F S n ↔
      f.Monic ∧ f.natDegree = n ∧ Squarefree f ∧ ∀ p ∈ S, ¬ p ∣ f := by
  simp only [squarefreeLayer, Finset.mem_filter, mem_monicLayer, and_assoc]

private theorem exists_squarefree_multiset {α : Type*} (m : Multiset α) :
    ∃ s t, s.Nodup ∧ s + 2 • t = m := by
  induction m using Multiset.induction_on with
  | empty => exact ⟨0, 0, by simp, by simp⟩
  | cons a m ih =>
    obtain ⟨s, t, hs, rfl⟩ := ih
    by_cases ha : a ∈ s
    · exact ⟨s.erase a, a ::ₘ t, hs.erase a, by
        conv_rhs => rw [← Multiset.cons_erase ha]
        simp only [← Multiset.singleton_add, two_nsmul]
        ac_rfl⟩
    · exact ⟨a ::ₘ s, t, Multiset.nodup_cons.mpr ⟨ha, hs⟩, by
        rw [← Multiset.singleton_add, ← Multiset.singleton_add, add_assoc]⟩

section Factorization

omit [Fintype F]

private theorem normFactors_prod_monic (f : Polynomial F) (hf : f.Monic) :
    (normalizedFactors f).prod = f := by
  simpa only [hf.leadingCoeff, C_1, one_mul] using leadingCoeff_mul_prod_normalizedFactors f

private theorem monic_irreducible_prod (s : Multiset (Polynomial F))
    (h : ∀ p ∈ s, Irreducible p ∧ p.Monic) :
    s.prod.Monic ∧ normalizedFactors s.prod = s := by
  constructor
  · simpa only [Multiset.map_id] using monic_multiset_prod_of_monic s id (fun p hp ↦ (h p hp).2)
  · rw [normalizedFactors_prod_eq s (fun p hp ↦ (h p hp).1)]
    rw [Multiset.map_congr rfl (f := normalize) (g := id)
      (fun p hp ↦ (normalize_eq_self_iff_monic (h p hp).1.ne_zero).mpr (h p hp).2), Multiset.map_id]

private theorem exists_squarefree_square {f : Polynomial F} (hf : f.Monic) :
    ∃ g h : Polynomial F, g.Monic ∧ h.Monic ∧ Squarefree g ∧ g * h ^ 2 = f := by
  obtain ⟨s, t, hs, hst⟩ := exists_squarefree_multiset (normalizedFactors f)
  have hfactors {p : Polynomial F} (hp : p ∈ normalizedFactors f) :
      Irreducible p ∧ p.Monic := by
    obtain ⟨hirr, hm, _⟩ := (Polynomial.mem_normalizedFactors_iff hf.ne_zero).mp hp
    exact ⟨hirr, hm⟩
  have hs' := monic_irreducible_prod s (fun p hp ↦
    hfactors (hst ▸ Multiset.mem_add.mpr (Or.inl hp)))
  have ht' := monic_irreducible_prod t (fun p hp ↦ by
    apply hfactors
    rw [← hst, two_nsmul, Multiset.mem_add, Multiset.mem_add]
    exact Or.inr (Or.inl hp))
  refine ⟨s.prod, t.prod, hs'.1, ht'.1, ?_, ?_⟩
  · rwa [squarefree_iff_nodup_normalizedFactors hs'.1.ne_zero, hs'.2]
  · rw [← Multiset.prod_nsmul, ← Multiset.prod_add, hst, normFactors_prod_monic f hf]

private theorem squarefree_square_injective {g h g' h' : Polynomial F}
    (hg : g.Monic) (hh : h.Monic) (hg' : g'.Monic) (hh' : h'.Monic)
    (hs : Squarefree g) (hs' : Squarefree g')
    (he : g * h ^ 2 = g' * h' ^ 2) : g = g' ∧ h = h' := by
  have heq := congrArg normalizedFactors he
  rw [normalizedFactors_mul hg.ne_zero (pow_ne_zero _ hh.ne_zero),
    normalizedFactors_mul hg'.ne_zero (pow_ne_zero _ hh'.ne_zero),
    normalizedFactors_pow, normalizedFactors_pow] at heq
  have hn := (squarefree_iff_nodup_normalizedFactors hg.ne_zero).mp hs
  have hn' := (squarefree_iff_nodup_normalizedFactors hg'.ne_zero).mp hs'
  have hcount (p : Polynomial F) :
      (normalizedFactors g).count p = (normalizedFactors g').count p ∧
      (normalizedFactors h).count p = (normalizedFactors h').count p := by
    have hc := congrArg (Multiset.count p) heq
    simp only [Multiset.count_add, Multiset.count_nsmul] at hc
    have hp := Multiset.nodup_iff_count_le_one.mp hn p
    have hp' := Multiset.nodup_iff_count_le_one.mp hn' p
    omega
  exact ⟨(normFactors_prod_monic g hg).symm.trans
    ((congrArg Multiset.prod (Multiset.ext' fun p ↦ (hcount p).1)).trans
      (normFactors_prod_monic g' hg')),
    (normFactors_prod_monic h hh).symm.trans
    ((congrArg Multiset.prod (Multiset.ext' fun p ↦ (hcount p).2)).trans
      (normFactors_prod_monic h' hh'))⟩

end Factorization

theorem card_monicLayer_squarefree (n : ℕ) :
    Fintype.card F ^ n =
      ∑ k ∈ Finset.range (n / 2 + 1),
        (squarefreeLayer F ∅ (n - 2*k)).card * Fintype.card F ^ k := by
  let D := (Finset.range (n/2+1)).sigma fun k ↦
    squarefreeLayer F ∅ (n-2*k) ×ˢ monicLayer F k
  have hcard : D.card = (monicLayer F n).card := by
    apply Finset.card_bij (fun a _ ↦ a.2.1 * a.2.2 ^ 2)
    · rintro ⟨k, g, h⟩ hk
      obtain ⟨hk', hgh⟩ := Finset.mem_sigma.mp hk
      obtain ⟨hg, hh⟩ := Finset.mem_product.mp hgh
      obtain ⟨hgm, hgd, _, _⟩ := mem_squarefreeLayer.mp hg
      obtain ⟨hhm, hhd⟩ := mem_monicLayer.mp hh
      refine mem_monicLayer.mpr ⟨hgm.mul (hhm.pow 2), ?_⟩
      rw [natDegree_mul hgm.ne_zero (pow_ne_zero _ hhm.ne_zero), natDegree_pow, hgd, hhd]
      have := Finset.mem_range.mp hk'
      omega
    · rintro ⟨k, g, h⟩ hk ⟨k', g', h'⟩ hk' he
      obtain ⟨hg, hh⟩ := Finset.mem_product.mp (Finset.mem_sigma.mp hk).2
      obtain ⟨hg', hh'⟩ := Finset.mem_product.mp (Finset.mem_sigma.mp hk').2
      obtain ⟨hgm, _, hgs, _⟩ := mem_squarefreeLayer.mp hg
      obtain ⟨hgm', _, hgs', _⟩ := mem_squarefreeLayer.mp hg'
      obtain ⟨hhm, hhd⟩ := mem_monicLayer.mp hh
      obtain ⟨hhm', hhd'⟩ := mem_monicLayer.mp hh'
      obtain ⟨rfl, rfl⟩ := squarefree_square_injective hgm hhm hgm' hhm' hgs hgs' he
      have hkk : k = k' := hhd.symm.trans hhd'
      subst k'
      rfl
    · intro f hf
      obtain ⟨hfm, hfd⟩ := mem_monicLayer.mp hf
      obtain ⟨g, h, hgm, hhm, hgs, hgh⟩ := exists_squarefree_square hfm
      have hdeg : g.natDegree + 2*h.natDegree = n := by
        have he := congrArg natDegree hgh
        rwa [natDegree_mul hgm.ne_zero (pow_ne_zero _ hhm.ne_zero), natDegree_pow, hfd] at he
      refine ⟨⟨h.natDegree, g, h⟩, Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr ?_,
        Finset.mem_product.mpr ⟨mem_squarefreeLayer.mpr ⟨hgm, ?_, hgs, by simp⟩,
          mem_monicLayer.mpr ⟨hhm, rfl⟩⟩⟩, hgh⟩
      · change h.natDegree < n/2+1
        omega
      · change g.natDegree = n-2*h.natDegree
        omega
  simpa only [D, Finset.card_sigma, Finset.card_product, card_monicLayer] using hcard.symm

private theorem card_squarefreeLayer_empty_add_two (n : ℕ) :
    (squarefreeLayer F ∅ (n+2)).card + Fintype.card F ^ (n+1) = Fintype.card F ^ (n+2) := by
  have hh := card_monicLayer_squarefree (F := F) (n+2)
  rw [show (n+2)/2+1 = (n/2+1)+1 by omega, Finset.sum_range_succ'] at hh
  simp only [Nat.mul_zero, Nat.sub_zero, pow_zero, mul_one] at hh
  have hs : (∑ k ∈ Finset.range (n/2+1),
      (squarefreeLayer F ∅ (n+2-2*(k+1))).card * Fintype.card F ^ (k+1)) =
      Fintype.card F ^ (n+1) := by
    rw [pow_succ, card_monicLayer_squarefree (F := F) n, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [show n+2-2*(k+1) = n-2*k by omega, pow_succ, mul_assoc]
  rw [hs] at hh
  simpa only [add_comm (Fintype.card F ^ (n+1))] using hh.symm

private theorem card_squarefreeLayer_insert (S : Finset (Polynomial F)) {p : Polynomial F}
    (hp : p.Monic) (hirr : Irreducible p) (hpS : p ∉ S)
    (hS : ∀ r ∈ S, r.Monic ∧ Irreducible r) {n : ℕ} (hn : p.natDegree ≤ n) :
    (squarefreeLayer F S n).card =
      (squarefreeLayer F (insert p S) n).card +
      (squarefreeLayer F (insert p S) (n-p.natDegree)).card := by
  let A := squarefreeLayer F S n
  have hnot : A.filter (fun f ↦ ¬ p ∣ f) = squarefreeLayer F (insert p S) n := by
    ext f
    simp only [A, Finset.mem_filter, mem_squarefreeLayer, Finset.forall_mem_insert]
    tauto
  have hdiv : (squarefreeLayer F (insert p S) (n-p.natDegree)).card =
      (A.filter (fun f ↦ p ∣ f)).card := by
    apply Finset.card_bij (fun f _ ↦ p*f)
    · intro f hf
      obtain ⟨hfm, hfd, hfs, hav⟩ := mem_squarefreeLayer.mp hf
      have hfnot := hav p (Finset.mem_insert_self p S)
      refine Finset.mem_filter.mpr ⟨mem_squarefreeLayer.mpr ⟨hp.mul hfm, ?_,
        squarefree_mul_iff.mpr ⟨hirr.isRelPrime_iff_not_dvd.mpr hfnot, hirr.squarefree, hfs⟩,
        ?_⟩, dvd_mul_right p f⟩
      · rw [natDegree_mul hp.ne_zero hfm.ne_zero, hfd, Nat.add_sub_of_le hn]
      · intro r hr hrd
        obtain ⟨hrm, hri⟩ := hS r hr
        rcases hri.prime.dvd_mul.mp hrd with hrp | hrf
        · exact hpS (eq_of_monic_of_associated hrm hp (hri.associated_of_dvd hirr hrp) ▸ hr)
        · exact hav r (Finset.mem_insert_of_mem hr) hrf
    · intro f _ g _ h
      exact mul_left_cancel₀ hp.ne_zero h
    · intro f hf
      obtain ⟨hfA, g, rfl⟩ := Finset.mem_filter.mp hf
      obtain ⟨hfm, hfd, hfs, hav⟩ := mem_squarefreeLayer.mp hfA
      have hgm := hp.of_mul_monic_left hfm
      have hsq := squarefree_mul_iff.mp hfs
      refine ⟨g, mem_squarefreeLayer.mpr ⟨hgm, ?_, hsq.2.2, ?_⟩, rfl⟩
      · rw [natDegree_mul hp.ne_zero hgm.ne_zero] at hfd
        omega
      · intro r hr
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact hirr.isRelPrime_iff_not_dvd.mp hsq.1
        · exact fun hrg ↦ hav r hr (dvd_mul_of_dvd_right hrg p)
  rw [hdiv, ← hnot, add_comm, Finset.card_filter_add_card_filter_not]

private theorem tendsto_normalized_squarefreeLayer_empty :
    Tendsto (fun n ↦ ((squarefreeLayer F ∅ n).card : ℝ) / (Fintype.card F : ℝ)^n)
      atTop (𝓝 (1 - (Fintype.card F : ℝ)⁻¹)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k+2 := ⟨n-2, by omega⟩
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h := card_squarefreeLayer_empty_add_two (F := F) k
  have hr : ((squarefreeLayer F ∅ (k+2)).card : ℝ) + (Fintype.card F : ℝ)^(k+1) =
      (Fintype.card F : ℝ)^(k+2) := by exact_mod_cast h
  rw [show ((squarefreeLayer F ∅ (k+2)).card : ℝ) =
    (Fintype.card F : ℝ)^(k+2) - (Fintype.card F : ℝ)^(k+1) by linarith,
    pow_succ _ (k+1)]
  field_simp

private theorem tendsto_normalized_squarefreeLayer (S : Finset (Polynomial F))
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) :
    Tendsto (fun n ↦ ((squarefreeLayer F S n).card : ℝ) / (Fintype.card F : ℝ)^n)
      atTop (𝓝 ((1 - (Fintype.card F : ℝ)⁻¹) *
        ∏ p ∈ S, (1 + (Fintype.card F : ℝ)⁻¹ ^ p.natDegree)⁻¹)) := by
  induction S using Finset.induction_on with
  | empty => simpa using tendsto_normalized_squarefreeLayer_empty (F := F)
  | @insert p S hpS ih =>
    obtain ⟨hp, hirr⟩ := hS p (Finset.mem_insert_self p S)
    have hSm : ∀ r ∈ S, r.Monic ∧ Irreducible r :=
      fun r hr ↦ hS r (Finset.mem_insert_of_mem hr)
    have hd : 0 < p.natDegree := by
      by_contra! h
      exact hirr.not_isUnit ((hp.natDegree_eq_zero.mp (Nat.eq_zero_of_le_zero h)) ▸ isUnit_one)
    have hq : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
    have hq₀ : (0 : ℝ) < Fintype.card F := by linarith
    have hx₁ : (Fintype.card F : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
    rw [Finset.prod_insert hpS,
      mul_comm ((1 + (Fintype.card F : ℝ)⁻¹ ^ p.natDegree)⁻¹), ← mul_assoc]
    apply tendsto_of_prime_exclusion_recurrence
      (fun n ↦ ((squarefreeLayer F S n).card : ℝ) / (Fintype.card F : ℝ)^n)
      (fun n ↦ ((squarefreeLayer F (insert p S) n).card : ℝ) / (Fintype.card F : ℝ)^n)
      p.natDegree ((Fintype.card F : ℝ)⁻¹ ^ p.natDegree) _ hd (by positivity)
      (pow_lt_one₀ (by positivity) hx₁ hd.ne')
    · intro n
      refine ⟨by positivity, (div_le_iff₀ (pow_pos hq₀ _)).2 ?_⟩
      rw [one_mul, ← Nat.cast_pow, Nat.cast_le, ← card_monicLayer (F := F) n]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    · exact ih hSm
    · intro n hn
      have h := card_squarefreeLayer_insert S hp hirr hpS hSm hn
      rw [h, Nat.cast_add, add_div]
      congr 1
      have hpow : (Fintype.card F : ℝ)^n =
          (Fintype.card F : ℝ)^(n-p.natDegree) * (Fintype.card F : ℝ)^p.natDegree := by
        rw [← pow_add, Nat.sub_add_cancel hn]
      rw [hpow, inv_pow]
      field_simp

/-- The limiting normalized number of monic squarefree polynomials with no irreducible
factor of degree at most `L`. -/
noncomputable def polynomialRoughDensity (F : Type*) [Field F] [Fintype F] (L : ℕ) : ℝ :=
  (1 - (Fintype.card F : ℝ)⁻¹) *
    ∏ p ∈ polynomialSmoothPrimes F L, (1 + (Fintype.card F : ℝ)⁻¹ ^ p.natDegree)⁻¹

theorem polynomialRoughDensity_pos (F : Type*) [Field F] [Fintype F] (L : ℕ) :
    0 < polynomialRoughDensity F L := by
  have hq : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  unfold polynomialRoughDensity
  refine mul_pos (sub_pos.mpr (inv_lt_one_of_one_lt₀ hq)) (Finset.prod_pos ?_)
  intro p hp
  positivity

private theorem squarefreeRoughLayer_eq (L n : ℕ) :
    polynomialSquarefreeRoughLayer F L n = squarefreeLayer F (polynomialSmoothPrimes F L) n := by
  ext f
  rw [mem_polynomialSquarefreeRoughLayer, mem_squarefreeLayer]
  refine and_congr_right fun hm ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  constructor
  · intro hf p hp hpd
    obtain ⟨hpm, hpi, hdeg⟩ := mem_polynomialSmoothPrimes.mp hp
    exact (not_lt_of_ge hdeg) (hf p ((Polynomial.mem_normalizedFactors_iff hm.ne_zero).mpr
      ⟨hpi, hpm, hpd⟩))
  · intro hf p hp
    obtain ⟨hpi, hpm, hpd⟩ := (Polynomial.mem_normalizedFactors_iff hm.ne_zero).mp hp
    exact lt_of_not_ge fun hdeg ↦ hf p (mem_polynomialSmoothPrimes.mpr ⟨hpm, hpi, hdeg⟩) hpd

/-- The normalized squarefree rough count tends to the positive Euler coefficient
in the article. -/
theorem tendsto_polynomialSquarefreeRoughLayer_card_div_pow
    (F : Type*) [Field F] [Fintype F] (L : ℕ) :
    Tendsto (fun n ↦ ((polynomialSquarefreeRoughLayer F L n).card : ℝ) /
      (Fintype.card F : ℝ)^n) atTop (𝓝 (polynomialRoughDensity F L)) := by
  simp only [squarefreeRoughLayer_eq, polynomialRoughDensity]
  exact tendsto_normalized_squarefreeLayer _ (fun p hp ↦
    ⟨(mem_polynomialSmoothPrimes.mp hp).1, (mem_polynomialSmoothPrimes.mp hp).2.1⟩)

end GRHArticle.ProgressionFree
