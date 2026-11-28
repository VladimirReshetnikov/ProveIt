import GRHArticle.ProgressionFree.PolynomialOneFreePrimeFibers

/-!
# Counting greedy monic cofactors by the low ternary digit

Every greedy cofactor splits uniquely as a squarefree factor times the
cube of another greedy cofactor. Both factors avoid the same excluded
primes. The degree identity gives an exact finite convolution.
-/

namespace GRHArticle.ProgressionFree

open Polynomial UniqueFactorizationMonoid
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F]

/-- The monic greedy degree layer after excluding a finite set of primes. -/
noncomputable def greedyPrimeAvoidingLayer (S : Finset F[X]) (n : ℕ) : Finset F[X] :=
  (monicLayer F n).filter fun f ↦ (∀ p ∈ S, ¬p ∣ f) ∧
    ∀ p, polynomialPrimeExponent p f ∈ greedyExponents

theorem mem_greedyPrimeAvoidingLayer {S : Finset F[X]} {n : ℕ} {f : F[X]} :
    f ∈ greedyPrimeAvoidingLayer S n ↔ f.Monic ∧ f.natDegree = n ∧
      (∀ p ∈ S, ¬p ∣ f) ∧ (∀ p, polynomialPrimeExponent p f ∈ greedyExponents) := by
  simp [greedyPrimeAvoidingLayer, mem_monicLayer, and_assoc]

theorem greedyPrimeAvoidingLayer_singleton (P : F[X]) (n : ℕ) :
    greedyPrimeAvoidingLayer {P} n = oneFreePrimeCofactorLayer P n := by
  ext f
  simp [mem_greedyPrimeAvoidingLayer, mem_oneFreePrimeCofactorLayer,
    OneFreePrimeAdmissibleCofactor, and_left_comm]

theorem card_greedyPrimeAvoidingLayer_le (S : Finset F[X]) (n : ℕ) :
    (greedyPrimeAvoidingLayer S n).card ≤ Fintype.card F ^ n := by
  rw [← card_monicLayer (F := F)]
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem card_greedyPrimeAvoidingLayer_zero (S : Finset F[X])
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) : (greedyPrimeAvoidingLayer S 0).card = 1 := by
  apply le_antisymm
  · simpa using card_greedyPrimeAvoidingLayer_le S 0
  · have h : (1 : F[X]) ∈ greedyPrimeAvoidingLayer S 0 := by
      refine mem_greedyPrimeAvoidingLayer.mpr ⟨monic_one, natDegree_one, ?_, ?_⟩
      · intro p hp hd
        exact (hS p hp).2.not_isUnit (isUnit_of_dvd_one hd)
      · intro p
        simpa [polynomialPrimeExponent] using zero_mem_greedyExponents
    exact Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨1,h⟩)

omit [Fintype F] in
private theorem normalizedFactors_prod_monic {f : F[X]} (h : f.Monic) :
    (normalizedFactors f).prod = f := by
  simpa only [h.leadingCoeff, C_1, one_mul] using leadingCoeff_mul_prod_normalizedFactors f

omit [Fintype F] in
private theorem monic_normalizedFactors_prod (s : Multiset F[X])
    (h : ∀ p ∈ s, p.Monic ∧ Irreducible p) :
    s.prod.Monic ∧ normalizedFactors s.prod = s := by
  constructor
  · simpa only [Multiset.map_id] using monic_multiset_prod_of_monic s id
      (fun p hp ↦ (h p hp).1)
  · rw [normalizedFactors_prod_eq s (fun p hp ↦ (h p hp).2)]
    rw [Multiset.map_congr (s := s) rfl (f := normalize) (g := id)
      (fun p hp ↦ (normalize_eq_self_iff_monic (h p hp).2.ne_zero).mpr (h p hp).1),
      Multiset.map_id]

private noncomputable def transformCounts {α : Type*} [DecidableEq α] (s : Multiset α) (w : ℕ → ℕ) : Multiset α :=
  ∑ p ∈ s.toFinset, Multiset.replicate (w (s.count p)) p

private theorem count_transformCounts {α : Type*} [DecidableEq α] (s : Multiset α) (w : ℕ → ℕ)
    (hw : w 0 = 0) (p : α) :
    (transformCounts s w).count p = w (s.count p) := by
  unfold transformCounts
  rw [Multiset.count_sum']
  by_cases hmem : p ∈ s.toFinset
  · rw [Finset.sum_eq_single_of_mem p hmem]
    · exact Multiset.count_replicate_self _ _
    · intro q _ hqp
      simp [Multiset.count_replicate, hqp]
  · have hz : s.count p = 0 := Multiset.count_eq_zero.mpr
      (fun h ↦ hmem (Multiset.mem_toFinset.mpr h))
    rw [hz, hw]
    apply Finset.sum_eq_zero
    intro q hq
    have hqp : q ≠ p := fun h ↦ hmem (h ▸ hq)
    simp [Multiset.count_replicate, hqp]

private theorem mem_of_mem_transformCounts {α : Type*} [DecidableEq α] {s : Multiset α} {w : ℕ → ℕ}
    (hw : w 0 = 0) {p : α} (hp : p ∈ transformCounts s w) : p ∈ s := by
  by_contra h
  have hz := Multiset.count_eq_zero.mpr h
  exact (Multiset.count_ne_zero.mpr hp) ((count_transformCounts s w hw p).trans (hz ▸ hw))

omit [Fintype F] in
private theorem exists_greedy_squarefree_cube (S : Finset F[X]) {f : F[X]}
    (hf : f.Monic) (havoid : ∀ p ∈ S, ¬p ∣ f)
    (hgreedy : ∀ p, polynomialPrimeExponent p f ∈ greedyExponents) :
    ∃ g h : F[X], g.Monic ∧ h.Monic ∧ Squarefree g ∧
      (∀ p ∈ S, ¬p ∣ g) ∧ (∀ p ∈ S, ¬p ∣ h) ∧
      (∀ p, polynomialPrimeExponent p h ∈ greedyExponents) ∧ g*h^3 = f := by
  let s := normalizedFactors f
  let b := transformCounts s (· % 3)
  let c := transformCounts s (· / 3)
  have hfact (p : F[X]) (hp : p ∈ s) : p.Monic ∧ Irreducible p := by
    obtain ⟨hi, hm, _⟩ := (Polynomial.mem_normalizedFactors_iff hf.ne_zero).mp hp
    exact ⟨hm, hi⟩
  have hb := monic_normalizedFactors_prod b (fun p hp ↦ hfact p (mem_of_mem_transformCounts rfl hp))
  have hc := monic_normalizedFactors_prod c (fun p hp ↦ hfact p (mem_of_mem_transformCounts rfl hp))
  have hcb (p : F[X]) : b.count p = s.count p % 3 := count_transformCounts s _ rfl p
  have hcc (p : F[X]) : c.count p = s.count p / 3 := count_transformCounts s _ rfl p
  have hmod (p : F[X]) := (mem_greedyExponents_iff (s.count p)).mp (hgreedy p)
  have hsum : b + 3 • c = s := by
    apply Multiset.ext.mpr
    intro p
    simp only [Multiset.count_add, Multiset.count_nsmul, hcb, hcc]
    omega
  have he : b.prod*c.prod^3 = f := by
    rw [← Multiset.prod_nsmul, ← Multiset.prod_add, hsum, normalizedFactors_prod_monic hf]
  have hav₁ (p : F[X]) (hp : p ∈ S) : ¬p ∣ b.prod := by
    intro h
    exact havoid p hp (he ▸ dvd_mul_of_dvd_left h _)
  have hav₂ (p : F[X]) (hp : p ∈ S) : ¬p ∣ c.prod := by
    intro h
    exact havoid p hp (he ▸ dvd_mul_of_dvd_right (h.trans (dvd_pow_self _ (by decide : 3 ≠ 0))) _)
  refine ⟨b.prod,c.prod,hb.1,hc.1,?_,hav₁,hav₂,?_,he⟩
  · rw [squarefree_iff_nodup_normalizedFactors hb.1.ne_zero, hb.2, Multiset.nodup_iff_count_le_one]
    intro p
    rw [hcb]
    exact (hmod p).1
  · intro p
    rw [polynomialPrimeExponent, hc.2, hcc]
    exact (hmod p).2

omit [Fintype F] in
private theorem greedy_squarefree_cube_mem (S : Finset F[X])
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) {g h : F[X]}
    (hg : g.Monic) (hh : h.Monic) (hs : Squarefree g)
    (havoidg : ∀ p ∈ S, ¬p ∣ g) (havoidh : ∀ p ∈ S, ¬p ∣ h)
    (hgreedyh : ∀ p, polynomialPrimeExponent p h ∈ greedyExponents) :
    (∀ p ∈ S, ¬p ∣ g*h^3) ∧ (∀ p, polynomialPrimeExponent p (g*h^3) ∈ greedyExponents) := by
  constructor
  · intro p hp h
    have hprime := (hS p hp).2.prime
    rcases hprime.dvd_mul.mp h with h | h
    · exact havoidg p hp h
    · exact havoidh p hp (hprime.dvd_of_dvd_pow h)
  · intro p
    have hx : polynomialPrimeExponent p g ≤ 1 :=
      Multiset.nodup_iff_count_le_one.mp
        ((squarefree_iff_nodup_normalizedFactors hg.ne_zero).mp hs) p
    have he : polynomialPrimeExponent p (g*h^3) =
        polynomialPrimeExponent p g + 3 * polynomialPrimeExponent p h := by
      rw [polynomialPrimeExponent_mul p hg.ne_zero (pow_ne_zero _ hh.ne_zero)]
      simp [polynomialPrimeExponent, normalizedFactors_pow, Multiset.count_nsmul]
    rw [he, mem_greedyExponents_iff]
    have hm : (polynomialPrimeExponent p g + 3 * polynomialPrimeExponent p h) % 3 =
        polynomialPrimeExponent p g := by omega
    have hd : (polynomialPrimeExponent p g + 3 * polynomialPrimeExponent p h) / 3 =
        polynomialPrimeExponent p h := by omega
    rw [hm, hd]
    exact ⟨hx, hgreedyh p⟩

omit [Fintype F] in
private theorem squarefree_cube_injective {g h g' h' : F[X]}
    (hg : g.Monic) (hh : h.Monic) (hg' : g'.Monic) (hh' : h'.Monic)
    (hs : Squarefree g) (hs' : Squarefree g')
    (he : g*h^3 = g'*h'^3) : g = g' ∧ h = h' := by
  have heq := congrArg normalizedFactors he
  rw [normalizedFactors_mul hg.ne_zero (pow_ne_zero _ hh.ne_zero),
    normalizedFactors_mul hg'.ne_zero (pow_ne_zero _ hh'.ne_zero),
    normalizedFactors_pow, normalizedFactors_pow] at heq
  have hcount (p : F[X]) :
      (normalizedFactors g).count p = (normalizedFactors g').count p ∧
        (normalizedFactors h).count p = (normalizedFactors h').count p := by
    have hc := congrArg (Multiset.count p) heq
    simp only [Multiset.count_add, Multiset.count_nsmul] at hc
    have h₀ := Multiset.nodup_iff_count_le_one.mp
      ((squarefree_iff_nodup_normalizedFactors hg.ne_zero).mp hs) p
    have h₁ := Multiset.nodup_iff_count_le_one.mp
      ((squarefree_iff_nodup_normalizedFactors hg'.ne_zero).mp hs') p
    omega
  constructor
  · rw [← normalizedFactors_prod_monic hg, ← normalizedFactors_prod_monic hg']
    exact congrArg Multiset.prod (Multiset.ext.mpr fun p ↦ (hcount p).1)
  · rw [← normalizedFactors_prod_monic hh, ← normalizedFactors_prod_monic hh']
    exact congrArg Multiset.prod (Multiset.ext.mpr fun p ↦ (hcount p).2)

/-- Exact degree-by-degree convolution separating the low ternary digit. -/
theorem card_greedyPrimeAvoidingLayer (S : Finset F[X])
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) (n : ℕ) :
    (greedyPrimeAvoidingLayer S n).card =
      ∑ k ∈ Finset.range (n/3+1),
        (squarefreeLayer F S (n-3*k)).card * (greedyPrimeAvoidingLayer S k).card := by
  let D := (Finset.range (n/3+1)).sigma fun k ↦
    squarefreeLayer F S (n-3*k) ×ˢ greedyPrimeAvoidingLayer S k
  have hcard : D.card = (greedyPrimeAvoidingLayer S n).card := by
    apply Finset.card_bij (fun a _ ↦ a.2.1 * a.2.2^3)
    · rintro ⟨k,g,h⟩ hk
      obtain ⟨hk,hgh⟩ := Finset.mem_sigma.mp hk
      obtain ⟨hg,hh⟩ := Finset.mem_product.mp hgh
      obtain ⟨hgm,hgd,hgs,hga⟩ := mem_squarefreeLayer.mp hg
      obtain ⟨hhm,hhd,hha,hhg⟩ := mem_greedyPrimeAvoidingLayer.mp hh
      obtain ⟨havoid,hgreedy⟩ := greedy_squarefree_cube_mem S hS hgm hhm hgs hga hha hhg
      have hkn := Finset.mem_range.mp hk
      change k < n/3+1 at hkn
      refine mem_greedyPrimeAvoidingLayer.mpr ⟨hgm.mul (hhm.pow _), ?_, havoid, hgreedy⟩
      change g.natDegree = n-3*k at hgd
      change h.natDegree = k at hhd
      change (g*h^3).natDegree = n
      rw [natDegree_mul hgm.ne_zero (pow_ne_zero _ hhm.ne_zero), natDegree_pow, hgd, hhd]
      omega
    · rintro ⟨k,g,h⟩ hk ⟨k',g',h'⟩ hk' he
      obtain ⟨hg,hh⟩ := Finset.mem_product.mp (Finset.mem_sigma.mp hk).2
      obtain ⟨hg',hh'⟩ := Finset.mem_product.mp (Finset.mem_sigma.mp hk').2
      obtain ⟨hgm,_,hgs,_⟩ := mem_squarefreeLayer.mp hg
      obtain ⟨hgm',_,hgs',_⟩ := mem_squarefreeLayer.mp hg'
      obtain ⟨hhm,hhd,_,_⟩ := mem_greedyPrimeAvoidingLayer.mp hh
      obtain ⟨hhm',hhd',_,_⟩ := mem_greedyPrimeAvoidingLayer.mp hh'
      obtain ⟨rfl,rfl⟩ := squarefree_cube_injective hgm hhm hgm' hhm' hgs hgs' he
      have : k = k' := hhd.symm.trans hhd'
      subst k'
      rfl
    · intro f hf
      obtain ⟨hfm,hfd,hfa,hfg⟩ := mem_greedyPrimeAvoidingLayer.mp hf
      obtain ⟨g,h,hgm,hhm,hgs,hga,hha,hhg,hgh⟩ := exists_greedy_squarefree_cube S hfm hfa hfg
      have hdeg : g.natDegree + 3*h.natDegree = n := by
        have he := congrArg natDegree hgh
        rw [natDegree_mul hgm.ne_zero (pow_ne_zero _ hhm.ne_zero), natDegree_pow, hfd] at he
        omega
      refine ⟨⟨h.natDegree,g,h⟩, Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr ?_,
        Finset.mem_product.mpr ⟨mem_squarefreeLayer.mpr ⟨hgm,?_,hgs,hga⟩,
          mem_greedyPrimeAvoidingLayer.mpr ⟨hhm,rfl,hha,hhg⟩⟩⟩, hgh⟩
      · change h.natDegree < n/3+1
        omega
      · change g.natDegree = n-3*h.natDegree
        omega
  simpa only [D, Finset.card_sigma, Finset.card_product] using hcard.symm

end GRHArticle.ProgressionFree
