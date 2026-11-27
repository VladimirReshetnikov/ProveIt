import GRHArticle.ProgressionFree.PolynomialDensitySupremum
import GRHArticle.ProgressionFree.PolynomialSmoothCount

/-!
# Exact finite optimization over smooth polynomial balls

The search uses finite coefficient vectors with convolution for multiplication.
It enumerates the monic smooth vectors, then keeps exactly the subsets that
pass the bounded-ratio test.
-/

namespace GRHArticle.ProgressionFree

open Polynomial UniqueFactorizationMonoid
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

private abbrev Coefficients (F : Type*) (n : ℕ) := Fin n → F

private noncomputable def vectorPolynomial (n : ℕ) : Coefficients F n ↪ Polynomial F :=
  (degreeLTEquiv F n).symm.toEquiv.toEmbedding.trans
    (Function.Embedding.subtype fun f ↦ f ∈ degreeLT F n)

omit [Fintype F] [DecidableEq F] in
private theorem vectorPolynomial_degree_lt (v : Coefficients F n) :
    (vectorPolynomial n v).degree < n :=
  mem_degreeLT.mp ((degreeLTEquiv F n).symm v).property

omit [Fintype F] [DecidableEq F] in
private theorem exists_vectorPolynomial {p : Polynomial F} (hp : p.degree < n) :
    ∃ v, vectorPolynomial n v = p := by
  let P : degreeLT F n := ⟨p, mem_degreeLT.mpr hp⟩
  exact ⟨degreeLTEquiv F n P, congrArg Subtype.val ((degreeLTEquiv F n).symm_apply_apply P)⟩

private def vectorCoeff (v : Coefficients F n) (i : ℕ) : F :=
  if h : i < n then v ⟨i, h⟩ else 0

omit [Fintype F] [DecidableEq F] in
private theorem vectorPolynomial_coeff (v : Coefficients F n) (i : ℕ) :
    (vectorPolynomial n v).coeff i = vectorCoeff v i := by
  by_cases hi : i < n
  · rw [vectorCoeff, dif_pos hi]
    change degreeLTEquiv F n ((degreeLTEquiv F n).symm v) ⟨i, hi⟩ = _
    exact congrFun ((degreeLTEquiv F n).apply_symm_apply v) ⟨i, hi⟩
  · rw [vectorCoeff, dif_neg hi]
    exact coeff_eq_zero_of_degree_lt ((vectorPolynomial_degree_lt v).trans_le
      (Nat.cast_le.mpr (Nat.le_of_not_gt hi)))

private def vectorNatDegree (v : Coefficients F n) : ℕ :=
  (Finset.univ.filter fun i : Fin n ↦ v i ≠ 0).sup Fin.val

omit [Fintype F] in
private theorem vectorPolynomial_natDegree (v : Coefficients F n) :
    (vectorPolynomial n v).natDegree = vectorNatDegree v := by
  apply le_antisymm
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [vectorPolynomial_coeff, vectorCoeff]
    split
    · rename_i hin
      by_contra hne
      exact (not_le_of_gt hi) (Finset.le_sup (f := Fin.val)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ (⟨i, hin⟩ : Fin n), hne⟩))
    · rfl
  · apply Finset.sup_le
    intro i hi
    apply le_natDegree_of_ne_zero
    rw [vectorPolynomial_coeff, vectorCoeff, dif_pos i.is_lt]
    exact (Finset.mem_filter.mp hi).2

private abbrev vectorMonic (v : Coefficients F n) : Prop :=
  vectorCoeff v (vectorNatDegree v) = 1

omit [Fintype F] in
private theorem vectorMonic_iff (v : Coefficients F n) :
    vectorMonic v ↔ (vectorPolynomial n v).Monic := by
  change _ ↔ (vectorPolynomial n v).leadingCoeff = 1
  rw [leadingCoeff, vectorPolynomial_natDegree, vectorPolynomial_coeff]

private def vectorProductCoeff (u v : Coefficients F n) (i : ℕ) : F :=
  ∑ j ∈ Finset.range (i + 1), vectorCoeff u j * vectorCoeff v (i-j)

private abbrev vectorProductEq (u v w : Coefficients F n) : Prop :=
  ∀ i ∈ Finset.range (2*n), vectorProductCoeff u v i = vectorCoeff w i

omit [Fintype F] [DecidableEq F] in
private theorem vectorProductEq_iff (u v w : Coefficients F n) :
    vectorProductEq u v w ↔ vectorPolynomial n u * vectorPolynomial n v = vectorPolynomial n w := by
  have hcoeff (i : ℕ) : (vectorPolynomial n u * vectorPolynomial n v).coeff i =
      vectorProductCoeff u v i := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [vectorPolynomial_coeff, vectorProductCoeff]
  constructor
  · intro h
    apply Polynomial.ext
    intro i
    rw [hcoeff, vectorPolynomial_coeff]
    by_cases hi : i < 2*n
    · exact h i (Finset.mem_range.mpr hi)
    · rw [show vectorCoeff w i = 0 by exact dif_neg (by omega)]
      apply Finset.sum_eq_zero
      intro j hj
      have hj' := Finset.mem_range.mp hj
      by_cases hjn : j < n
      · rw [show vectorCoeff v (i-j) = 0 by exact dif_neg (by omega), mul_zero]
      · rw [show vectorCoeff u j = 0 by exact dif_neg hjn, zero_mul]
  · intro h i _
    rw [← hcoeff, h, vectorPolynomial_coeff]

private abbrev vectorPrime (v : Coefficients F n) : Prop :=
  vectorMonic v ∧ 0 < vectorNatDegree v ∧
    ∀ a ∈ (Finset.univ : Finset (Coefficients F n)), ∀ b ∈ (Finset.univ : Finset (Coefficients F n)),
      vectorMonic a → vectorMonic b → 0 < vectorNatDegree a → 0 < vectorNatDegree b →
        ¬ vectorProductEq a b v

private theorem vectorPrime_iff (v : Coefficients F (n+1)) :
    vectorPrime v ↔ (vectorPolynomial (n+1) v).Monic ∧ Irreducible (vectorPolynomial (n+1) v) := by
  let p := vectorPolynomial (n+1) v
  constructor
  · rintro ⟨hm, hd, hsearch⟩
    have hm' : p.Monic := (vectorMonic_iff v).mp hm
    refine ⟨hm', (hm'.irreducible_iff_natDegree).mpr ⟨?_, ?_⟩⟩
    · intro hp
      have hd' : 0 < p.natDegree := (vectorPolynomial_natDegree v).symm ▸ hd
      simp [hp] at hd'
    · intro f g hf hg hprod
      have hpdeg := vectorPolynomial_degree_lt v
      rw [degree_eq_natDegree hm'.ne_zero, Nat.cast_lt] at hpdeg
      have hdeg : f.natDegree + g.natDegree = p.natDegree := by
        rw [← hprod, natDegree_mul hf.ne_zero hg.ne_zero]
      have hfd : f.degree < (n+1 : ℕ) := by
        rw [degree_eq_natDegree hf.ne_zero, Nat.cast_lt]
        omega
      have hgd : g.degree < (n+1 : ℕ) := by
        rw [degree_eq_natDegree hg.ne_zero, Nat.cast_lt]
        omega
      obtain ⟨a, rfl⟩ := exists_vectorPolynomial hfd
      obtain ⟨b, rfl⟩ := exists_vectorPolynomial hgd
      rw [vectorPolynomial_natDegree, vectorPolynomial_natDegree]
      by_contra! hp
      exact hsearch a (Finset.mem_univ _) b (Finset.mem_univ _)
        ((vectorMonic_iff a).mpr hf) ((vectorMonic_iff b).mpr hg)
        (Nat.pos_of_ne_zero hp.1) (Nat.pos_of_ne_zero hp.2) ((vectorProductEq_iff a b v).mpr hprod)
  · rintro ⟨hm, hi⟩
    refine ⟨(vectorMonic_iff v).mpr hm, (vectorPolynomial_natDegree v) ▸ hi.natDegree_pos, ?_⟩
    intro a _ b _ ha hb hda hdb hprod
    have ht := ((hm.irreducible_iff_natDegree).mp hi).2 _ _
      ((vectorMonic_iff a).mp ha) ((vectorMonic_iff b).mp hb) ((vectorProductEq_iff a b v).mp hprod)
    rw [vectorPolynomial_natDegree, vectorPolynomial_natDegree] at ht
    exact ht.elim (Nat.ne_of_gt hda) (Nat.ne_of_gt hdb)

private def vectorPrimeTest (v : Coefficients F n) : Bool :=
  decide (vectorPrime v)

private theorem vectorPrimeTest_eq_true_iff (v : Coefficients F n) :
    vectorPrimeTest v = true ↔ vectorPrime v := by simp [vectorPrimeTest]

private def vectorDividesTest (p v : Coefficients F n) : Bool :=
  decide (((Finset.univ : Finset (Coefficients F n)).filter fun q ↦ vectorProductEq p q v).Nonempty)

private theorem vectorDividesTest_eq_true_iff (p v : Coefficients F n) :
    vectorDividesTest p v = true ↔ ∃ q, vectorProductEq p q v := by
  simp [vectorDividesTest, Finset.Nonempty]

private def smoothVectors (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (T t : ℕ) : Finset (Coefficients F (t+1)) :=
  Finset.univ.filter fun v ↦ vectorMonic v ∧
    ∀ p ∈ (Finset.univ : Finset (Coefficients F (t+1))), vectorPrimeTest p = true →
      vectorDividesTest p v = true →
        vectorNatDegree p ≤ T

private theorem mem_smoothVectors {T t : ℕ} {v : Coefficients F (t+1)} :
    v ∈ smoothVectors F T t ↔
      (vectorPolynomial (t+1) v).Monic ∧
        ∀ p ∈ normalizedFactors (vectorPolynomial (t+1) v), p.natDegree ≤ T := by
  let f := vectorPolynomial (t+1) v
  simp only [smoothVectors, Finset.mem_filter, Finset.mem_univ, true_and, vectorMonic_iff,
    vectorDividesTest_eq_true_iff, vectorPrimeTest_eq_true_iff, true_implies]
  constructor
  · rintro ⟨hm, h⟩
    refine ⟨hm, ?_⟩
    intro p hp
    have hi := irreducible_of_normalized_factor p hp
    have hpm := (normalize_eq_self_iff_monic hi.ne_zero).mp (normalize_normalized_factor p hp)
    obtain ⟨q, heq⟩ := dvd_of_mem_normalizedFactors hp
    change f = p * q at heq
    have hq₀ : q ≠ 0 := by rintro rfl; exact hm.ne_zero (by simpa using heq)
    have hfd := vectorPolynomial_degree_lt v
    rw [degree_eq_natDegree hm.ne_zero, Nat.cast_lt] at hfd
    have hdeg : f.natDegree = p.natDegree + q.natDegree := by
      rw [heq, natDegree_mul hpm.ne_zero hq₀]
    change f.natDegree < t+1 at hfd
    have hpd : p.degree < (t+1 : ℕ) := by
      rw [degree_eq_natDegree hpm.ne_zero, Nat.cast_lt]
      omega
    have hqd : q.degree < (t+1 : ℕ) := by
      rw [degree_eq_natDegree hq₀, Nat.cast_lt]
      omega
    obtain ⟨a, rfl⟩ := exists_vectorPolynomial hpd
    obtain ⟨b, rfl⟩ := exists_vectorPolynomial hqd
    rw [vectorPolynomial_natDegree]
    exact h a ((vectorPrime_iff a).mpr ⟨hpm, hi⟩) ⟨b, (vectorProductEq_iff a b v).mpr heq.symm⟩
  · rintro ⟨hm, h⟩
    refine ⟨hm, ?_⟩
    rintro a ha ⟨b, hb⟩
    obtain ⟨ham, hai⟩ := (vectorPrime_iff a).mp ha
    rw [← vectorPolynomial_natDegree]
    exact h _ ((mem_normalizedFactors_iff' hm.ne_zero).mpr
      ⟨hai, (normalize_eq_self_iff_monic ham.ne_zero).mpr ham,
        ⟨_, ((vectorProductEq_iff a b v).mp hb).symm⟩⟩)

/-- The finite ball of monic polynomials whose irreducible factors have degree at most `T`. -/
noncomputable def polynomialSmoothBall (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (T t : ℕ) : Finset (Polynomial F) :=
  (smoothVectors F T t).map (vectorPolynomial (t+1))

theorem mem_polynomialSmoothBall {T t : ℕ} {f : Polynomial F} :
    f ∈ polynomialSmoothBall F T t ↔
      f.Monic ∧ f.natDegree ≤ t ∧ ∀ p ∈ normalizedFactors f, p.natDegree ≤ T := by
  rw [polynomialSmoothBall, Finset.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨hm, hs⟩ := mem_smoothVectors.mp hv
    have hd := vectorPolynomial_degree_lt v
    rw [degree_eq_natDegree hm.ne_zero, Nat.cast_lt, Nat.lt_succ_iff] at hd
    exact ⟨hm, hd, hs⟩
  · rintro ⟨hm, hd, hs⟩
    have hdeg : f.degree < (t+1 : ℕ) := by
      rwa [degree_eq_natDegree hm.ne_zero, Nat.cast_lt, Nat.lt_succ_iff]
    obtain ⟨v, rfl⟩ := exists_vectorPolynomial hdeg
    exact ⟨v, mem_smoothVectors.mpr ⟨hm, hs⟩, rfl⟩

private def vectorRatioTest (B : Finset (Coefficients F n)) : Bool :=
  decide (∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, ∀ r ∈ (Finset.univ : Finset (Coefficients F n)),
    a ≠ 0 → 0 < vectorNatDegree r → ¬ (vectorProductEq a r b ∧ vectorProductEq b r c))

omit [Fintype F] [DecidableEq F] in
private theorem vectorPolynomial_zero : vectorPolynomial n (0 : Coefficients F n) = 0 :=
  congrArg Subtype.val ((degreeLTEquiv F n).symm.map_zero)

private theorem vectorRatioTest_eq_true_iff (B : Finset (Coefficients F n)) :
    vectorRatioTest B = true ↔
      PolynomialRatioThreeGPFree (B.map (vectorPolynomial n) : Set (Polynomial F)) := by
  rw [vectorRatioTest, decide_eq_true_eq]
  simp only [Finset.mem_univ, true_implies]
  constructor
  · intro h f r hf hr ⟨hfB, hfr, hfrr⟩
    have hr₀ : r ≠ 0 := by rintro rfl; simp at hr
    obtain ⟨a, ha, hae⟩ := Finset.mem_map.mp hfB
    obtain ⟨b, hb, hbe⟩ := Finset.mem_map.mp hfr
    obtain ⟨c, hc, hce⟩ := Finset.mem_map.mp hfrr
    have hd := vectorPolynomial_degree_lt b
    rw [hbe, degree_eq_natDegree (mul_ne_zero hf hr₀), Nat.cast_lt,
      natDegree_mul hf hr₀] at hd
    have hrd : r.degree < n := by
      rw [degree_eq_natDegree hr₀, Nat.cast_lt]
      omega
    obtain ⟨v, hv⟩ := exists_vectorPolynomial hrd
    refine h a ha b hb c hc v (fun haz ↦ hf ?_) ?_ ⟨?_, ?_⟩
    · rw [← hae, haz, vectorPolynomial_zero]
    · rwa [← vectorPolynomial_natDegree, hv]
    · apply (vectorProductEq_iff a v b).mpr
      rw [hae, hv, hbe]
    · apply (vectorProductEq_iff b v c).mpr
      rw [hbe, hv, hce]
  · intro h a ha b hb c hc r ha₀ hr ⟨hab, hbc⟩
    have ha₀' : vectorPolynomial n a ≠ 0 := by
      intro hzero
      exact ha₀ ((vectorPolynomial n).injective (hzero.trans vectorPolynomial_zero.symm))
    have hr' : 0 < (vectorPolynomial n r).natDegree := by rwa [vectorPolynomial_natDegree]
    have hma : vectorPolynomial n a ∈ B.map (vectorPolynomial n) := Finset.mem_map.mpr ⟨a, ha, rfl⟩
    have hmb : vectorPolynomial n b ∈ B.map (vectorPolynomial n) := Finset.mem_map.mpr ⟨b, hb, rfl⟩
    have hmc : vectorPolynomial n c ∈ B.map (vectorPolynomial n) := Finset.mem_map.mpr ⟨c, hc, rfl⟩
    exact h _ _ ha₀' hr' ⟨hma, ((vectorProductEq_iff a r b).mp hab).symm ▸ hmb,
      (by rwa [(vectorProductEq_iff a r b).mp hab, (vectorProductEq_iff b r c).mp hbc])⟩

/-- The exact `J_S(t)` for the cutoff primes, computed by finite exhaustive search. -/
def polynomialSmoothMaximum (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (T t : ℕ) : ℕ :=
  ((smoothVectors F T t).powerset.filter fun B ↦ vectorRatioTest B).sup Finset.card

/-- Every progression-free subset of the smooth ball has cardinal at most the computed optimum. -/
theorem le_polynomialSmoothMaximum {T t : ℕ} {B : Finset (Polynomial F)}
    (hB : B ⊆ polynomialSmoothBall F T t)
    (hfree : PolynomialRatioThreeGPFree (B : Set (Polynomial F))) :
    B.card ≤ polynomialSmoothMaximum F T t := by
  classical
  let v := vectorPolynomial (F := F) (t+1)
  let W := (smoothVectors F T t).filter fun a ↦ v a ∈ B
  have hmap : W.map v = B := by
    ext f
    constructor
    · intro hf
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hf
      exact (Finset.mem_filter.mp ha).2
    · intro hf
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp (hB hf)
      exact Finset.mem_map.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hf⟩, rfl⟩
  have hw : W ∈ (smoothVectors F T t).powerset.filter (fun E ↦ vectorRatioTest E) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
    exact (vectorRatioTest_eq_true_iff W).mpr (hmap.symm ▸ hfree)
  have heq : W.card = B.card := by rw [← hmap, Finset.card_map]
  rw [← heq]
  exact Finset.le_sup (f := Finset.card) hw

/-- A progression-free subset realizes the computed optimum. -/
theorem exists_polynomialSmoothMaximum (T t : ℕ) :
    ∃ B : Finset (Polynomial F), B ⊆ polynomialSmoothBall F T t ∧
      PolynomialRatioThreeGPFree (B : Set (Polynomial F)) ∧
      B.card = polynomialSmoothMaximum F T t := by
  let C := (smoothVectors F T t).powerset.filter fun B ↦ vectorRatioTest B
  have hne : C.Nonempty := ⟨∅, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by rw [vectorRatioTest, decide_eq_true_eq]; simp⟩⟩
  obtain ⟨A, hA, heq⟩ := Finset.exists_mem_eq_sup C hne Finset.card
  refine ⟨A.map (vectorPolynomial (t+1)), ?_,
    (vectorRatioTest_eq_true_iff A).mp (Finset.mem_filter.mp hA).2, ?_⟩
  · exact Finset.map_subset_map.mpr (Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1)
  · rw [Finset.card_map, ← heq]
    rfl

/-- The optimal size is bounded by the number of possible exponent vectors. -/
theorem polynomialSmoothMaximum_le_pow (T t : ℕ) :
    polynomialSmoothMaximum F T t ≤ (t+1) ^ (polynomialSmoothPrimes F T).card := by
  classical
  let S := polynomialSmoothPrimes F T
  have hs {f : polynomialSmoothBall F T t} {p : Polynomial F} (hp : p ∈ normalizedFactors f.1) :
      p ∈ S := by
    have hi := irreducible_of_normalized_factor p hp
    exact mem_polynomialSmoothPrimes.mpr
      ⟨(normalize_eq_self_iff_monic hi.ne_zero).mp (normalize_normalized_factor p hp), hi,
        (mem_polynomialSmoothBall.mp f.2).2.2 p hp⟩
  have hprod (f : polynomialSmoothBall F T t) : (normalizedFactors f.1).prod = f.1 := by
    simpa only [(mem_polynomialSmoothBall.mp f.2).1.leadingCoeff, C_1, one_mul] using
      leadingCoeff_mul_prod_normalizedFactors f.1
  let code (f : polynomialSmoothBall F T t) (p : S) : Fin (t+1) := by
    let k := (normalizedFactors f.1).count p.1
    refine ⟨k, Nat.lt_succ_of_le ?_⟩
    have hsub : Multiset.replicate k p.1 ≤ normalizedFactors f.1 :=
      Multiset.le_count_iff_replicate_le.mp le_rfl
    have hdvd := Multiset.prod_dvd_prod_of_le hsub
    rw [Multiset.prod_replicate, hprod] at hdvd
    obtain ⟨hpm, hpi, _⟩ := mem_polynomialSmoothPrimes.mp p.2
    obtain ⟨hfm, hfd, _⟩ := mem_polynomialSmoothBall.mp f.2
    have hd := natDegree_le_of_dvd hdvd hfm.ne_zero
    rw [hpm.natDegree_pow] at hd
    exact (by simpa using Nat.mul_le_mul_left k hpi.natDegree_pos : k ≤ k * p.1.natDegree).trans
      (hd.trans hfd)
  have hinj : Function.Injective code := by
    intro f g hfg
    apply Subtype.ext
    rw [← hprod f, ← hprod g]
    congr 1
    apply Multiset.ext'
    intro p
    by_cases hp : p ∈ S
    · exact congrArg (fun x : S → Fin (t+1) ↦ (x ⟨p, hp⟩).val) hfg
    · rw [Multiset.count_eq_zero_of_notMem (fun h ↦ hp (hs h)),
        Multiset.count_eq_zero_of_notMem (fun h ↦ hp (hs h))]
  obtain ⟨B, hB, _, hcard⟩ := exists_polynomialSmoothMaximum (F := F) T t
  have hbound := Fintype.card_le_of_injective code hinj
  rw [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe] at hbound
  exact hcard ▸ (Finset.card_le_card hB).trans hbound

/-- The degrees of the cutoff primes can be computed without a polynomial-ring
normalization oracle. This multiset suffices for the finite Euler factors. -/
def polynomialSmoothPrimeDegrees (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (T : ℕ) : Multiset ℕ :=
  ((Finset.univ : Finset (Coefficients F (T+1))).filter fun v ↦
    vectorPrimeTest v).val.map vectorNatDegree

theorem polynomialSmoothPrimeDegrees_eq (T : ℕ) :
    polynomialSmoothPrimeDegrees F T = (polynomialSmoothPrimes F T).val.map Polynomial.natDegree := by
  let P := (Finset.univ : Finset (Coefficients F (T+1))).filter fun v ↦ vectorPrimeTest v
  have hP : P.map (vectorPolynomial (T+1)) = polynomialSmoothPrimes F T := by
    ext f
    rw [Finset.mem_map, mem_polynomialSmoothPrimes]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have h := (vectorPrime_iff v).mp ((vectorPrimeTest_eq_true_iff v).mp (Finset.mem_filter.mp hv).2)
      have hd := vectorPolynomial_degree_lt v
      rw [degree_eq_natDegree h.1.ne_zero, Nat.cast_lt, Nat.lt_succ_iff] at hd
      exact ⟨h.1, h.2, hd⟩
    · rintro ⟨hm, hi, hd⟩
      have hdeg : f.degree < (T+1 : ℕ) := by
        rwa [degree_eq_natDegree hm.ne_zero, Nat.cast_lt, Nat.lt_succ_iff]
      obtain ⟨v, rfl⟩ := exists_vectorPolynomial hdeg
      exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (vectorPrimeTest_eq_true_iff v).mpr ((vectorPrime_iff v).mpr ⟨hm, hi⟩)⟩, rfl⟩
  rw [← hP, Finset.map_val, Multiset.map_map]
  change P.val.map vectorNatDegree = _
  exact Multiset.map_congr rfl (fun v _ ↦ (vectorPolynomial_natDegree v).symm)

end GRHArticle.ProgressionFree
