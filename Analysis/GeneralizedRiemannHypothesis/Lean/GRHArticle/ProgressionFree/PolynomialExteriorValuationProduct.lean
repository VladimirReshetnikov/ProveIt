import GRHArticle.ProgressionFree.PolynomialExteriorValuationTail
import GRHArticle.ProgressionFree.PolynomialFiniteValuationDensity

/-!
# Exterior Euler products for polynomial valuations

The finite geometric laws converge along all finite sets of tested
primes. The uniform estimate for missed high-degree squares identifies
their infinite product with the actual cofactor limit.
-/

namespace GRHArticle.ProgressionFree

open Polynomial UniqueFactorizationMonoid Filter Topology
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F]

/-- The probability of the allowed exponents at a prime of weight `w`. -/
noncomputable def primeValuationProbability (w : ℝ) (D : Set ℕ) : ℝ :=
  (1-w)*primeExponentWeight w D

theorem primeValuationProbability_singleton (w : ℝ) (a : ℕ) :
    primeValuationProbability w ({a} : Set ℕ) = (1-w)*w^a := by
  simp [primeValuationProbability, primeExponentWeight, Set.indicator, tsum_ite_eq]

theorem primeValuationProbability_zero_one (w : ℝ) :
    primeValuationProbability w ({0,1} : Set ℕ) = 1-w^2 := by
  unfold primeValuationProbability primeExponentWeight
  rw [tsum_eq_sum (s := ({0,1} : Finset ℕ))]
  · simp [Finset.sum_insert, Set.indicator]
    ring
  · intro a ha
    have h : a ∉ ({0,1} : Set ℕ) := by simpa using ha
    exact Set.indicator_of_notMem h _

/-- The weight `q^(-deg p)` of a monic prime. -/
noncomputable def polynomialPrimeWeight (p : F[X]) : ℝ :=
  (Fintype.card F : ℝ)⁻¹^p.natDegree

/-- The limiting probability that none of the specified primes divides
the polynomial. -/
noncomputable def polynomialPrimeExclusionWeight (S : Finset F[X]) : ℝ :=
  ∏ p ∈ S, (1-polynomialPrimeWeight p)

theorem polynomialPrimeExclusionWeight_pos (S : Finset F[X])
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) :
    0 < polynomialPrimeExclusionWeight S := by
  have hq : 1 < (Fintype.card F : ℝ) := by
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card F)
  apply Finset.prod_pos
  intro p hp
  apply sub_pos.mpr
  exact pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hq) (hS p hp).2.natDegree_pos.ne'

/-- The monic irreducibles exterior to `S`. -/
abbrev PolynomialExteriorMonicPrime (S : Finset F[X]) :=
  {p : F[X] // p.Monic ∧ Irreducible p ∧ p ∉ S}

private def exteriorMonicPrimeEmbedding (S : Finset F[X]) :
    PolynomialExteriorMonicPrime S ↪ F[X] :=
  ⟨Subtype.val, Subtype.val_injective⟩

private noncomputable def finiteExteriorPrimes (S : Finset F[X]) (L : ℕ) :
    Finset (PolynomialExteriorMonicPrime S) :=
  (polynomialSmoothPrimes F L).subtype (fun p ↦ p.Monic ∧ Irreducible p ∧ p ∉ S)

private theorem tendsto_finiteExteriorValuationCofactor
    (S : Finset F[X]) (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p)
    (D : Set ℕ) (T : Finset (PolynomialExteriorMonicPrime S)) :
    Tendsto (monicFamilyProportion
        (finiteExteriorValuationCofactor S (T.map (exteriorMonicPrimeEmbedding S)) D)) atTop
      (𝓝 (polynomialPrimeExclusionWeight S *
        ∏ p ∈ T, primeValuationProbability (polynomialPrimeWeight p.val) D)) := by
  let T' := T.map (exteriorMonicPrimeEmbedding S)
  have hT (p) (hp : p ∈ T') : p.Monic ∧ Irreducible p := by
    obtain ⟨r,_,rfl⟩ := Finset.mem_map.mp hp
    exact ⟨r.property.1,r.property.2.1⟩
  have hdis : Disjoint S T' := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨r,_,rfl⟩ := Finset.mem_map.mp hq
    exact r.property.2.2 hp
  simpa only [finiteExteriorValuationCofactor, T', polynomialPrimeExclusionWeight,
    polynomialPrimeWeight, primeValuationProbability, Finset.prod_map, exteriorMonicPrimeEmbedding,
    Function.Embedding.coeFn_mk] using tendsto_monicFamilyProportion_finiteValuations S T'
      (fun _ ↦ D) hS hT hdis

/-- The actual normalized cofactor limit determines the exterior Euler product.
The factors converge over all finite subsets of the exterior primes. -/
theorem hasProd_exteriorValuationProbability
    (S : Finset F[X]) (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p)
    (D : Set ℕ) (h₀ : 0 ∈ D) (h₁ : 1 ∈ D) {c : ℝ}
    (hlim : Tendsto (monicFamilyProportion (exteriorValuationCofactor S D)) atTop (𝓝 c)) :
    HasProd (fun p : PolynomialExteriorMonicPrime S ↦
        primeValuationProbability (polynomialPrimeWeight p.val) D)
      (c / polynomialPrimeExclusionWeight S) := by
  let q := (Fintype.card F : ℝ)
  let z := q⁻¹
  let a := polynomialPrimeExclusionWeight S
  have ha : 0 < a := polynomialPrimeExclusionWeight_pos S hS
  have hq : 1 < q := by dsimp [q]; exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card F)
  have hz₀ : 0 ≤ z := inv_nonneg.mpr (zero_lt_one.le.trans hq.le)
  have hz₁ : z < 1 := inv_lt_one_of_one_lt₀ hq
  have htail : Tendsto (fun L : ℕ ↦ z^(L+1)/(1-z)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, zero_div] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hz₀ hz₁).comp
        (tendsto_add_atTop_nat 1)).div_const (1-z)
  change Tendsto (fun T : Finset (PolynomialExteriorMonicPrime S) ↦
    ∏ p ∈ T, primeValuationProbability (polynomialPrimeWeight p.val) D) atTop (𝓝 (c/a))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨L, hL⟩ := (htail.eventually_lt_const (mul_pos ha hε)).exists
  filter_upwards [eventually_ge_atTop (finiteExteriorPrimes S L)] with T hT
  let T' := T.map (exteriorMonicPrimeEmbedding S)
  let v := ∏ p ∈ T, primeValuationProbability (polynomialPrimeWeight p.val) D
  have hcover (p) (hp : p ∈ polynomialSmoothPrimes F L) (hpS : p ∉ S) : p ∈ T' := by
    obtain ⟨hm,hi,_⟩ := mem_polynomialSmoothPrimes.mp hp
    let r : PolynomialExteriorMonicPrime S := ⟨p,hm,hi,hpS⟩
    have hsmall : r ∈ finiteExteriorPrimes S L := by simpa [finiteExteriorPrimes, r] using hp
    exact Finset.mem_map.mpr ⟨r,hT hsmall,rfl⟩
  have h := finiteExteriorValuationCofactor_tail S T' D h₀ h₁ L
  have hfin := tendsto_finiteExteriorValuationCofactor S hS D T
  have hlow : c ≤ a*v := le_of_tendsto_of_tendsto hlim hfin
    (Eventually.of_forall fun n ↦ (h n hcover).1)
  have hhigh : a*v ≤ c + z^(L+1)/(1-z) := le_of_tendsto_of_tendsto hfin
    (hlim.add tendsto_const_nhds) (Eventually.of_forall fun n ↦ (h n hcover).2)
  have hv₀ : c/a ≤ v := (div_le_iff₀ ha).mpr (by simpa only [mul_comm v a] using hlow)
  have hv₁ : v-c/a ≤ (z^(L+1)/(1-z))/a := by
    apply (le_div_iff₀ ha).mpr
    rw [sub_mul, div_mul_cancel₀ c ha.ne', mul_comm v a]
    exact sub_le_iff_le_add.mpr (by simpa only [add_comm c] using hhigh)
  change dist v (c/a) < ε
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hv₀)]
  exact hv₁.trans_lt ((div_lt_iff₀ ha).mpr (by simpa only [mul_comm ε a] using hL))

/-- The article's exterior greedy factor `C_S`. -/
noncomputable def greedyPrimeExteriorProduct (S : Finset F[X]) : ℝ :=
  ∏' p : PolynomialExteriorMonicPrime S,
    primeValuationProbability (polynomialPrimeWeight p.val) greedyExponents

theorem hasProd_greedyPrimeExterior (S : Finset F[X])
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) :
    HasProd (fun p : PolynomialExteriorMonicPrime S ↦
        primeValuationProbability (polynomialPrimeWeight p.val) greedyExponents)
      (greedyPrimeAvoidingDensity S / polynomialPrimeExclusionWeight S) := by
  apply hasProd_exteriorValuationProbability S hS greedyExponents
    zero_mem_greedyExponents one_mem_greedyExponents
  unfold monicFamilyProportion
  refine (tendsto_greedyPrimeAvoidingLayer_card_div_pow S hS).congr (fun n ↦ ?_)
  have he : monicFamilyLayer (exteriorValuationCofactor S greedyExponents) n =
      greedyPrimeAvoidingLayer S n := by
    ext f
    rw [mem_monicFamilyLayer, mem_greedyPrimeAvoidingLayer]
    rfl
  rw [he]

/-- Removing all powers of the primes in `S` contributes exactly the
finite exclusion factor to the cofactor density. -/
theorem greedyPrimeAvoidingDensity_eq_exclusion_mul_exteriorProduct
    (S : Finset F[X]) (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) :
    greedyPrimeAvoidingDensity S = polynomialPrimeExclusionWeight S * greedyPrimeExteriorProduct S := by
  unfold greedyPrimeExteriorProduct
  rw [(hasProd_greedyPrimeExterior S hS).tprod_eq, mul_comm,
    div_mul_cancel₀ _ (polynomialPrimeExclusionWeight_pos S hS).ne']

theorem one_sub_inv_card_le_greedyPrimeExteriorProduct
    (S : Finset F[X]) (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) :
    1-(Fintype.card F : ℝ)⁻¹ ≤ greedyPrimeExteriorProduct S := by
  have h := greedyPrimeAvoidingDensity_ge_exclusion_product S hS
  rw [greedyPrimeAvoidingDensity_eq_exclusion_mul_exteriorProduct S hS] at h
  change (1-(Fintype.card F : ℝ)⁻¹) * polynomialPrimeExclusionWeight S ≤
    polynomialPrimeExclusionWeight S * greedyPrimeExteriorProduct S at h
  rw [mul_comm (1-(Fintype.card F : ℝ)⁻¹)] at h
  exact le_of_mul_le_mul_left h (polynomialPrimeExclusionWeight_pos S hS)

/-- The exterior Euler factor is the cofactor density divided by the
probability of excluding the distinguished primes. -/
theorem greedyPrimeExteriorProduct_eq_cofactor_ratio (S : Finset F[X])
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) :
    greedyPrimeExteriorProduct S = greedyPrimeAvoidingDensity S / polynomialPrimeExclusionWeight S :=
  (hasProd_greedyPrimeExterior S hS).tprod_eq

/-- The linear-prime specialization gives the constant used in the
one-free-prime optimum. -/
theorem greedyPrimeAvoidingDensity_singleton_linear_eq_exteriorProduct {P : F[X]}
    (hm : P.Monic) (hi : Irreducible P) (hP : P.natDegree = 1) :
    greedyPrimeAvoidingDensity {P} =
      (1-(Fintype.card F : ℝ)⁻¹) * greedyPrimeExteriorProduct {P} := by
  rw [greedyPrimeAvoidingDensity_eq_exclusion_mul_exteriorProduct {P} (by simpa using And.intro hm hi),
    polynomialPrimeExclusionWeight, Finset.prod_singleton, polynomialPrimeWeight, hP, pow_one]

/-- The all-prime comparison product for allowed valuations zero and one. -/
theorem hasProd_monicPrime_one_sub_weight_sq :
    HasProd (fun p : PolynomialExteriorMonicPrime (∅ : Finset F[X]) ↦
        1-(polynomialPrimeWeight p.val)^2) (1-(Fintype.card F : ℝ)⁻¹) := by
  have hlim : Tendsto (monicFamilyProportion
      (exteriorValuationCofactor (∅ : Finset F[X]) ({0,1} : Set ℕ))) atTop
      (𝓝 (1-(Fintype.card F : ℝ)⁻¹)) := by
    have he (n : ℕ) : monicFamilyLayer (exteriorValuationCofactor (∅ : Finset F[X])
        ({0,1} : Set ℕ)) n = squarefreeLayer F ∅ n := by
      ext f
      rw [mem_monicFamilyLayer, mem_squarefreeLayer]
      refine and_congr_right (fun hm ↦ and_congr_right (fun _ ↦ ?_))
      rw [squarefree_iff_nodup_normalizedFactors hm.ne_zero, Multiset.nodup_iff_count_le_one]
      simp only [exteriorValuationCofactor, Set.mem_setOf_eq, Finset.notMem_empty, IsEmpty.forall_iff,
        implies_true, true_and, and_true, polynomialPrimeExponent, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact forall_congr' fun _ ↦ by omega
    unfold monicFamilyProportion
    simp_rw [he]
    simpa only [Finset.prod_empty, mul_one] using
      tendsto_normalized_squarefreeLayer (F := F) ∅ (by simp)
  simpa only [primeValuationProbability_zero_one, polynomialPrimeExclusionWeight,
      Finset.prod_empty, div_one] using
    hasProd_exteriorValuationProbability (∅ : Finset F[X]) (by simp) {0,1}
      (by simp) (by simp) hlim

/-- Finite coordinate restrictions multiply their local probabilities by
the Euler product of the exterior greedy factors. -/
theorem tendsto_monicValuationRuleSet_greedyExterior_product
    (S : Finset F[X]) (D : F[X] → Set ℕ) (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) :
    Tendsto (monicFamilyProportion
        (monicValuationRuleSet (replacePrimeRules S (fun _ ↦ greedyExponents) D))) atTop
      (𝓝 ((∏ p ∈ S, primeValuationProbability (polynomialPrimeWeight p) (D p)) *
        greedyPrimeExteriorProduct S)) := by
  have h := tendsto_monicValuationRuleSet_greedyExterior S D hS
  rw [greedyPrimeAvoidingDensity_eq_exclusion_mul_exteriorProduct S hS, mul_right_comm] at h
  simpa only [polynomialPrimeExclusionWeight, polynomialPrimeWeight, primeValuationProbability,
    Finset.prod_mul_distrib, mul_assoc] using h

end GRHArticle.ProgressionFree
