import GRHArticle.ProgressionFree.FinitePrimeBlockDensity
import GRHArticle.ProgressionFree.IndependentPrimeRuleDensity

/-!
# Finite exceptional blocks with a fixed exterior rule

Once finitely many block constraints are fixed, the exterior rule may
be imposed independently at all other primes. An exterior rule accepting
zero and one can be truncated with a uniform square-tail error.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology
open scoped Classical BigOperators

/-- Arbitrary rules on finitely many exceptional prime blocks, and the same
independent exponent rule at every prime outside their union. -/
def finiteExceptionPrimeRule (S : Finset (Finset ℕ))
    (rules : (P : Finset ℕ) → Set (↥P → ℕ)) (G : Set ℕ) : Set ℕ :=
  {n | n ∈ finitePrimeBlockRule S rules ∧
    ∀ p : ℕ, p.Prime → p ∉ S.biUnion id → n.factorization p ∈ G}

/-- A finite local block probability is nonnegative. -/
theorem primeBlockProbability_nonneg {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (F : Set (↥P → ℕ)) : 0 ≤ primeBlockProbability P F := by
  apply mul_nonneg
  · exact prod_nonneg fun p _ ↦ sub_nonneg.mpr
      ((div_le_one (by exact_mod_cast (hP _ p.property).pos)).mpr
        (by exact_mod_cast (hP _ p.property).one_lt.le))
  · rw [reciprocalExponentMass_eq_tsum_subtype]
    exact tsum_nonneg fun _ ↦ reciprocalExponentWeight_nonneg (fun _ ↦ by positivity) _

/-- Add finitely many independent prime rules to disjoint exceptional blocks.
The new primes must avoid the union of the exceptional blocks. -/
theorem hasNaturalDensity_mixedBlockRule (S : Finset (Finset ℕ))
    (rules : (P : Finset ℕ) → Set (↥P → ℕ)) (G : Set ℕ) (T : Finset ℕ)
    (hS : ∀ P ∈ S, ∀ p ∈ P, p.Prime) (hpair : (S : Set (Finset ℕ)).PairwiseDisjoint id)
    (hT : ∀ p ∈ T, p.Prime) (hdis : Disjoint T (S.biUnion id)) :
    HasNaturalDensity (finitePrimeBlockRule S rules ∩ integerFiniteIndependentPrimeRules T (fun _ ↦ G))
      ((∏ P ∈ S, primeBlockProbability P (rules P)) *
        ∏ p ∈ T, primeBlockProbability {p} (blockwiseIndependentRules (fun _ ↦ G) {p})) := by
  let U := T.image (singleton : ℕ → Finset ℕ)
  let R (P : Finset ℕ) : Set (↥P → ℕ) :=
    if P ∈ S then rules P else blockwiseIndependentRules (fun _ ↦ G) P
  have hSU : Disjoint S U := disjoint_left.mpr fun P hP hU ↦ by
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hU
    exact (disjoint_left.mp hdis) hp (mem_biUnion.mpr ⟨{p},hP,mem_singleton_self p⟩)
  have hRU (p : ℕ) (hp : p ∈ T) : R {p} = blockwiseIndependentRules (fun _ ↦ G) {p} :=
    if_neg (fun hs ↦ (disjoint_left.mp hSU) hs (mem_image_of_mem _ hp))
  have hSP (P : Finset ℕ) (hP : P ∈ S) : R P = rules P := if_pos hP
  have hpr (P : Finset ℕ) (hP : P ∈ S ∪ U) : ∀ p ∈ P, p.Prime := by
    rcases mem_union.mp hP with hP | hP
    · exact hS P hP
    · obtain ⟨q,hq,rfl⟩ := mem_image.mp hP
      intro p hp
      exact (mem_singleton.mp hp).symm ▸ hT q hq
  have hsep (P : Finset ℕ) (hP : P ∈ S) (Q : Finset ℕ) (hQ : Q ∈ U) : Disjoint P Q := by
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hQ
    exact disjoint_left.mpr fun p hp hp' ↦ (disjoint_left.mp hdis)
      ((mem_singleton.mp hp').symm ▸ hq) (mem_biUnion.mpr ⟨P,hP,hp⟩)
  have hpairs : ((S ∪ U : Finset (Finset ℕ)) : Set (Finset ℕ)).PairwiseDisjoint id := by
    intro P hP Q hQ hPQ
    rcases mem_union.mp hP with hP | hP <;> rcases mem_union.mp hQ with hQ | hQ
    · exact hpair hP hQ hPQ
    · exact hsep P hP Q hQ
    · exact (hsep Q hQ P hP).symm
    · obtain ⟨p,_,rfl⟩ := mem_image.mp hP
      obtain ⟨q,_,rfl⟩ := mem_image.mp hQ
      exact disjoint_singleton.mpr fun he ↦ hPQ (congrArg singleton he)
  have hset : finitePrimeBlockRule (S ∪ U) R =
      finitePrimeBlockRule S rules ∩ integerFiniteIndependentPrimeRules T (fun _ ↦ G) := by
    ext n
    constructor
    · rintro ⟨hn,h⟩
      refine ⟨⟨hn,fun P hP ↦ ?_⟩,⟨hn,fun p ↦ ?_⟩⟩
      · exact hSP P hP ▸ h P (mem_union_left _ hP)
      · have hm := hRU p.val p.property ▸ h {p.val} (mem_union_right _ (mem_image_of_mem _ p.property))
        exact hm ⟨p.val, mem_singleton_self _⟩
    · rintro ⟨⟨hn,h⟩,⟨_,ht⟩⟩
      refine ⟨hn, fun P hP ↦ ?_⟩
      rcases mem_union.mp hP with hP | hP
      · exact (hSP P hP).symm ▸ h P hP
      · obtain ⟨p,hp,rfl⟩ := mem_image.mp hP
        rw [hRU p hp]
        intro q
        have he := mem_singleton.mp q.property
        change n.factorization q.val ∈ G
        rw [he]
        exact ht ⟨p,hp⟩
  have hProdS : (∏ P ∈ S, primeBlockProbability P (R P)) = ∏ P ∈ S, primeBlockProbability P (rules P) :=
    prod_congr rfl fun P hP ↦ by rw [hSP P hP]
  have hProdT : (∏ P ∈ U, primeBlockProbability P (R P)) =
      ∏ p ∈ T, primeBlockProbability {p} (blockwiseIndependentRules (fun _ ↦ G) {p}) := by
    rw [show U = T.image (singleton : ℕ → Finset ℕ) from rfl, prod_image]
    · exact prod_congr rfl fun p hp ↦ by rw [hRU p hp]
    · exact fun a _ b _ h ↦ singleton_injective h
  have hd := hasNaturalDensity_finitePrimeBlockRule (S ∪ U) R hpr hpairs
  rwa [hset,prod_union hSU,hProdS,hProdT] at hd

private def exteriorPrimes (S : Finset (Finset ℕ)) (Y : ℕ) : Finset ℕ :=
  Nat.primesLE Y \ S.biUnion id

private def exteriorApproximation (S : Finset (Finset ℕ))
    (rules : (P : Finset ℕ) → Set (↥P → ℕ)) (G : Set ℕ) (Y : ℕ) : Set ℕ :=
  finitePrimeBlockRule S rules ∩ integerFiniteIndependentPrimeRules (exteriorPrimes S Y) (fun _ ↦ G)

private noncomputable def exteriorMass (S : Finset (Finset ℕ)) (G : Set ℕ) (Y : ℕ) : ℝ :=
  ∏ p ∈ exteriorPrimes S Y, primeBlockProbability {p} (blockwiseIndependentRules (fun _ ↦ G) {p})

private theorem exteriorApproximation_density (S : Finset (Finset ℕ))
    (rules : (P : Finset ℕ) → Set (↥P → ℕ)) (G : Set ℕ) (Y : ℕ)
    (hS : ∀ P ∈ S, ∀ p ∈ P, p.Prime) (hpair : (S : Set (Finset ℕ)).PairwiseDisjoint id) :
    HasNaturalDensity (exteriorApproximation S rules G Y)
      ((∏ P ∈ S, primeBlockProbability P (rules P)) * exteriorMass S G Y) := by
  apply hasNaturalDensity_mixedBlockRule S rules G (exteriorPrimes S Y) hS hpair
  · intro p hp
    exact Nat.prime_of_mem_primesLE (mem_sdiff.mp hp).1
  · exact disjoint_left.mpr fun p hp hS ↦ (mem_sdiff.mp hp).2 hS

private theorem exteriorApproximation_error (S : Finset (Finset ℕ))
    (rules : (P : Finset ℕ) → Set (↥P → ℕ)) {G : Set ℕ} (h0 : 0 ∈ G) (h1 : 1 ∈ G)
    (Y N : ℕ) (hY : 0 < Y) :
    |densityUpTo (finiteExceptionPrimeRule S rules G) N -
      densityUpTo (exteriorApproximation S rules G Y) N| ≤ 1/(Y : ℝ) := by
  refine (densityUpTo_abs_sub_le_of_symmDiff_subset
    (E := {n | ∃ p, Y < p ∧ p.Prime ∧ p^2 ∣ n}) N ?_).trans
    (densityUpTo_largePrimeSquare_le Y N hY)
  intro n h
  rcases h with ⟨h,h'⟩ | ⟨h,h'⟩
  · exact (h' ⟨h.1,⟨h.1.1, fun p ↦ h.2 p.val
      (Nat.prime_of_mem_primesLE (mem_sdiff.mp p.property).1) (mem_sdiff.mp p.property).2⟩⟩).elim
  · by_contra hSquare
    apply h'
    refine ⟨h.1, fun p hp hOut ↦ ?_⟩
    by_cases hpY : p ≤ Y
    · exact h.2.2 ⟨p,mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨hpY,hp⟩,hOut⟩⟩
    · have hsmall : n.factorization p < 2 := by
        by_contra! he
        exact hSquare ⟨p, lt_of_not_ge hpY, hp, (hp.pow_dvd_iff_le_factorization h.1.1).mpr he⟩
      rcases (show n.factorization p = 0 ∨ n.factorization p = 1 by omega) with he | he
      · exact he.symm ▸ h0
      · exact he.symm ▸ h1

/-- With an exterior rule containing zero and one, finitely many exceptional
blocks always give a true natural density. -/
theorem exists_hasNaturalDensity_finiteExceptionPrimeRule (S : Finset (Finset ℕ))
    (rules : (P : Finset ℕ) → Set (↥P → ℕ)) {G : Set ℕ} (h0 : 0 ∈ G) (h1 : 1 ∈ G)
    (hS : ∀ P ∈ S, ∀ p ∈ P, p.Prime) (hpair : (S : Set (Finset ℕ)).PairwiseDisjoint id) :
    ∃ d, HasNaturalDensity (finiteExceptionPrimeRule S rules G) d := by
  apply exists_hasNaturalDensity_of_uniform_approximation
  intro ε hε
  obtain ⟨Y,hY⟩ := exists_nat_one_div_lt hε
  refine ⟨_,_,exteriorApproximation_density S rules G (Y+1) hS hpair, fun N ↦ ?_⟩
  exact (exteriorApproximation_error S rules h0 h1 (Y+1) N (Nat.succ_pos _)).trans
    (by exact_mod_cast hY.le)

/-- Comparing two exceptional rule families on the same blocks cancels the
common exterior density factor. -/
theorem finiteExceptionPrimeRule_density_cross_mul (S : Finset (Finset ℕ))
    (rules₁ rules₂ : (P : Finset ℕ) → Set (↥P → ℕ)) {G : Set ℕ} (h0 : 0 ∈ G) (h1 : 1 ∈ G)
    (hS : ∀ P ∈ S, ∀ p ∈ P, p.Prime) (hpair : (S : Set (Finset ℕ)).PairwiseDisjoint id)
    {d₁ d₂ : ℝ} (hd₁ : HasNaturalDensity (finiteExceptionPrimeRule S rules₁ G) d₁)
    (hd₂ : HasNaturalDensity (finiteExceptionPrimeRule S rules₂ G) d₂) :
    d₁ * (∏ P ∈ S, primeBlockProbability P (rules₂ P)) =
      d₂ * (∏ P ∈ S, primeBlockProbability P (rules₁ P)) := by
  let a (rules : (P : Finset ℕ) → Set (↥P → ℕ)) := ∏ P ∈ S, primeBlockProbability P (rules P)
  have ha (rules : (P : Finset ℕ) → Set (↥P → ℕ)) : 0 ≤ a rules :=
    prod_nonneg fun P hP ↦ primeBlockProbability_nonneg (hS P hP) (rules P)
  have hclose (rules : (P : Finset ℕ) → Set (↥P → ℕ)) {d : ℝ}
      (hd : HasNaturalDensity (finiteExceptionPrimeRule S rules G) d)
      {Y : ℕ} (hY : 0 < Y) : |d - a rules * exteriorMass S G Y| ≤ 1/(Y : ℝ) :=
    le_of_tendsto' (hd.sub (exteriorApproximation_density S rules G Y hS hpair)).abs
      (fun N ↦ exteriorApproximation_error S rules h0 h1 Y N hY)
  have hev : ∀ᶠ Y : ℕ in atTop, |d₁*a rules₂-d₂*a rules₁| ≤
      (a rules₁+a rules₂) * (1/(Y : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with Y hY
    let w := exteriorMass S G Y
    rw [show d₁*a rules₂-d₂*a rules₁ =
      (d₁-a rules₁*w)*a rules₂-(d₂-a rules₂*w)*a rules₁ by ring]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul,abs_mul,abs_of_nonneg (ha rules₂),abs_of_nonneg (ha rules₁)]
    exact (add_le_add (mul_le_mul_of_nonneg_right (hclose rules₁ hd₁ hY) (ha rules₂))
      (mul_le_mul_of_nonneg_right (hclose rules₂ hd₂ hY) (ha rules₁))).trans_eq (by ring)
  have hlim := tendsto_one_div_atTop_nhds_zero_nat.const_mul (a rules₁+a rules₂)
  rw [mul_zero] at hlim
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (ge_of_tendsto hlim hev) (abs_nonneg _)))

end GRHArticle.ProgressionFree
