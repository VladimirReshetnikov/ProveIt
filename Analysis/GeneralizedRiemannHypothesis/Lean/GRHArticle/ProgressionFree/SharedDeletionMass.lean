import GRHArticle.ProgressionFree.SharedDeletionProgressions
import GRHArticle.ProgressionFree.PrimeBlockRuleDensity

/-!
# Finite reciprocal-mass gain of the shared deletion

The deleted rows consist of the all-baseline row and, independently for
each satellite, a row of large exponents. The inserted vectors have
a fixed marker exponent and one raised satellite exponent.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped Classical BigOperators

/-- The unedited independent exponent patterns on the affected primes. -/
def sharedDeletionBasePatterns {ι : Type*} (G : Set ℕ) : Set (ℕ × (ι → ℕ)) :=
  {v | v.1 ∈ G ∧ ∀ q, v.2 q ∈ G}

/-- The exact edited patterns in marker-and-satellites coordinates. -/
def sharedDeletionEditedPatterns {ι : Type*} [DecidableEq ι] (b : ℕ) (G : Set ℕ) :
    Set (ℕ × (ι → ℕ)) :=
  {v | (fun j ↦ j.elim v.1 v.2) ∈ sharedDeletionRule b G}

private def raised {ι : Type*} [DecidableEq ι] (b : ℕ) (q : ι) (a : ℕ) (r : ι) : ℕ :=
  if r = q then a else b

private def allBase {ι : Type*} (b : ℕ) : ℕ ↪ (ℕ × (ι → ℕ)) :=
  ⟨fun n ↦ (n, fun _ ↦ b), fun _ _ h ↦ congrArg Prod.fst h⟩

private def oneRaised {ι : Type*} [DecidableEq ι] (b : ℕ) (q : ι) :
    (ℕ × ℕ) ↪ (ℕ × (ι → ℕ)) :=
  ⟨fun n ↦ (n.1, raised b q n.2), fun a c h ↦ Prod.ext (congrArg (fun z : ℕ × (ι → ℕ) ↦ z.1) h)
    (by simpa [raised] using congrArg (fun z : ℕ × (ι → ℕ) ↦ z.2 q) h)⟩

private def inserted {ι : Type*} [DecidableEq ι] (b : ℕ) : ι ↪ (ℕ × (ι → ℕ)) :=
  ⟨fun q ↦ (b+1, raised b q (b+1)), fun q r he ↦ by
    by_contra h
    have hh := congrArg (fun z : ℕ × (ι → ℕ) ↦ z.2 q) he
    simp [raised,h] at hh⟩

private theorem is_inserted_iff {ι : Type*} [DecidableEq ι] (b : ℕ) (q : ι)
    (v : ℕ × (ι → ℕ)) :
    sharedDeletionVector b q = (fun j ↦ j.elim v.1 v.2) ↔ inserted b q = v := by
  constructor
  · intro h
    exact Prod.ext (congrFun h none) (funext fun p ↦ congrFun h (some p))
  · intro h
    funext j
    cases j
    · exact congrArg Prod.fst h
    · exact congrFun (congrArg Prod.snd h) _

private theorem prod_raised {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → ℝ)
    {b a : ℕ} (q : ι) (hba : b ≤ a) :
    (∏ p, u p ^ raised b q a p) = (∏ p, u p ^ b) * u q^(a-b) := by
  rw [← Fintype.prod_ite_eq' q (fun p ↦ u p^(a-b)), ← prod_mul_distrib]
  apply prod_congr rfl
  intro p _
  by_cases hp : p = q
  · simp only [raised, if_pos hp, ← pow_add, Nat.add_sub_of_le hba]
  · simp [raised,hp]

/-- Signed mass identity for the exact bounded exponent patterns of the
article's exchange. Its three terms are insertions, all-baseline deletions,
and one-satellite tail deletions. -/
theorem sharedDeletionPatternMass_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ℝ) (u : ι → ℝ) {b K : ℕ} {G : Set ℕ}
    (hb : b ∈ G) (hskip : b+1 ∉ G) (hK : b+1 < K) :
    exactPatternMass w u (sharedDeletionEditedPatterns b G) K -
      exactPatternMass w u (sharedDeletionBasePatterns G) K =
      (∏ q, u q^b) * (w^(b+1) * (∑ q, u q) -
        (∑ n ∈ exponentsBelow G K, w^n) *
          (1 + ∑ q, ∑ a ∈ (exponentsBelow G K).filter (b+2 ≤ ·), u q^(a-b))) := by
  let H := exponentsBelow G K
  let T : Finset (ℕ × (ι → ℕ)) := boundedExactPatterns (sharedDeletionBasePatterns G) K
  let U : Finset (ℕ × (ι → ℕ)) := boundedExactPatterns (sharedDeletionEditedPatterns b G) K
  let H' := H.filter (b+2 ≤ ·)
  let A : Finset (ℕ × (ι → ℕ)) := H.map (allBase b)
  let B (q : ι) := (H ×ˢ H').map (oneRaised b q)
  let R := A ∪ (univ.biUnion B)
  let V := univ.map (inserted (ι := ι) b)
  let f := exactPatternWeight w u
  let W := ∏ q, u q^b
  let J := ∑ n ∈ H, w^n
  have hbH : b ∈ H := mem_exponentsBelow.mpr ⟨hb, by omega⟩
  have hT (v : ℕ × (ι → ℕ)) : v ∈ T ↔ v.1 ∈ H ∧ ∀ q, v.2 q ∈ H := by
    simp only [T, H, mem_boundedExactPatterns, sharedDeletionBasePatterns, Set.mem_setOf_eq,
      mem_exponentsBelow]
    constructor
    · rintro ⟨⟨h₁,h₂⟩,h₃,h₄⟩
      exact ⟨⟨h₁,h₃⟩,fun q ↦ ⟨h₂ q,h₄ q⟩⟩
    · rintro ⟨⟨h₁,h₃⟩,h⟩
      exact ⟨⟨h₁,fun q ↦ (h q).1⟩,h₃,fun q ↦ (h q).2⟩
  have hA (v : ℕ × (ι → ℕ)) : v ∈ A ↔ v.1 ∈ H ∧ ∀ q, v.2 q = b := by
    constructor
    · rintro h
      obtain ⟨n,hn,rfl⟩ := mem_map.mp h
      exact ⟨hn, fun _ ↦ rfl⟩
    · rintro ⟨hn,hq⟩
      exact mem_map.mpr ⟨v.1,hn,Prod.ext rfl (funext fun q ↦ (hq q).symm)⟩
  have hB (q : ι) (v : ℕ × (ι → ℕ)) :
      v ∈ B q ↔ v.1 ∈ H ∧ v.2 q ∈ H' ∧ ∀ r, r ≠ q → v.2 r = b := by
    constructor
    · intro h
      change v ∈ (H ×ˢ H').map (oneRaised b q) at h
      obtain ⟨⟨n,a⟩,hm,he⟩ := mem_map.mp h
      obtain ⟨hn,ha⟩ := mem_product.mp hm
      rw [← he]
      exact ⟨hn, by simpa [oneRaised,raised] using ha, fun r hr ↦ by simp [oneRaised,raised,hr]⟩
    · rintro ⟨hn,ha,hr⟩
      refine mem_map.mpr ⟨(v.1,v.2 q), mem_product.mpr ⟨hn,ha⟩, Prod.ext rfl (funext fun p ↦ ?_)⟩
      by_cases hp : p = q
      · subst p; simp [oneRaised,raised]
      · simp [oneRaised,raised,hp,hr p hp]
  have hh (a : ℕ) (ha : a ∈ H') : b+2 ≤ a := (mem_filter.mp ha).2
  have hR : R ⊆ T := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · obtain ⟨h₁,h₂⟩ := (hA v).mp hv
      exact (hT v).mpr ⟨h₁, fun q ↦ (h₂ q).symm ▸ hbH⟩
    · obtain ⟨q,_,hq⟩ := mem_biUnion.mp hv
      obtain ⟨h₁,h₂,h₃⟩ := (hB q v).mp hq
      refine (hT v).mpr ⟨h₁,fun p ↦ ?_⟩
      by_cases hp : p = q
      · simpa only [hp] using (mem_filter.mp h₂).1
      · exact (h₃ p hp).symm ▸ hbH
  have hDisRows : ((univ : Finset ι) : Set ι).PairwiseDisjoint B := by
    intro p _ q _ hpq
    refine disjoint_left.mpr fun v hp hq ↦ ?_
    have hhi := hh _ ((hB p v).mp hp).2.1
    have hlo := ((hB q v).mp hq).2.2 p hpq
    omega
  have hDisA : Disjoint A (univ.biUnion B) := by
    refine disjoint_left.mpr fun v h₁ h₂ ↦ ?_
    obtain ⟨q,_,hq⟩ := mem_biUnion.mp h₂
    have hhi := hh _ ((hB q v).mp hq).2.1
    have hlo := ((hA v).mp h₁).2 q
    omega
  have hU : U = (T \ R) ∪ V := by
    ext v
    rw [mem_union, mem_sdiff, hT, mem_boundedExactPatterns]
    constructor
    · rintro ⟨hOld | ⟨q,hAdd⟩,hn,hcoord⟩
      · have h₁ : v.1 ∈ H := mem_exponentsBelow.mpr ⟨hOld.1 none,hn⟩
        have h₂ (q : ι) : v.2 q ∈ H :=
          mem_exponentsBelow.mpr ⟨hOld.1 (some q),hcoord q⟩
        refine Or.inl ⟨⟨h₁,h₂⟩,fun hv ↦ ?_⟩
        rcases mem_union.mp hv with hv | hv
        · exact hOld.2.1 ((hA v).mp hv).2
        · obtain ⟨q,_,hqr⟩ := mem_biUnion.mp hv
          obtain ⟨_,hhi,hbase⟩ := (hB q v).mp hqr
          exact (not_lt_of_ge (hh _ hhi)) (hOld.2.2 q hbase)
      · exact Or.inr (mem_map.mpr ⟨q,mem_univ _,(is_inserted_iff b q v).mp hAdd⟩)
    · rintro (⟨⟨h₁,h₂⟩,hR'⟩ | h)
      · refine ⟨Or.inl ⟨?_,?_,?_⟩,(mem_exponentsBelow.mp h₁).2,fun p ↦ (mem_exponentsBelow.mp (h₂ p)).2⟩
        · intro p
          cases p with
          | none => exact (mem_exponentsBelow.mp h₁).1
          | some p => exact (mem_exponentsBelow.mp (h₂ p)).1
        · exact fun h ↦ hR' (mem_union_left _ ((hA v).mpr ⟨h₁,h⟩))
        · intro p hothers
          by_contra! hp
          have hrow : v ∈ B p := (hB p v).mpr ⟨h₁,mem_filter.mpr ⟨h₂ p,hp⟩,hothers⟩
          exact hR' (mem_union_right _ (mem_biUnion.mpr ⟨p,mem_univ _,hrow⟩))
      · obtain ⟨q,_,rfl⟩ := mem_map.mp h
        refine ⟨Or.inr ⟨q,(is_inserted_iff b q (inserted b q)).mpr rfl⟩,hK,fun p ↦ ?_⟩
        change raised b q (b+1) p < K
        by_cases hp : p = q <;> simp [raised,hp,hK,show b < K by omega]
  have hDisV : Disjoint (T \ R) V := by
    refine disjoint_left.mpr fun v ht hv ↦ ?_
    obtain ⟨q,_,rfl⟩ := mem_map.mp hv
    have hh := (hT (inserted b q)).mp (mem_sdiff.mp ht).1
    exact hskip (mem_exponentsBelow.mp hh.1).1
  have hA_sum : ∑ v ∈ A, f v = W * J := by
    rw [show A = H.map (allBase b) from rfl, sum_map]
    simp only [f, exactPatternWeight, allBase, Function.Embedding.coeFn_mk, ← sum_mul]
    exact mul_comm _ _
  have hB_sum (q : ι) :
      ∑ v ∈ B q, f v = W * J * ∑ a ∈ H', u q^(a-b) := by
    rw [show B q = (H ×ˢ H').map (oneRaised b q) from rfl, sum_map, sum_product]
    simp only [f, exactPatternWeight, oneRaised, Function.Embedding.coeFn_mk]
    calc
      _ = ∑ n ∈ H, ∑ a ∈ H', (W * w^n) * u q^(a-b) := by
        apply sum_congr rfl
        intro n _
        apply sum_congr rfl
        intro a ha
        rw [prod_raised u q (show b ≤ a from (by omega : b ≤ b+2).trans (hh _ ha))]
        dsimp [W]
        ring
      _ = _ := by simp only [← mul_sum, ← sum_mul, J, mul_assoc]
  have hV_sum : ∑ v ∈ V, f v = W * (w^(b+1) * ∑ q, u q) := by
    rw [show V = univ.map (inserted b) from rfl, sum_map, mul_sum, mul_sum]
    apply sum_congr rfl
    intro p _
    change w^(b+1) * (∏ q, u q^raised b p (b+1) q) = _
    rw [prod_raised u p (by omega), show b+1-b = 1 by omega, pow_one]
    ring
  change (∑ v ∈ U, f v) - (∑ v ∈ T, f v) = _
  rw [hU, sum_union hDisV, ← sum_sdiff hR, show R = A ∪ univ.biUnion B from rfl,
    sum_union hDisA, sum_biUnion hDisRows, hA_sum, hV_sum]
  simp_rw [hB_sum, ← mul_sum]
  change _ = W * (w^(b+1)*(∑ q,u q) - J*(1+∑ q, ∑ a ∈ H', u q^(a-b)))
  ring

private theorem sum_exponent_tail_le {G : Set ℕ} {b K : ℕ} {x : ℝ}
    (hx : 0 ≤ x) (hx' : x ≤ 1/2) :
    (∑ a ∈ (exponentsBelow G K).filter (b+2 ≤ ·), x^(a-b)) ≤ 2*x^2 := by
  have hs : (exponentsBelow G K).filter (b+2 ≤ ·) ⊆ Ico (b+2) K := by
    intro a ha
    exact mem_Ico.mpr ⟨(mem_filter.mp ha).2, (mem_exponentsBelow.mp (mem_filter.mp ha).1).2⟩
  have hg := hasSum_geometric_of_lt_one hx (show x < 1 by linarith)
  calc
    _ ≤ ∑ a ∈ Ico (b+2) K, x^(a-b) := sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ ↦ pow_nonneg hx _)
    _ = x^2 * ∑ n ∈ range (K-(b+2)), x^n := by
      rw [sum_Ico_eq_sum_range, mul_sum]
      apply sum_congr rfl
      intro n _
      rw [← pow_add]
      congr 1
      omega
    _ ≤ x^2 * (1-x)⁻¹ := mul_le_mul_of_nonneg_left
      ((hg.summable.sum_le_tsum _ (fun _ _ ↦ pow_nonneg hx _)).trans_eq hg.tsum_eq) (sq_nonneg _)
    _ ≤ _ := by
      rw [mul_comm 2]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      rw [← one_div, div_le_iff₀ (show 0 < 1-x by linarith)]
      linarith

/-- A surplus of seven times the common baseline is enough for a positive
finite mass gain. This uses a reciprocal-square bound for the satellite
tails. -/
theorem sharedDeletionPatternMass_gain {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w : ℝ} {u : ι → ℝ} {b K : ℕ} {G : Set ℕ}
    (hb : b ∈ G) (hskip : b+1 ∉ G) (hK : b+1 < K)
    (hw : 0 ≤ w) (hw' : w ≤ 1/2)
    (hu : ∀ q, 0 ≤ u q) (hu' : ∀ q, u q ≤ 1/2)
    (hSq : (∑ q, (u q)^2) ≤ 1) (hlarge : 7 ≤ w^(b+1) * ∑ q, u q) :
    (∏ q, u q^b) ≤ exactPatternMass w u (sharedDeletionEditedPatterns b G) K -
      exactPatternMass w u (sharedDeletionBasePatterns G) K := by
  rw [sharedDeletionPatternMass_sub w u hb hskip hK]
  have hwS := hasSum_geometric_of_lt_one hw (show w < 1 by linarith)
  have hj : (∑ n ∈ exponentsBelow G K, w^n) ≤ 2 := by
    refine ((hwS.summable.sum_le_tsum _ (fun _ _ ↦ pow_nonneg hw _)).trans_eq hwS.tsum_eq).trans ?_
    rw [← one_div, div_le_iff₀ (show 0 < 1-w by linarith)]
    linarith
  have hts : (∑ q, ∑ a ∈ (exponentsBelow G K).filter (b+2 ≤ ·), u q^(a-b)) ≤ 2 := by
    refine (sum_le_sum fun q _ ↦ sum_exponent_tail_le (hu q) (hu' q)).trans ?_
    rw [← mul_sum]
    linarith
  have hts₀ : 0 ≤ (∑ q, ∑ a ∈ (exponentsBelow G K).filter (b+2 ≤ ·), u q^(a-b)) :=
    sum_nonneg fun q _ ↦ sum_nonneg fun a _ ↦ pow_nonneg (hu q) _
  have hloss := mul_le_mul hj (show 1 + _ ≤ 3 by linarith only [hts])
    (show 0 ≤ 1 + _ by linarith only [hts₀]) (show (0 : ℝ) ≤ 2 by norm_num)
  have hf : 1 ≤ w^(b+1) * (∑ q, u q) -
      (∑ n ∈ exponentsBelow G K, w^n) *
        (1 + ∑ q, ∑ a ∈ (exponentsBelow G K).filter (b+2 ≤ ·), u q^(a-b)) := by
    linarith only [hloss,hlarge]
  exact (mul_one _).symm.le.trans
    (mul_le_mul_of_nonneg_left hf (prod_nonneg fun q _ ↦ pow_nonneg (hu q) _))

end GRHArticle.ProgressionFree
