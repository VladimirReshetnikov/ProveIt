import GRHArticle.ProgressionFree.CompactPrimeBlockConfigurations
import GRHArticle.ProgressionFree.PaddedPrimeBlockMass
import GRHArticle.ProgressionFree.PrimeBlockDensityUpgrade
import GRHArticle.ProgressionFree.WidthPreservingFiniteExceptions

/-!
# Realizing compact prime-block configurations

The nonzero weights in each row correspond to a genuine finite prime
block. Slice the rule at exponent zero on unoccupied coordinates.
The resulting exceptional blocks are disjoint, and ignoring empty rows
can only increase the normalized density.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped Classical BigOperators OnePoint

/-- Normalized local probability relative to the greedy rule. -/
noncomputable def primeBlockRuleRatio (k : ℕ) (P : Finset ℕ) (R : Set (↥P → ℕ)) : ℝ :=
  primeBlockProbability P R / primeBlockProbability P (greedyExponentPatterns ↥P k)

/-- The density of a reduced rule is the greedy density times its finite
product of local probability ratios. -/
theorem finiteExceptionPrimeRule_density_eq_greedy_mul {k : ℕ} (hk : 3 ≤ k)
    {S : Finset (Finset ℕ)} (R : (P : Finset ℕ) → Set (↥P → ℕ))
    (hPr : ∀ P ∈ S, ∀ p ∈ P, p.Prime)
    (hPair : (S : Set (Finset ℕ)).PairwiseDisjoint id)
    {e dG : ℝ} (he : HasNaturalDensity (finiteExceptionPrimeRule S R (greedyLengthExponents k)) e)
    (hG : HasNaturalDensity (integerGreedyLengthSet k) dG) :
    e = dG * ∏ P ∈ S, primeBlockRuleRatio k P (R P) := by
  have hp : 0 < ∏ P ∈ S, primeBlockProbability P (greedyExponentPatterns ↥P k) :=
    prod_pos fun P hP ↦ primeBlockProbability_greedy_pos (by omega) (hPr P hP)
  simp only [primeBlockRuleRatio,prod_div_distrib,← mul_div_assoc]
  exact (eq_div_iff hp.ne').mpr (finiteExceptionPrimeRule_density_relative_greedy hk R hPr hPair he hG)

private noncomputable def slotPrimeNumber (s : OnePoint ℕ) : ℕ :=
  s.elim 0 (Nat.nth Nat.Prime)

private theorem slotPrimeNumber_nonzero {s : OnePoint ℕ} (hs : slotPrimeNumber s ≠ 0) :
    ∃ n : ℕ, s = (n : OnePoint ℕ) ∧ slotPrimeNumber s = Nat.nth Nat.Prime n := by
  cases s with
  | infty => exact (hs rfl).elim
  | coe n => exact ⟨n,rfl,rfl⟩

private theorem slotPosition_eq_of_samePrime {k m d : ℕ} {x : PrimeBlockSlotConfiguration m d}
    (hx : ValidPrimeBlockSlotConfiguration k x) (a b : Fin m × Fin d)
    (hn : slotPrimeNumber (x.1 a.1 a.2) ≠ 0)
    (he : slotPrimeNumber (x.1 a.1 a.2) = slotPrimeNumber (x.1 b.1 b.2)) : a = b := by
  obtain ⟨n,ha,hnth⟩ := slotPrimeNumber_nonzero hn
  obtain ⟨j,hb,hjth⟩ := slotPrimeNumber_nonzero (fun h ↦ hn (he.trans h))
  have hj : n = j := (Nat.nth_strictMono Nat.infinite_setOf_prime).injective (hnth.symm.trans (he.trans hjth))
  subst j
  by_contra hab
  exact hx.1 a b hab n ⟨ha,hb⟩

private noncomputable def slotPrimeBlock {m d : ℕ} (x : PrimeBlockSlotConfiguration m d)
    (i : Fin m) : Finset ℕ :=
  ((univ : Finset (Fin d)).image (fun j ↦ slotPrimeNumber (x.1 i j))).erase 0

private theorem exists_slot_at_prime {m d : ℕ} (x : PrimeBlockSlotConfiguration m d) (i : Fin m)
    {p : ℕ} (hp : p ∈ slotPrimeBlock x i) : ∃ j : Fin d, slotPrimeNumber (x.1 i j) = p := by
  obtain ⟨j,_,hj⟩ := mem_image.mp (mem_of_mem_erase hp)
  exact ⟨j,hj⟩

private noncomputable def slotPrimeBlockEmbedding {m d : ℕ}
    (x : PrimeBlockSlotConfiguration m d) (i : Fin m) : ↥(slotPrimeBlock x i) ↪ Fin d :=
  ⟨fun p ↦ (exists_slot_at_prime x i p.property).choose, fun p q h ↦ Subtype.ext
    ((exists_slot_at_prime x i p.property).choose_spec.symm.trans
      ((congrArg (fun j ↦ slotPrimeNumber (x.1 i j)) h).trans (exists_slot_at_prime x i q.property).choose_spec))⟩

private theorem slotPrimeBlockEmbedding_spec {m d : ℕ} (x : PrimeBlockSlotConfiguration m d)
    (i : Fin m) (p : ↥(slotPrimeBlock x i)) :
    slotPrimeNumber (x.1 i (slotPrimeBlockEmbedding x i p)) = p.val :=
  (exists_slot_at_prime x i p.property).choose_spec

private theorem prime_of_mem_slotPrimeBlock {m d : ℕ}
    (x : PrimeBlockSlotConfiguration m d) (i : Fin m) (p : ℕ) (hp : p ∈ slotPrimeBlock x i) :
    p.Prime := by
  obtain ⟨j,hj⟩ := exists_slot_at_prime x i hp
  obtain ⟨n,_,hn⟩ := slotPrimeNumber_nonzero (fun h ↦ ne_of_mem_erase hp (hj.symm.trans h))
  exact (hn.symm.trans hj) ▸ Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

private theorem slotPrimeBlock_pairwise {k m d : ℕ} {x : PrimeBlockSlotConfiguration m d}
    (hx : ValidPrimeBlockSlotConfiguration k x) :
    Pairwise (fun i j ↦ Disjoint (slotPrimeBlock x i) (slotPrimeBlock x j)) := by
  intro i j hne
  refine disjoint_left.mpr fun p hp hq ↦ ?_
  obtain ⟨a,ha⟩ := exists_slot_at_prime x i hp
  obtain ⟨b,hb⟩ := exists_slot_at_prime x j hq
  have h := slotPosition_eq_of_samePrime hx (i,a) (j,b)
    (fun he ↦ ne_of_mem_erase hp (ha.symm.trans he)) (ha.trans hb.symm)
  exact hne (congrArg Prod.fst h)

private theorem slotWeight_embedding {m d : ℕ} (x : PrimeBlockSlotConfiguration m d) (i : Fin m)
    (p : ↥(slotPrimeBlock x i)) :
    (primeSlotWeight (x.1 i (slotPrimeBlockEmbedding x i p))).val = 1/(p.val : ℝ) := by
  have he := slotPrimeBlockEmbedding_spec x i p
  obtain ⟨n,hn,hp⟩ := slotPrimeNumber_nonzero (fun h ↦ ne_of_mem_erase p.property (he.symm.trans h))
  rw [hn,primeSlotWeight_coe,hp.symm,he]

private theorem slotWeight_off_embedding {k m d : ℕ} {x : PrimeBlockSlotConfiguration m d}
    (hx : ValidPrimeBlockSlotConfiguration k x) (i : Fin m) (j : Fin d)
    (hj : j ∉ Set.range (slotPrimeBlockEmbedding x i)) : (primeSlotWeight (x.1 i j)).val = 0 := by
  by_cases h : slotPrimeNumber (x.1 i j) = 0
  · generalize hSlot : x.1 i j = s
    rw [hSlot] at h
    cases s with
    | infty => rfl
    | coe n => exact ((Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n).ne_zero h).elim
  · exfalso
    let p : ↥(slotPrimeBlock x i) := ⟨slotPrimeNumber (x.1 i j),
      mem_erase.mpr ⟨h,mem_image_of_mem _ (mem_univ j)⟩⟩
    apply hj
    refine ⟨p,?_⟩
    exact congrArg Prod.snd (slotPosition_eq_of_samePrime hx (i,j)
      (i,slotPrimeBlockEmbedding x i p) h (slotPrimeBlockEmbedding_spec x i p).symm) |>.symm

private noncomputable def slotPrimeBlockRule {m d : ℕ} (x : PrimeBlockSlotConfiguration m d)
    (i : Fin m) : Set (↥(slotPrimeBlock x i) → ℕ) :=
  paddedRuleSlice (slotPrimeBlockEmbedding x i) (exponentRuleOfCode (x.2 i))

private theorem slotRowScore_ruleRatio {k m d : ℕ} (hk : 2 ≤ k) {x : PrimeBlockSlotConfiguration m d}
    (hx : ValidPrimeBlockSlotConfiguration k x) (i : Fin m) :
    primeBlockSlotRowScore k x i = primeBlockRuleRatio k (slotPrimeBlock x i) (slotPrimeBlockRule x i) := by
  unfold primeBlockSlotRowScore
  rw [reciprocalExponentMass_eq_paddedRuleSlice (slotPrimeBlockEmbedding x i) _
      (slotWeight_off_embedding hx i) (exponentRuleOfCode (x.2 i)),
    reciprocalExponentMass_eq_paddedRuleSlice (slotPrimeBlockEmbedding x i) _
      (slotWeight_off_embedding hx i) (greedyExponentPatterns (Fin d) k),
    paddedRuleSlice_greedyExponentPatterns hk]
  simp_rw [slotWeight_embedding]
  unfold primeBlockRuleRatio primeBlockProbability
  have h : 0 < ∏ p : ↥(slotPrimeBlock x i), (1-1/(p.val:ℝ)) := by
    apply prod_pos
    intro p _
    have hp := prime_of_mem_slotPrimeBlock x i _ p.property
    exact sub_pos.mpr ((div_lt_one (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hp.one_lt))
  rw [mul_div_mul_left _ _ h.ne']
  rfl

private theorem slotRowScore_nonneg {k m d : ℕ} (hk : 2 ≤ k)
    (x : PrimeBlockSlotConfiguration m d) (i : Fin m) :
    0 ≤ primeBlockSlotRowScore k x i := by
  unfold primeBlockSlotRowScore
  apply div_nonneg
  · rw [reciprocalExponentMass_eq_tsum_subtype]
    exact tsum_nonneg fun _ ↦ reciprocalExponentWeight_nonneg (fun j ↦ (primeSlotWeight (x.1 i j)).property.1) _
  · exact zero_le_one.trans (one_le_reciprocalExponentMass_greedy hk (fun j ↦ primeSlotWeight (x.1 i j)))

private theorem slotRowScore_le_one_of_empty {k m d : ℕ} (hk : 2 ≤ k)
    {x : PrimeBlockSlotConfiguration m d} (hx : ValidPrimeBlockSlotConfiguration k x)
    (i : Fin m) (hi : (slotPrimeBlock x i) = ∅) : primeBlockSlotRowScore k x i ≤ 1 := by
  have hWeight (p : Fin d) : (primeSlotWeight (x.1 i p)).val = 0 :=
    slotWeight_off_embedding hx i p (by
      rintro ⟨q,hq⟩
      exact notMem_empty _ (Eq.mp (congrArg (fun S : Finset ℕ ↦ q.val ∈ S) hi) q.property))
  unfold primeBlockSlotRowScore
  rw [show (fun p ↦ (primeSlotWeight (x.1 i p)).val) = fun _ ↦ 0 from funext hWeight]
  have hMass : reciprocalExponentMass (fun _ : Fin d ↦ (0:ℝ)) (exponentRuleOfCode (x.2 i)) ≤ 1 := by
    apply Real.tsum_le_of_sum_le
    · exact fun v ↦ Set.indicator_nonneg (fun _ _ ↦ reciprocalExponentWeight_nonneg (fun _ ↦ le_rfl) _) v
    · intro T
      calc
        _ ≤ ∑ v ∈ T, reciprocalExponentWeight (fun _ : Fin d ↦ (0:ℝ)) v := by
          apply sum_le_sum
          intro v _
          by_cases hv : v ∈ exponentRuleOfCode (x.2 i)
          · rw [Set.indicator_of_mem hv]
          · rw [Set.indicator_of_notMem hv]
            exact reciprocalExponentWeight_nonneg (fun _ ↦ le_rfl) _
        _ ≤ _ := by
          simpa using sum_reciprocalExponentWeight_le
            (u := fun _ : Fin d ↦ (0:ℝ)) (fun _ ↦ le_rfl) (fun _ ↦ zero_lt_one) T
  have hDen : 1 ≤ reciprocalExponentMass (fun _ : Fin d ↦ (0:ℝ)) (greedyExponentPatterns (Fin d) k) := by
    simpa only [hWeight] using one_le_reciprocalExponentMass_greedy hk (fun j ↦ primeSlotWeight (x.1 i j))
  exact (div_le_one (zero_lt_one.trans_le hDen)).mpr (hMass.trans hDen)

/-- A finite configuration is realized by a bounded-width set, at a
density at least its normalized score times the greedy density. -/
theorem exists_primeBlockRule_realizing_slotScore {k m d : ℕ} (hk : 3 ≤ k) (hd : 0 < d)
    {x : PrimeBlockSlotConfiguration m d} (hx : ValidPrimeBlockSlotConfiguration k x)
    {dG : ℝ} (hG₀ : 0 ≤ dG) (hG : HasNaturalDensity (integerGreedyLengthSet k) dG) :
    ∃ (S : Finset (Finset ℕ)) (R : (P : Finset ℕ) → Set (↥P → ℕ)) (e : ℝ),
      let A := finiteExceptionPrimeRule S R (greedyLengthExponents k)
      IntegerBoundedPrimeBlockSet d A ∧ KTermGPFree k A ∧
        HasNaturalDensity A e ∧ dG*primeBlockSlotScore k x ≤ e := by
  let P := slotPrimeBlock x
  let I := (univ : Finset (Fin m)).filter (fun i ↦ (P i).Nonempty)
  let S := I.image P
  have hInj : Set.InjOn P (I : Set (Fin m)) := by
    intro i hi j _ he
    by_contra h
    obtain ⟨p,hp⟩ := (mem_filter.mp hi).2
    have hp' : p ∈ P j := he ▸ hp
    exact (disjoint_left.mp (slotPrimeBlock_pairwise hx h)) hp hp'
  have hPick (Q : Finset ℕ) (hQ : Q ∈ S) : ∃ F : Set (↥Q → ℕ),
      KTermVectorAPFree k F ∧ ∀ i ∈ I, P i = Q →
        primeBlockRuleRatio k Q F = primeBlockSlotRowScore k x i := by
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hQ
    refine ⟨slotPrimeBlockRule x i,kTermVectorAPFree_paddedRuleSlice _ (hx.2 i),fun j hj he ↦ ?_⟩
    have h := hInj hj hi he
    subst j
    exact (slotRowScore_ruleRatio (by omega) hx i).symm
  let R (Q : Finset ℕ) : Set (↥Q → ℕ) := if hQ : Q ∈ S then (hPick Q hQ).choose else Set.univ
  have hS (Q : Finset ℕ) (hQ : Q ∈ S) : Q.Nonempty ∧ (∀ p ∈ Q, p.Prime) ∧ Q.card ≤ d := by
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hQ
    have hcard := Fintype.card_le_of_injective (slotPrimeBlockEmbedding x i)
      (slotPrimeBlockEmbedding x i).injective
    rw [Fintype.card_coe,Fintype.card_fin] at hcard
    exact ⟨(mem_filter.mp hi).2,prime_of_mem_slotPrimeBlock x i,hcard⟩
  have hPr (Q : Finset ℕ) (hQ : Q ∈ S) := (hS Q hQ).2.1
  have hPair : (S : Set (Finset ℕ)).PairwiseDisjoint id := by
    intro Q hQ Q' hQ' hne
    obtain ⟨i,_,rfl⟩ := mem_image.mp hQ
    obtain ⟨j,_,rfl⟩ := mem_image.mp hQ'
    exact slotPrimeBlock_pairwise hx (fun h ↦ hne (congrArg P h))
  have hFree (Q : Finset ℕ) (hQ : Q ∈ S) : KTermVectorAPFree k (R Q) := by
    rw [show R Q = (hPick Q hQ).choose from dif_pos hQ]
    exact (hPick Q hQ).choose_spec.1
  let G := greedyLengthExponents k
  have h0 : 0 ∈ G := mem_greedyLengthExponents_of_lt (by omega) (by omega)
  have h1 : 1 ∈ G := mem_greedyLengthExponents_of_lt (by omega) (by omega)
  obtain ⟨e,he⟩ := exists_hasNaturalDensity_finiteExceptionPrimeRule S R h0 h1 hPr hPair
  refine ⟨S,R,e,
    integerBoundedPrimeBlockSet_finiteExceptionPrimeRule hd S R G (fun Q hQ ↦ (hS Q hQ).1)
      hPr hPair (fun Q hQ ↦ (hS Q hQ).2.2),
    kTermGPFree_finiteExceptionPrimeRule (by omega) S R hFree (kTermAPFree_greedyLengthExponents (by omega)),
    he,?_⟩
  have hEq := finiteExceptionPrimeRule_density_eq_greedy_mul hk R hPr hPair he hG
  rw [hEq]
  apply mul_le_mul_of_nonneg_left _ hG₀
  have hAct : (∏ Q ∈ S, primeBlockRuleRatio k Q (R Q)) = ∏ i ∈ I, primeBlockSlotRowScore k x i := by
    rw [show S = I.image P from rfl,prod_image hInj]
    apply prod_congr rfl
    intro i hi
    have hQ : P i ∈ S := mem_image_of_mem _ hi
    rw [show R (P i) = (hPick (P i) hQ).choose from dif_pos hQ]
    exact (hPick (P i) hQ).choose_spec.2 i hi rfl
  rw [hAct]
  have hLe : ∏ i ∈ (univ : Finset (Fin m)) \ I, primeBlockSlotRowScore k x i ≤ 1 := by
    apply prod_le_one (fun i _ ↦ slotRowScore_nonneg (by omega) x i)
    intro i hi
    apply slotRowScore_le_one_of_empty (by omega) hx i
    apply not_nonempty_iff_eq_empty.mp
    exact fun he ↦ (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _,he⟩)
  unfold primeBlockSlotScore
  rw [← prod_sdiff (subset_univ I)]
  exact mul_le_of_le_one_left (prod_nonneg fun i _ ↦ slotRowScore_nonneg (by omega) x i) hLe

end GRHArticle.ProgressionFree
