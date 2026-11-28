import GRHArticle.ProgressionFree.PrimeBlockSlotRealization
import Mathlib.Data.Fin.Embedding

/-!
# Packing finite prime rules into a compact configuration

Assign each prime its canonical index in the ordered list of primes.
Unused columns get weight zero and unused rows contribute a factor of one.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped Classical BigOperators OnePoint

private noncomputable def finsetEmbedding {α : Type*} (S : Finset α) {m : ℕ}
    (h : S.card ≤ m) : ↥S ↪ Fin m :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe S)).toEmbedding.trans (Fin.castLEEmb h)

private noncomputable def blockAt {m : ℕ} {S : Finset (Finset ℕ)} (row : ↥S ↪ Fin m) (i : Fin m) :
    Finset ℕ := if hi : i ∈ Set.range row then hi.choose.val else ∅

private theorem blockAt_row {m : ℕ} {S : Finset (Finset ℕ)} (row : ↥S ↪ Fin m) (P : ↥S) :
    blockAt row (row P) = P.val := by
  have h : row P ∈ Set.range row := ⟨P,rfl⟩
  rw [blockAt,dif_pos h,row.injective h.choose_spec]

private theorem blockAt_active {m : ℕ} {S : Finset (Finset ℕ)} (row : ↥S ↪ Fin m)
    {i : Fin m} (hi : i ∈ Set.range row) : blockAt row i ∈ S := by
  rw [blockAt,dif_pos hi]
  exact hi.choose.property

private theorem blockAt_inactive {m : ℕ} {S : Finset (Finset ℕ)} (row : ↥S ↪ Fin m)
    {i : Fin m} (hi : i ∉ Set.range row) : blockAt row i = ∅ := dif_neg hi

private noncomputable def primeLabelAt {d : ℕ} {P : Finset ℕ} (col : ↥P ↪ Fin d) (j : Fin d) :
    OnePoint ℕ :=
  if hj : j ∈ Set.range col then (Nat.count Nat.Prime hj.choose.val : OnePoint ℕ) else ∞

private theorem primeLabelAt_col {d : ℕ} {P : Finset ℕ} (col : ↥P ↪ Fin d) (p : ↥P) :
    primeLabelAt col (col p) = (Nat.count Nat.Prime p.val : OnePoint ℕ) := by
  have h : col p ∈ Set.range col := ⟨p,rfl⟩
  rw [primeLabelAt,dif_pos h,col.injective h.choose_spec]

private theorem primeLabelAt_unused {d : ℕ} {P : Finset ℕ} (col : ↥P ↪ Fin d)
    {j : Fin d} (hj : j ∉ Set.range col) : primeLabelAt col j = ∞ := dif_neg hj

private theorem slotRowScore_padded {k m d : ℕ} (hk : 2 ≤ k)
    (x : PrimeBlockSlotConfiguration m d) (i : Fin m) (P : Finset ℕ)
    (hPr : ∀ p ∈ P, p.Prime) (col : ↥P ↪ Fin d) (R : Set (↥P → ℕ))
    (hLabel : ∀ j, x.1 i j = primeLabelAt col j)
    (hRule : exponentRuleOfCode (x.2 i) = paddedExponentRule col R) :
    primeBlockSlotRowScore k x i = primeBlockRuleRatio k P R := by
  let w (j : Fin d) := (primeSlotWeight (x.1 i j)).val
  have h₀ (j : Fin d) (hj : j ∉ Set.range col) : w j = 0 := by
    simp only [w,hLabel,primeLabelAt_unused col hj,primeSlotWeight_infty]
  have hw (p : ↥P) : w (col p) = 1/(p.val : ℝ) := by
    simp only [w,hLabel,primeLabelAt_col,primeSlotWeight_coe,Nat.nth_count (hPr p.val p.property)]
  unfold primeBlockSlotRowScore
  change reciprocalExponentMass w (exponentRuleOfCode (x.2 i)) /
    reciprocalExponentMass w (greedyExponentPatterns (Fin d) k) = _
  rw [hRule,reciprocalExponentMass_eq_paddedRuleSlice col w h₀ (paddedExponentRule col R),
    reciprocalExponentMass_eq_paddedRuleSlice col w h₀ (greedyExponentPatterns (Fin d) k),
    paddedRuleSlice_paddedExponentRule,paddedRuleSlice_greedyExponentPatterns hk]
  simp_rw [hw]
  unfold primeBlockRuleRatio primeBlockProbability
  have hC : 0 < ∏ p : ↥P, (1-1/(p.val:ℝ)) := by
    apply prod_pos
    intro p _
    have hp := hPr p.val p.property
    exact sub_pos.mpr ((div_lt_one (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hp.one_lt))
  rw [mul_div_mul_left _ _ hC.ne']

private theorem primeLabelAt_eq_of_finite {d : ℕ} {P : Finset ℕ} (col : ↥P ↪ Fin d)
    (hPr : ∀ p ∈ P, p.Prime) {j : Fin d} {n : ℕ}
    (h : primeLabelAt col j = (n : OnePoint ℕ)) :
    ∃ p : ↥P, col p = j ∧ p.val = Nat.nth Nat.Prime n := by
  have hj : j ∈ Set.range col := by
    by_contra he
    rw [primeLabelAt_unused col he] at h
    exact OnePoint.infty_ne_coe n h
  obtain ⟨p,rfl⟩ := hj
  rw [primeLabelAt_col,OnePoint.coe_eq_coe] at h
  rw [← h,Nat.nth_count (hPr p.val p.property)]
  exact ⟨p,rfl,rfl⟩

private theorem packedPrimeLabels_unique {m d : ℕ} {S : Finset (Finset ℕ)}
    (row : ↥S ↪ Fin m) (col : (i : Fin m) → ↥(blockAt row i) ↪ Fin d)
    (hPr : ∀ i p, p ∈ blockAt row i → p.Prime)
    (hPair : (S : Set (Finset ℕ)).PairwiseDisjoint id) :
    ∀ a b : Fin m × Fin d, a ≠ b → ∀ n : ℕ,
      ¬ (primeLabelAt (col a.1) a.2 = (n : OnePoint ℕ) ∧
         primeLabelAt (col b.1) b.2 = (n : OnePoint ℕ)) := by
  have hRow (i : Fin m) (p : ℕ) (hp : p ∈ blockAt row i) : i ∈ Set.range row := by
    by_contra hi
    rw [blockAt_inactive row hi] at hp
    exact notMem_empty _ hp
  rintro ⟨i,j⟩ ⟨r,s⟩ hne n ⟨hi,hr⟩
  obtain ⟨p,hpj,hpn⟩ := primeLabelAt_eq_of_finite (col i) (hPr i) hi
  obtain ⟨q,hqs,hqn⟩ := primeLabelAt_eq_of_finite (col r) (hPr r) hr
  have hpq : p.val = q.val := hpn.trans hqn.symm
  have h₁ := hRow i p.val p.property
  have h₂ := hRow r q.val q.property
  have hBlock : blockAt row i = blockAt row r := by
    by_contra h
    have hD := hPair (blockAt_active row h₁) (blockAt_active row h₂) h
    have hq : p.val ∈ blockAt row r := hpq.symm ▸ q.property
    exact (disjoint_left.mp hD) p.property hq
  have hir : i = r := by
    obtain ⟨u,hu⟩ := h₁
    obtain ⟨v,hv⟩ := h₂
    have he : blockAt row (row u) = blockAt row (row v) := by rw [hu,hv,hBlock]
    rw [blockAt_row,blockAt_row] at he
    exact hu.symm.trans ((congrArg row (Subtype.ext he)).trans hv)
  subst r
  have he : p = q := Subtype.ext hpq
  exact hne (congrArg (Prod.mk i) (hpj.symm.trans ((congrArg (fun z ↦ col i z) he).trans hqs)))

private noncomputable def packedExponentRule {m d : ℕ} {S : Finset (Finset ℕ)}
    (k : ℕ) (row : ↥S ↪ Fin m) (col : (i : Fin m) → ↥(blockAt row i) ↪ Fin d)
    (R : (P : Finset ℕ) → Set (↥P → ℕ)) (i : Fin m) : Set (Fin d → ℕ) :=
  if i ∈ Set.range row then paddedExponentRule (col i) (R (blockAt row i))
  else greedyExponentPatterns (Fin d) k

private noncomputable def packedConfiguration {m d : ℕ} {S : Finset (Finset ℕ)}
    (k : ℕ) (row : ↥S ↪ Fin m) (col : (i : Fin m) → ↥(blockAt row i) ↪ Fin d)
    (R : (P : Finset ℕ) → Set (↥P → ℕ)) : PrimeBlockSlotConfiguration m d :=
  (fun i j ↦ primeLabelAt (col i) j,fun i v ↦ if v ∈ packedExponentRule k row col R i then 1 else 0)

private theorem primeAtBlockAt {m : ℕ} {S : Finset (Finset ℕ)} (row : ↥S ↪ Fin m)
    (hPr : ∀ P ∈ S, ∀ p ∈ P, p.Prime) (i : Fin m) (p : ℕ) (hp : p ∈ blockAt row i) : p.Prime := by
  by_cases hi : i ∈ Set.range row
  · exact hPr _ (blockAt_active row hi) p hp
  · rw [blockAt_inactive row hi] at hp
    exact (notMem_empty _ hp).elim

private theorem packedConfiguration_rule {k m d : ℕ} {S : Finset (Finset ℕ)}
    (row : ↥S ↪ Fin m) (col : (i : Fin m) → ↥(blockAt row i) ↪ Fin d)
    (R : (P : Finset ℕ) → Set (↥P → ℕ)) (i : Fin m) :
    exponentRuleOfCode ((packedConfiguration k row col R).2 i) = packedExponentRule k row col R i :=
  exponentRuleOfCode_indicator _

private theorem packedConfiguration_valid {k m d : ℕ} {S : Finset (Finset ℕ)} (hk : 2 ≤ k)
    (row : ↥S ↪ Fin m) (col : (i : Fin m) → ↥(blockAt row i) ↪ Fin d)
    (R : (P : Finset ℕ) → Set (↥P → ℕ))
    (hPr : ∀ P ∈ S, ∀ p ∈ P, p.Prime)
    (hPair : (S : Set (Finset ℕ)).PairwiseDisjoint id)
    (hFree : ∀ P ∈ S, KTermVectorAPFree k (R P)) :
    ValidPrimeBlockSlotConfiguration k (packedConfiguration k row col R) := by
  refine ⟨?_,fun i ↦ ?_⟩
  · dsimp only [packedConfiguration]
    exact packedPrimeLabels_unique row col (primeAtBlockAt row hPr) hPair
  · rw [packedConfiguration_rule,packedExponentRule]
    split_ifs with hi
    · exact kTermVectorAPFree_paddedExponentRule hk (col i) (hFree _ (blockAt_active row hi))
    · exact kTermVectorAPFree_greedyExponentPatterns _ hk

private theorem packedConfiguration_score_active {k m d : ℕ} {S : Finset (Finset ℕ)} (hk : 2 ≤ k)
    (row : ↥S ↪ Fin m) (col : (i : Fin m) → ↥(blockAt row i) ↪ Fin d)
    (R : (P : Finset ℕ) → Set (↥P → ℕ))
    (hPr : ∀ P ∈ S, ∀ p ∈ P, p.Prime) (i : Fin m) (hi : i ∈ Set.range row) :
    primeBlockSlotRowScore k (packedConfiguration k row col R) i =
      primeBlockRuleRatio k (blockAt row i) (R (blockAt row i)) := by
  have hLabel (j : Fin d) : (packedConfiguration k row col R).1 i j = primeLabelAt (col i) j := by
    simp only [packedConfiguration]
  have hRule : exponentRuleOfCode ((packedConfiguration k row col R).2 i) =
      paddedExponentRule (col i) (R (blockAt row i)) := by
    rw [packedConfiguration_rule,packedExponentRule,if_pos hi]
  exact @slotRowScore_padded k m d hk (packedConfiguration k row col R) i (blockAt row i)
    (primeAtBlockAt row hPr i) (col i) (R (blockAt row i)) hLabel hRule

private theorem packedConfiguration_score_inactive {k m d : ℕ} {S : Finset (Finset ℕ)} (hk : 2 ≤ k)
    (row : ↥S ↪ Fin m) (col : (i : Fin m) → ↥(blockAt row i) ↪ Fin d)
    (R : (P : Finset ℕ) → Set (↥P → ℕ)) (i : Fin m) (hi : i ∉ Set.range row) :
    primeBlockSlotRowScore k (packedConfiguration k row col R) i = 1 := by
  unfold primeBlockSlotRowScore
  rw [packedConfiguration_rule,packedExponentRule,if_neg hi]
  apply div_self
  exact ne_of_gt (zero_lt_one.trans_le (one_le_reciprocalExponentMass_greedy hk _))

private theorem packedConfiguration_score {k m d : ℕ} {S : Finset (Finset ℕ)} (hk : 2 ≤ k)
    (row : ↥S ↪ Fin m) (col : (i : Fin m) → ↥(blockAt row i) ↪ Fin d)
    (R : (P : Finset ℕ) → Set (↥P → ℕ))
    (hPr : ∀ P ∈ S, ∀ p ∈ P, p.Prime) :
    primeBlockSlotScore k (packedConfiguration k row col R) =
      ∏ P ∈ S, primeBlockRuleRatio k P (R P) := by
  let f (i : Fin m) := primeBlockSlotRowScore k (packedConfiguration k row col R) i
  change (∏ i, f i) = _
  calc
    _ = ∏ i ∈ (univ : Finset ↥S).map row, f i := by
      symm
      apply prod_subset (subset_univ _)
      intro i _ hi
      apply packedConfiguration_score_inactive hk row col R i
      rintro ⟨P,rfl⟩
      exact hi (mem_map.mpr ⟨P,mem_univ _,rfl⟩)
    _ = ∏ P : ↥S, primeBlockRuleRatio k P.val (R P.val) := by
      rw [prod_map]
      apply prod_congr rfl
      intro P _
      rw [show f (row P) = _ from packedConfiguration_score_active hk row col R hPr (row P) ⟨P,rfl⟩,
        blockAt_row]
    _ = _ := by rw [univ_eq_attach,prod_attach S (fun P ↦ primeBlockRuleRatio k P (R P))]

/-- Any finite family of disjoint blocks with sufficiently many rows and
columns fits into a compact configuration without changing its score. -/
theorem exists_primeBlockSlotScore_eq_prod {k m d : ℕ} (hk : 2 ≤ k)
    (S : Finset (Finset ℕ)) (R : (P : Finset ℕ) → Set (↥P → ℕ))
    (hCard : S.card ≤ m) (hWidth : ∀ P ∈ S, P.card ≤ d)
    (hPr : ∀ P ∈ S, ∀ p ∈ P, p.Prime)
    (hPair : (S : Set (Finset ℕ)).PairwiseDisjoint id)
    (hFree : ∀ P ∈ S, KTermVectorAPFree k (R P)) :
    ∃ x : PrimeBlockSlotConfiguration m d, ValidPrimeBlockSlotConfiguration k x ∧
      primeBlockSlotScore k x = ∏ P ∈ S, primeBlockRuleRatio k P (R P) := by
  let row : ↥S ↪ Fin m := finsetEmbedding S hCard
  let P (i : Fin m) : Finset ℕ := blockAt row i
  have hWidthAt (i : Fin m) : (P i).card ≤ d := by
    by_cases hi : i ∈ Set.range row
    · exact hWidth _ (blockAt_active row hi)
    · change (blockAt row i).card ≤ d
      rw [blockAt_inactive row hi,card_empty]
      exact Nat.zero_le d
  let col (i : Fin m) : ↥(P i) ↪ Fin d := finsetEmbedding (P i) (hWidthAt i)
  exact ⟨packedConfiguration k row col R,packedConfiguration_valid hk row col R hPr hPair hFree,
    packedConfiguration_score hk row col R hPr⟩

end GRHArticle.ProgressionFree
