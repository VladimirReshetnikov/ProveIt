import GRHArticle.ProgressionFree.GreedyBlockWitnesses
import GRHArticle.ProgressionFree.PrimeBlockRuleDensity

/-!
# Reciprocal-mass optimality on light prime blocks

For every accepted nongreedy vector, charge its weight to a missing
greedy predecessor. Each charge is the predecessor's weight multiplied
by the weight of a distinct nonzero increment.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped Classical BigOperators

/-- The reciprocal weight of one exponent pattern at reciprocal prime
weights `u`. -/
noncomputable def reciprocalExponentWeight {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (v : ι → ℕ) : ℝ := ∏ p, u p ^ v p

/-- Total reciprocal weight of the accepted exponent patterns. -/
noncomputable def reciprocalExponentMass {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (F : Set (ι → ℕ)) : ℝ :=
  ∑' v, F.indicator (reciprocalExponentWeight u) v

theorem reciprocalExponentMass_eq_tsum_subtype {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (F : Set (ι → ℕ)) :
    reciprocalExponentMass u F = ∑' v : F, reciprocalExponentWeight u v.val :=
  (_root_.tsum_subtype F _).symm

theorem reciprocalExponentWeight_nonneg {ι : Type*} [Fintype ι] {u : ι → ℝ}
    (hu : ∀ p, 0 ≤ u p) (v : ι → ℕ) : 0 ≤ reciprocalExponentWeight u v :=
  prod_nonneg fun p _ ↦ pow_nonneg (hu p) _

theorem sum_reciprocalExponentWeight_le {ι : Type*} [Fintype ι] {u : ι → ℝ}
    (hu : ∀ p, 0 ≤ u p) (hu' : ∀ p, u p < 1) (T : Finset (ι → ℕ)) :
    (∑ v ∈ T, reciprocalExponentWeight u v) ≤ ∏ p, (1-u p)⁻¹ := by
  let E (p : ι) := T.image (fun v ↦ v p)
  have hs : T ⊆ Fintype.piFinset E := fun v hv ↦
    Fintype.mem_piFinset.mpr (fun p ↦ mem_image_of_mem _ hv)
  refine (sum_le_sum_of_subset_of_nonneg hs (fun v _ _ ↦ reciprocalExponentWeight_nonneg hu v)).trans ?_
  unfold reciprocalExponentWeight
  rw [← Finset.prod_univ_sum]
  refine prod_le_prod (fun p _ ↦ sum_nonneg fun a _ ↦ pow_nonneg (hu p) _) (fun p _ ↦ ?_)
  have h := hasSum_geometric_of_lt_one (hu p) (hu' p)
  exact (h.summable.sum_le_tsum _ (fun _ _ ↦ pow_nonneg (hu p) _)).trans_eq h.tsum_eq

theorem summable_reciprocalExponentWeight {ι : Type*} [Fintype ι] {u : ι → ℝ}
    (hu : ∀ p, 0 ≤ u p) (hu' : ∀ p, u p < 1) : Summable (reciprocalExponentWeight u) :=
  summable_of_sum_le (reciprocalExponentWeight_nonneg hu) (sum_reciprocalExponentWeight_le hu hu')

private theorem mass_inter_add_sdiff {ι : Type*} [Fintype ι] {u : ι → ℝ}
    (h : Summable (reciprocalExponentWeight u)) (F G : Set (ι → ℕ)) :
    reciprocalExponentMass u (F ∩ G) + reciprocalExponentMass u (F \ G) =
      reciprocalExponentMass u F := by
  unfold reciprocalExponentMass
  rw [← Summable.tsum_add
    (summable_subtype_iff_indicator.mp (h.subtype _))
    (summable_subtype_iff_indicator.mp (h.subtype _))]
  apply tsum_congr
  intro v
  by_cases hF : v ∈ F <;> by_cases hG : v ∈ G <;> simp [Set.indicator,hF,hG]

private theorem reciprocalExponentWeight_add {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (v w : ι → ℕ) :
    reciprocalExponentWeight u (v+w) = reciprocalExponentWeight u v * reciprocalExponentWeight u w := by
  simp only [reciprocalExponentWeight, Pi.add_apply, pow_add, prod_mul_distrib]

set_option maxHeartbeats 550000 in
/-- Greedy exponent rules maximize reciprocal mass on every light block.
This is the article's `gpi:prop:light` in exponent coordinates. -/
theorem reciprocalExponentMass_le_greedy_of_light {ι : Type*} [Fintype ι] {k : ℕ}
    (hk : 2 ≤ k) {u : ι → ℝ} (hu : ∀ p, 0 ≤ u p) (hu' : ∀ p, u p < 1)
    (hlight : (∏ p, (1-u p)⁻¹) ≤ 2) {F : Set (ι → ℕ)} (hF : KTermVectorAPFree k F) :
    reciprocalExponentMass u F ≤ reciprocalExponentMass u (greedyExponentPatterns ι k) := by
  let W := reciprocalExponentWeight u
  let G := greedyExponentPatterns ι k
  let E := F \ G
  let M := G \ F
  let Q := ({0} : Set (ι → ℕ))ᶜ
  have hW := summable_reciprocalExponentWeight hu hu'
  have hQ : (∑' q : Q, W q.val) ≤ 1 := by
    have hsum := hW.tsum_le_of_sum_le (sum_reciprocalExponentWeight_le hu hu')
    have hsplit := hW.tsum_subtype_add_tsum_subtype_compl ({0} : Set (ι → ℕ))
    rw [tsum_singleton] at hsplit
    have hzero : W 0 = 1 := by simp [W,reciprocalExponentWeight]
    change W 0 + (∑' q : Q, W q.val) = ∑' v, W v at hsplit
    rw [hzero] at hsplit
    linarith
  choose t ht hle hne using fun v : E ↦
    exists_missing_greedyBlockWitness hk hF v.property.1 v.property.2
  let inc (v : E) : ι → ℕ := v.val - t v
  have hinc (v : E) : t v + inc v = v.val := by
    funext p
    exact Nat.add_sub_of_le (hle v p)
  have hnz (v : E) : inc v ∈ Q := by
    change inc v ∉ ({0} : Set (ι → ℕ))
    intro hv
    have hv0 : inc v = 0 := hv
    exact hne v (by simpa only [hv0,add_zero] using hinc v)
  let e (v : E) : M × Q := (⟨t v,ht v⟩, ⟨inc v,hnz v⟩)
  have he : Function.Injective e := by
    intro a b h
    have h₁ : t a = t b := congrArg (fun z : M × Q ↦ z.1.val) h
    have h₂ : inc a = inc b := congrArg (fun z : M × Q ↦ z.2.val) h
    exact Subtype.ext ((hinc a).symm.trans ((congrArg₂ (·+·) h₁ h₂).trans (hinc b)))
  let cost (v : M × Q) : ℝ := W v.1.val * W v.2.val
  have hnonneg (v : M × Q) : 0 ≤ cost v :=
    mul_nonneg (reciprocalExponentWeight_nonneg hu _) (reciprocalExponentWeight_nonneg hu _)
  have hSM : Summable (fun v : M ↦ W v.val) := hW.subtype _
  have hSQ : Summable (fun v : Q ↦ W v.val) := hW.subtype _
  have hs : Summable cost := by
    apply (summable_prod_of_nonneg (f := cost) hnonneg).2
    refine ⟨fun v : M ↦ hSQ.mul_left (W v.val),?_⟩
    simp only [cost,tsum_mul_left]
    exact hSM.mul_right (∑' v : Q, W v.val)
  have hcharge :
      (∑' v : E, W v.val) ≤ ∑' v : M × Q, cost v := by
    have hSE : Summable (fun v : E ↦ W v.val) := hW.subtype _
    refine Summable.tsum_le_tsum_of_inj e he (fun v _ ↦ hnonneg v) ?_ hSE hs
    intro v
    have hv := congrArg W (hinc v)
    change W (t v + inc v) = W v.val at hv
    rw [show W (t v + inc v) = W (t v) * W (inc v) from reciprocalExponentWeight_add u _ _] at hv
    exact hv.symm.le
  have hb : (∑' v : M × Q, cost v) ≤ ∑' t : M, W t.val := by
    rw [hs.tsum_prod]
    simp only [cost,tsum_mul_left,tsum_mul_right]
    exact mul_le_of_le_one_right (tsum_nonneg fun v : M ↦ reciprocalExponentWeight_nonneg hu v.val) hQ
  have hmass : reciprocalExponentMass u E ≤ reciprocalExponentMass u M := by
    simp only [reciprocalExponentMass_eq_tsum_subtype]
    exact hcharge.trans hb
  have hFsplit := mass_inter_add_sdiff hW F G
  have hGsplit := mass_inter_add_sdiff hW G F
  rw [Set.inter_comm G F] at hGsplit
  change reciprocalExponentMass u (F ∩ G) + reciprocalExponentMass u E = _ at hFsplit
  change reciprocalExponentMass u (F ∩ G) + reciprocalExponentMass u M = _ at hGsplit
  linarith

end GRHArticle.ProgressionFree
