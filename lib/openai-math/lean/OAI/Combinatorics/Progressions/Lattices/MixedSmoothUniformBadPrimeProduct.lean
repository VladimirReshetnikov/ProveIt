/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.RingTheory.Coprime.Lemmas
import OAI.Combinatorics.Progressions.Estimates.FiniteFiberPMF
import OAI.Combinatorics.Progressions.Lattices.SmoothBadPrimeProduct

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem uniform_fiberLaw_surjective_hom {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) :
    (FiniteProbabilityWeights.uniform G).fiberLaw f =
      FiniteProbabilityWeights.uniform H := by
  apply FiniteProbabilityWeights.eq_of_weight_eq
  intro y
  have hh := uniform_mean_surjective_hom_fiber f hf y
  change _ = (Fintype.card H : ℝ)⁻¹
  convert hh using 1
  unfold FiniteProbabilityWeights.fiberLaw FiniteProbabilityWeights.fiberMean
  congr 1

theorem uniform_complexMean_surjective_hom {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (g : H → ℂ) :
    (FiniteProbabilityWeights.uniform G).complexMean (fun x => g (f x)) =
      (FiniteProbabilityWeights.uniform H).complexMean g := by
  rw [← FiniteProbabilityWeights.fiberLaw_complexMean,
    uniform_fiberLaw_surjective_hom f hf]

theorem uniform_tupleResidueReduction_fiberLaw {D : Type*}
    [Fintype D] [DecidableEq D] {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) :
    (FiniteProbabilityWeights.uniform (D → ZMod N)).fiberLaw (tupleResidueReduction hMN) =
      FiniteProbabilityWeights.uniform (D → ZMod M) :=
  uniform_fiberLaw_surjective_hom (tupleResidueReduction hMN)
    (tupleResidueReduction_surjective hMN)

theorem uniform_tupleResidueReduction_mean {D : Type*}
    [Fintype D] [DecidableEq D] {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (g : (D → ZMod M) → ℝ) :
    (FiniteProbabilityWeights.uniform (D → ZMod N)).mean
      (fun x => g (tupleResidueReduction hMN x)) =
      (FiniteProbabilityWeights.uniform (D → ZMod M)).mean g :=
  uniform_mean_surjective_hom (tupleResidueReduction hMN)
    (tupleResidueReduction_surjective hMN) g

theorem uniform_tupleResidueReduction_complexMean {D : Type*}
    [Fintype D] [DecidableEq D] {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (g : (D → ZMod M) → ℂ) :
    (FiniteProbabilityWeights.uniform (D → ZMod N)).complexMean
      (fun x => g (tupleResidueReduction hMN x)) =
      (FiniteProbabilityWeights.uniform (D → ZMod M)).complexMean g :=
  uniform_complexMean_surjective_hom (tupleResidueReduction hMN)
    (tupleResidueReduction_surjective hMN) g

theorem expect_tupleResidueReduction {D : Type*}
    [Fintype D] [DecidableEq D] {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (g : (D → ZMod M) → ℝ) :
    (𝔼 x : D → ZMod N, g (tupleResidueReduction hMN x)) =
      𝔼 y : D → ZMod M, g y := by
  simpa only [FiniteProbabilityWeights.uniform_mean] using
    uniform_tupleResidueReduction_mean hMN g

theorem uniform_tupleResidueReduction_toPMF_map {D : Type*}
    [Fintype D] [DecidableEq D] {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) :
    (FiniteProbabilityWeights.uniform (D → ZMod N)).toPMF.map (tupleResidueReduction hMN) =
      (FiniteProbabilityWeights.uniform (D → ZMod M)).toPMF := by
  rw [← FiniteProbabilityWeights.toPMF_fiberLaw,
    uniform_tupleResidueReduction_fiberLaw hMN]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open FiniteProbabilityWeights

theorem finiteWeights_prod_same_l1 {X Y : Type*} [Fintype X] [Fintype Y]
    (p q : FiniteProbabilityWeights X) (u : FiniteProbabilityWeights Y) :
    (∑ z : X × Y, |(p.prod u).weight z - (q.prod u).weight z|) =
      ∑ x : X, |p.weight x - q.weight x| := by
  simp only [FiniteProbabilityWeights.prod, ← sub_mul, abs_mul,
    abs_of_nonneg (u.nonneg _), Fintype.sum_prod_type, ← Finset.mul_sum,
    u.total, mul_one]

def mixedResidueArrayEquiv (J D R : Type*) : ((J → R) × (D → R)) ≃ ((J ⊕ D) → R) where
  toFun p := Sum.elim p.1 p.2
  invFun f := (fun j => f (.inl j), fun d => f (.inr d))
  left_inv _ := rfl
  right_inv f := by funext t; cases t <;> rfl

private theorem uniform_pair_sum_complexMean {J D : Type*} [Fintype J] [Fintype D]
    (M : ℕ) [NeZero M] (f : ((J ⊕ D) → ZMod M) → ℂ) :
    ((uniform (J → ZMod M)).prod (uniform (D → ZMod M))).complexMean
      (fun p => f (Sum.elim p.1 p.2)) =
      (uniform ((J ⊕ D) → ZMod M)).complexMean f := by
  rw [complexMean_prod]
  simp_rw [uniform_complexMean]
  have hprod := Finset.expect_product' (Finset.univ : Finset (J → ZMod M))
    (Finset.univ : Finset (D → ZMod M)) (fun x y => f (Sum.elim x y))
  rw [Finset.univ_product_univ] at hprod
  rw [← hprod]
  exact Fintype.expect_equiv (mixedResidueArrayEquiv J D (ZMod M)) _ _ (fun _ => rfl)

theorem mixedSmoothUniform_residue_complexMean_eq {J D : Type*} [Fintype J] [Fintype D]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) (hZ : 0 < shiftedSmoothProductMass a S)
    {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (f : ((J ⊕ D) → ZMod M) → ℂ) :
    ((shiftedSmoothProductFiniteWeights a S hS hZ).prod (uniform (D → ZMod N))).complexMean
      (fun z => f (Sum.elim (fun j => (z.1.val j : ZMod M))
        (fun d => ZMod.castHom hMN (ZMod M) (z.2 d)))) =
    ((ofPMF ((shiftedSmoothProductPMF a S hS hZ).map
      (fun x j => (x j : ZMod M)))).prod (uniform (D → ZMod M))).complexMean
      (fun z => f (Sum.elim z.1 z.2)) := by
  rw [complexMean_prod, complexMean_prod]
  have hred (x : J → ZMod M) :
      (uniform (D → ZMod N)).complexMean (fun y => f (Sum.elim x
        (fun d => ZMod.castHom hMN (ZMod M) (y d)))) =
      (uniform (D → ZMod M)).complexMean (fun y => f (Sum.elim x y)) :=
    uniform_tupleResidueReduction_complexMean hMN (fun y => f (Sum.elim x y))
  simp_rw [hred]
  exact shiftedSmoothProductFiniteWeights_map_complexMean a S hS hZ
    (fun x j => (x j : ZMod M)) (fun x => (uniform (D → ZMod M)).complexMean
      (fun y => f (Sum.elim x y)))

theorem mixedSmoothUniform_residue_l1 {J D : Type*} [Fintype J] [Fintype D]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) (hZ : 0 < shiftedSmoothProductMass a S)
    (M : ℕ) [NeZero M]
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) * M ≤ S j) :
    (∑ z : (J → ZMod M) × (D → ZMod M),
      |((ofPMF ((shiftedSmoothProductPMF a S hS hZ).map
          (fun x j => (x j : ZMod M)))).prod (uniform (D → ZMod M))).weight z -
        ((uniform (J → ZMod M)).prod (uniform (D → ZMod M))).weight z|) ≤
      ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * M / S j := by
  rw [finiteWeights_prod_same_l1]
  exact shiftedSmoothProductPMF_residue_l1 a S hS hZ M hlarge

theorem mixedSmoothUniform_residue_complexMean_error {J D : Type*} [Fintype J] [Fintype D]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) (hZ : 0 < shiftedSmoothProductMass a S)
    {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) * M ≤ S j)
    (f : ((J ⊕ D) → ZMod M) → ℂ) (hf : ∀ r, ‖f r‖ ≤ 1) :
    ‖((shiftedSmoothProductFiniteWeights a S hS hZ).prod (uniform (D → ZMod N))).complexMean
      (fun z => f (Sum.elim (fun j => (z.1.val j : ZMod M))
        (fun d => ZMod.castHom hMN (ZMod M) (z.2 d)))) -
      (uniform ((J ⊕ D) → ZMod M)).complexMean f‖ ≤
      ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * M / S j := by
  rw [mixedSmoothUniform_residue_complexMean_eq a S hS hZ hMN,
    ← uniform_pair_sum_complexMean M f]
  let p : FiniteProbabilityWeights (J → ZMod M) :=
    ofPMF ((shiftedSmoothProductPMF a S hS hZ).map (fun x j => (x j : ZMod M)))
  let q : FiniteProbabilityWeights (J → ZMod M) := uniform (J → ZMod M)
  let u : FiniteProbabilityWeights (D → ZMod M) := uniform (D → ZMod M)
  let g : (J → ZMod M) × (D → ZMod M) → ℂ := fun z => f (Sum.elim z.1 z.2)
  have hg : ∀ z, ‖g z‖ ≤ 1 := fun z => hf (Sum.elim z.1 z.2)
  have htest := norm_complexMean_sub_le_weight_l1 (p.prod u) (q.prod u) g hg
  have hweight : (∑ z, |(p.prod u).weight z - (q.prod u).weight z|) ≤
      ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * M / S j :=
    mixedSmoothUniform_residue_l1 (D := D) a S hS hZ M hlarge
  exact htest.trans hweight

private theorem complexMean_indicator_eq_event {T : Type*} [Fintype T]
    (p : FiniteProbabilityWeights T) (E : T → Prop) :
    p.complexMean (fun x => if E x then (1 : ℂ) else 0) = (p.eventProbability E : ℂ) := by
  simp only [complexMean, eventProbability, mean, Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

theorem mixedSmoothUniform_residue_event_error {J D : Type*} [Fintype J] [Fintype D]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) (hZ : 0 < shiftedSmoothProductMass a S)
    {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) * M ≤ S j)
    (E : ((J ⊕ D) → ZMod M) → Prop) :
    |((shiftedSmoothProductFiniteWeights a S hS hZ).prod (uniform (D → ZMod N))).eventProbability
      (fun z => E (Sum.elim (fun j => (z.1.val j : ZMod M))
        (fun d => ZMod.castHom hMN (ZMod M) (z.2 d)))) -
      (uniform ((J ⊕ D) → ZMod M)).eventProbability E| ≤
      ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * M / S j := by
  have h := mixedSmoothUniform_residue_complexMean_error a S hS hZ hMN hlarge
    (fun r => if E r then (1 : ℂ) else 0) (fun r => by split_ifs <;> norm_num)
  rw [complexMean_indicator_eq_event, complexMean_indicator_eq_event,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

theorem mixedSmoothUniform_residue_event_error_of_width
    {J D : Type*} [Fintype J] [Fintype D]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) (hZ : 0 < shiftedSmoothProductMass a S)
    {B W η : ℝ} (hW : 0 < W) (hwidth : ∀ j, W ≤ S j)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) * B ≤ W)
    (herror : (Fintype.card J : ℝ) *
      (16 * (probabilityProfileLipschitz : ℝ) * B / W) ≤ η)
    {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N) (hM : (M : ℝ) ≤ B)
    (E : ((J ⊕ D) → ZMod M) → Prop) :
    |((shiftedSmoothProductFiniteWeights a S hS hZ).prod (uniform (D → ZMod N))).eventProbability
      (fun z => E (Sum.elim (fun j => (z.1.val j : ZMod M))
        (fun d => ZMod.castHom hMN (ZMod M) (z.2 d)))) -
      (uniform ((J ⊕ D) → ZMod M)).eventProbability E| ≤ η := by
  have hB : 0 ≤ B := (Nat.cast_nonneg M).trans hM
  have hscale (j) : 8 * (probabilityProfileLipschitz : ℝ) * M ≤ S j :=
    ((mul_le_mul_of_nonneg_left hM (by positivity)).trans hlarge).trans (hwidth j)
  apply (mixedSmoothUniform_residue_event_error a S hS hZ hMN hscale E).trans
  calc
    _ ≤ ∑ _j : J, 16 * (probabilityProfileLipschitz : ℝ) * B / W := by
      apply Finset.sum_le_sum
      intro j _
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hM (by positivity))
        hW (hwidth j)
    _ ≤ η := by
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using herror

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem FiniteProbabilityWeights.fiberLaw_comp {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (p : FiniteProbabilityWeights X) (f : X → Y) (g : Y → Z) :
    (p.fiberLaw f).fiberLaw g = p.fiberLaw (g ∘ f) := by
  apply FiniteProbabilityWeights.eq_of_weight_eq
  intro z
  change (p.fiberLaw f).mean (fun y => if g y = z then (1 : ℝ) else 0) =
    p.mean (fun x => if g (f x) = z then (1 : ℝ) else 0)
  exact p.fiberLaw_mean f _

theorem uniform_tupleResidueReduction_fiberLaw_postcompose {D Y : Type*}
    [Fintype D] [DecidableEq D] [Fintype Y]
    {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (f : (D → ZMod M) → Y) :
    (FiniteProbabilityWeights.uniform (D → ZMod N)).fiberLaw
        (fun x => f (tupleResidueReduction hMN x)) =
      (FiniteProbabilityWeights.uniform (D → ZMod M)).fiberLaw f := by
  rw [← uniform_tupleResidueReduction_fiberLaw hMN,
    FiniteProbabilityWeights.fiberLaw_comp]
  rfl

theorem tupleResidueReduction_affine {D : Type*} {M N : ℕ}
    (hMN : M ∣ N) (a x : D → ZMod N) (step : ℕ) :
    tupleResidueReduction hMN (fun d => a d + (step : ZMod N) * x d) =
      fun d => tupleResidueReduction hMN a d +
        (step : ZMod M) * tupleResidueReduction hMN x d := by
  funext d
  change ZMod.castHom hMN (ZMod M) (a d + (step : ZMod N) * x d) = _
  simp only [map_add, map_mul, map_natCast]
  rfl

theorem uniform_affine_tupleResidueReduction_fiberLaw {D : Type*}
    [Fintype D] [DecidableEq D] {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (a : D → ZMod N) (step : ℕ) :
    ((FiniteProbabilityWeights.uniform (D → ZMod N)).fiberLaw
        (fun x d => a d + (step : ZMod N) * x d)).fiberLaw
          (tupleResidueReduction hMN) =
      (FiniteProbabilityWeights.uniform (D → ZMod M)).fiberLaw
        (fun y d => tupleResidueReduction hMN a d + (step : ZMod M) * y d) := by
  rw [FiniteProbabilityWeights.fiberLaw_comp]
  simp only [Function.comp_def, tupleResidueReduction_affine]
  exact uniform_tupleResidueReduction_fiberLaw_postcompose (D := D) hMN
    (fun y d => tupleResidueReduction hMN a d + (step : ZMod M) * y d)

theorem uniform_affine_tupleResidueReduction_complexMean {D : Type*}
    [Fintype D] [DecidableEq D] {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (a : D → ZMod N) (step : ℕ)
    (f : (D → ZMod M) → ℂ) :
    (FiniteProbabilityWeights.uniform (D → ZMod N)).complexMean
        (fun x => f (tupleResidueReduction hMN
          (fun d => a d + (step : ZMod N) * x d))) =
      (FiniteProbabilityWeights.uniform (D → ZMod M)).complexMean
        (fun y => f (fun d => tupleResidueReduction hMN a d +
          (step : ZMod M) * y d)) := by
  simp only [tupleResidueReduction_affine]
  exact uniform_tupleResidueReduction_complexMean (D := D) hMN
    (fun y => f (fun d => tupleResidueReduction hMN a d + (step : ZMod M) * y d))

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open FiniteProbabilityWeights

theorem selectedPrimePower_product_dvd (S : Finset ℕ) (a : ℕ → ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) {N : ℕ}
    (hcover : ∀ p ∈ S, p ^ a p ∣ N) :
    (∏ p : S, p.val ^ a p) ∣ N := by
  apply Fintype.prod_dvd_of_isRelPrime
  · intro p q hpq
    exact Nat.coprime_iff_isRelPrime.mp (selectedPrimePower_coprime S a hprime hpq)
  · intro p
    exact hcover p p.property

theorem coefficientCRTEquiv_mixed_reduction {L J D : Type*} [Fintype L]
    (q : L → ℕ) (hq : Pairwise (fun l k => (q l).Coprime (q k)))
    {N : ℕ} (hMN : (∏ l, q l) ∣ N) (x : J → ℤ) (r : D → ZMod N) :
    coefficientCRTEquiv q hq
      (Sum.elim (fun j => (x j : ZMod (∏ l, q l)))
        (fun d => ZMod.castHom hMN (ZMod (∏ l, q l)) (r d))) =
      (fun l => Sum.elim (fun j => (x j : ZMod (q l)))
        (fun d => ZMod.cast (r d))) := by
  funext l k
  cases k with
  | inl j =>
    rw [coefficientCRTEquiv_apply]
    exact map_intCast _ _
  | inr d =>
    rw [coefficientCRTEquiv_apply]
    change ZMod.castHom _ (ZMod (q l))
      (ZMod.castHom hMN (ZMod (∏ l, q l)) (r d)) = ZMod.cast (r d)
    rw [← RingHom.comp_apply, ZMod.castHom_comp, ZMod.castHom_apply]

private theorem uniform_event_fintype_congr {X : Type*} [Nonempty X]
    (i₁ i₂ : Fintype X) (E : X → Prop) :
    @eventProbability X i₁ (@uniform X i₁ inferInstance) E =
      @eventProbability X i₂ (@uniform X i₂ inferInstance) E := by
  cases Subsingleton.elim i₁ i₂
  rfl

theorem mixedSmoothUniform_primePower_event
    {J D : Type*} [Fintype J] [Fintype D] {N : ℕ} [NeZero N]
    (center width : J → ℝ) (hwidth : ∀ j, 0 < width j)
    (hZ : 0 < shiftedSmoothProductMass center width)
    (S : Finset ℕ) (a : ℕ → ℕ) (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcover : ∀ p ∈ S, p ^ a p ∣ N)
    [∀ p : S, NeZero (p.val ^ a p)]
    (E : ∀ p : S, ((J ⊕ D) → ZMod (p.val ^ a p)) → Prop)
    (hprob : ∀ p : S,
      (uniform ((J ⊕ D) → ZMod (p.val ^ a p))).eventProbability (E p) ≤
        1 / ((p.val ^ a p : ℕ) : ℝ) ^ 10)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) * (∏ p : S, p.val ^ a p) ≤ width j) :
    ((shiftedSmoothProductFiniteWeights center width hwidth hZ).prod
      (uniform (D → ZMod N))).eventProbability
        (fun x => ∀ p : S, E p (Sum.elim
          (fun j => (x.1.val j : ZMod (p.val ^ a p)))
          (fun d => ZMod.cast (x.2 d)))) ≤
      1 / ((∏ p : S, p.val ^ a p : ℕ) : ℝ) ^ 10 +
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (∏ p : S, p.val ^ a p) / width j := by
  let : NeZero (∏ p : S, p.val ^ a p) := ⟨(selectedPrimePower_nonzero S a hprime).2⟩
  let q : S → ℕ := fun p => p.val ^ a p
  let hq := selectedPrimePower_coprime S a hprime
  have hMN : (∏ p : S, q p) ∣ N := selectedPrimePower_product_dvd S a hprime hcover
  let F : ((J ⊕ D) → ZMod (∏ p : S, q p)) → Prop :=
    fun y => ∀ p : S, E p (coefficientCRTEquiv q hq y p)
  have htransfer := mixedSmoothUniform_residue_event_error center width hwidth hZ hMN hlarge F
  have hF (x : rectangularWeightIndices center width 1 × (D → ZMod N)) :
      F (Sum.elim (fun j => (x.1.val j : ZMod (∏ p : S, q p)))
        (fun d => ZMod.castHom hMN (ZMod (∏ p : S, q p)) (x.2 d))) =
      (∀ p : S, E p (Sum.elim (fun j => (x.1.val j : ZMod (p.val ^ a p)))
        (fun d => ZMod.cast (x.2 d)))) := by
    unfold F
    rw [coefficientCRTEquiv_mixed_reduction]
  simp only [hF] at htransfer
  have huniform : (uniform ((J ⊕ D) → ZMod (∏ p : S, q p))).eventProbability F ≤
      1 / ((∏ p : S, p.val ^ a p : ℕ) : ℝ) ^ 10 := by
    have hu : (uniform ((J ⊕ D) → ZMod (∏ p : S, q p))).eventProbability F =
        ∏ p : S, (uniform ((J ⊕ D) → ZMod (q p))).eventProbability (E p) := by
      convert uniform_coefficientCRT_event q hq E using 1
      · exact uniform_event_fintype_congr _ _ _
      · apply Finset.prod_congr rfl
        intro p _
        exact uniform_event_fintype_congr _ _ _
    rw [hu]
    calc
      _ ≤ ∏ p : S, 1 / ((p.val ^ a p : ℕ) : ℝ) ^ 10 :=
        Finset.prod_le_prod₀ (fun p _ => (uniform _).eventProbability_nonneg (E p))
          (fun p _ => hprob p)
      _ = _ := by
        simp only [one_div, ← Finset.prod_inv_distrib, ← Finset.prod_pow, Nat.cast_prod]
  have hupper := (abs_le.mp htransfer).2
  dsimp only [q] at hupper huniform
  linarith only [hupper, huniform]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open FiniteProbabilityWeights

def mixedSmoothUniformResiduePrimeBad {J D : Type*} {N : ℕ} (P : Finset ℕ)
    (E : ∀ p : P, ∀ a : ℕ, ((J ⊕ D) → ZMod (p.val ^ a)) → Prop)
    (p a : ℕ) (x : (J → ℤ) × (D → ZMod N)) : Prop :=
  ∃ hp : p ∈ P, E ⟨p, hp⟩ a
    (Sum.elim (fun j => (x.1 j : ZMod (p ^ a))) (fun d => ZMod.cast (x.2 d)))

theorem mixedSmoothUniform_badPrimeProduct_probability
    {J D : Type*} [Fintype J] [Fintype D] {N : ℕ} [NeZero N]
    (center width : J → ℝ) (hwidth : ∀ j, 0 < width j)
    (hZ : 0 < shiftedSmoothProductMass center width)
    (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
    (E : ∀ p : P, ∀ a : ℕ, ((J ⊕ D) → ZMod (p.val ^ a)) → Prop)
    {Qs Q R : ℕ} (hprime : ∀ p ∈ P, p.Prime)
    (hcover : ∀ p ∈ P, p ^ A p ∣ N)
    (hQs : 2 ≤ Qs) (hQ : 1 ≤ Q) (hR : 0 < R)
    (hdepth : ∀ p ∈ P, p ^ A p ≤ Q)
    (hprob : ∀ (p : P) a, 0 < a → a ≤ A p → Qs ≤ p.val ^ a →
      (uniform ((J ⊕ D) → ZMod (p.val ^ a))).eventProbability (E p a) ≤
        1 / ((p.val ^ a : ℕ) : ℝ) ^ 10)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) *
      (max Q (R ^ 2) : ℕ) ≤ width j)
    {η : ℝ} (hη : 0 ≤ η)
    (herror : (∑ j, 16 * (probabilityProfileLipschitz : ℝ) *
      (max Q (R ^ 2) : ℕ) / width j) ≤ η) :
    ((shiftedSmoothProductFiniteWeights center width hwidth hZ).prod
      (uniform (D → ZMod N))).eventProbability
      (fun x => smallPrimePowerCorrection Qs * R <
        ∏ p ∈ P, p ^ largestTestedBadDepth A
          (fun p a x => mixedSmoothUniformResiduePrimeBad P E p a (x.1.val, x.2)) p x) ≤
      2 / (9 * (R : ℝ) ^ 9) + ((Q : ℝ) + (R : ℝ) ^ 2) * η := by
  apply largestBadPrimeProduct_probability_bounded _ P A _ hprime hQs hQ hR hdepth hη
  intro T hTP a ha hd
  let (p : T) : NeZero (p.val ^ a p) :=
    ⟨pow_ne_zero _ (hprime p (hTP p.property)).ne_zero⟩
  let F (p : T) := E ⟨p.val, hTP p.property⟩ (a p)
  have hprod : (∏ p : T, p.val ^ a p) = ∏ p ∈ T, p ^ a p :=
    Finset.prod_coe_sort T (fun p => p ^ a p)
  have hd' : (∏ p : T, p.val ^ a p) ≤ max Q (R ^ 2) := by
    rw [hprod]
    exact hd
  have hs (j) : 8 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : T, p.val ^ a p) ≤ width j :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hd') (by positivity)).trans (hlarge j)
  have h := mixedSmoothUniform_primePower_event (D := D) (N := N)
    center width hwidth hZ T a (fun p hp => hprime p (hTP hp))
    (fun p hp => (pow_dvd_pow p (ha p hp).2.1).trans (hcover p (hTP hp))) F
    (fun p => hprob ⟨p.val, hTP p.property⟩ (a p) (ha p p.property).1
      (ha p p.property).2.1 (ha p p.property).2.2) hs
  have hevents :
      (fun x : rectangularWeightIndices center width 1 × (D → ZMod N) =>
        ∀ p ∈ T, mixedSmoothUniformResiduePrimeBad P E p (a p) (x.1.val, x.2)) =
      (fun x => ∀ p : T, F p
        (Sum.elim (fun j => (x.1.val j : ZMod (p.val ^ a p)))
          (fun d => ZMod.cast (x.2 d)))) := by
    funext x
    apply propext
    constructor
    · intro hx p
      obtain ⟨hp, he⟩ := hx p p.property
      exact he
    · intro hx p hp
      exact ⟨hTP hp, hx ⟨p, hp⟩⟩
  rw [hevents]
  have herr : (∑ j, 16 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : T, p.val ^ a p) / width j) ≤ η := by
    apply le_trans (Finset.sum_le_sum (fun j _ => ?_)) herror
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hd') (by positivity)) (hwidth j).le
  rw [hprod] at h herr
  exact h.trans (add_le_add le_rfl herr)

theorem exists_early_mixedSmoothUniform_badPrimeProduct_cutoff
    (Qs : ℕ) (hQs : 2 ≤ Qs) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℕ, 0 < R ∧ ∀ (J D : Type*) [Fintype J] [Fintype D]
      (N : ℕ) [NeZero N]
      (center width : J → ℝ) (hwidth : ∀ j, 0 < width j)
      (hZ : 0 < shiftedSmoothProductMass center width)
      (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
      (E : ∀ p : P, ∀ a : ℕ, ((J ⊕ D) → ZMod (p.val ^ a)) → Prop) (Q : ℕ),
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ^ A p ∣ N) →
      1 ≤ Q → (∀ p ∈ P, p ^ A p ≤ Q) →
      (∀ (p : P) a, 0 < a → a ≤ A p → Qs ≤ p.val ^ a →
        (uniform ((J ⊕ D) → ZMod (p.val ^ a))).eventProbability (E p a) ≤
          1 / ((p.val ^ a : ℕ) : ℝ) ^ 10) →
      (∀ j, 8 * (probabilityProfileLipschitz : ℝ) *
        (max Q (R ^ 2) : ℕ) ≤ width j) →
      (∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (max Q (R ^ 2) : ℕ) / width j) ≤
        δ / (2 * ((Q : ℝ) + (R : ℝ) ^ 2)) →
      ((shiftedSmoothProductFiniteWeights center width hwidth hZ).prod
        (uniform (D → ZMod N))).eventProbability
        (fun x => smallPrimePowerCorrection Qs * R <
          ∏ p ∈ P, p ^ largestTestedBadDepth A
            (fun p a x => mixedSmoothUniformResiduePrimeBad P E p a (x.1.val, x.2)) p x) ≤ δ := by
  obtain ⟨R, hR, hradius⟩ := exists_early_badPrime_radius hδ
  refine ⟨R, hR, ?_⟩
  intro J D _ _ N _ center width hwidth hZ P A _ E Q hprime hcover hQ hdepth hprob hlarge herror
  exact (mixedSmoothUniform_badPrimeProduct_probability center width hwidth hZ P A E
    hprime hcover hQs hQ hR hdepth hprob hlarge
    (hradius Q hQ).1.le herror).trans (hradius Q hQ).2

end Erdos3

end

end OAI
