import OAI.Combinatorics.Progressions.Dynamics.PreparedEarlyStructuralPowerBudget
import OAI.Combinatorics.Progressions.Estimates.PreparationSliceComposition

namespace OAI

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators

theorem exists_uniform_step {I J : Type} [Fintype I] [DecidableEq I] [DecidableEq J]
    {s D t T R : ℕ} {p δ : ℝ} (L : RankPreparationFamily I J s) (N : I → ℕ)
    (hp : 0 ≤ p) (hR : 1 ≤ R) (hRp : (R : ℝ) ≤ Real.exp p) (hδ : 0 < δ)
    (ht : t ≤ T) (hsize : L.Sized D t) (hheight : L.PreparedHeights p R)
    (hM : (preparationCoordinateCap s D T : ℝ) ≤ p)
    (hbad : ¬ ∀ u, HasLayerSamplingRank (u.val + 1) (fun i => (N i : ℝ)) R (L u).space (L u).poly)
    (f : (∀ i, Fin (N i)) → ℝ) :
    let M := preparationCoordinateCap s D T
    let Q := preparationModulusCap s M R p
    let C := preparationShrink s (Fintype.card I) M R p δ
    (∀ i, C ≤ N i) →
    ∃ (q : ℕ) (S : ResidueBoxSlice N q) (L' : RankPreparationFamily I J s)
      (ip : J → MvPolynomial I ℤ) (c : J → ℝ) (err : (∀ i, Fin (S.length i)) → J → ℝ),
      L'.potential + 1 ≤ L.potential ∧ L'.Sized D (t + 1) ∧ L'.PreparedHeights p R ∧
      0 < q ∧ q ≤ Q ∧ (∀ i, 0 < S.length i ∧ (N i : ℝ) ≤ C * S.length i) ∧
      ((𝔼 x, f x) ≤ 𝔼 x : (∀ i, Fin (S.length i)), f (S.point x)) ∧
      (∀ j, (ip j).totalDegree ≤ s) ∧ (∀ x j, |err x j| ≤ M * δ) ∧
      ∀ x j, L.value (fun i => ((S.point x i).val : ℝ)) j =
        L'.value (fun i => ((x i).val : ℝ)) j +
        (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (ip j) : ℝ) + c j + err x j := by
  classical
  intro M Q C hlarge
  have hC := preparationShrink_one_le s (Fintype.card I) M hR hp hδ
  have hN (i : I) : 0 < N i := by
    have h := hC.trans (hlarge i)
    exact_mod_cast h
  push Not at hbad
  obtain ⟨u, hfail⟩ := hbad
  obtain ⟨hcoord, hcol, hrow⟩ := preparationCoordinateCap_bounds hsize ht u
  let He := rankCutDirectionHeight (Fintype.card (L u).Coord) (Fintype.card (L u).Column)
    (Fintype.card (L u).Row) (preparationHeight p (s - 1 - u.val)) R
  obtain ⟨heNext, heGlobal⟩ := preparation_section_bound L u hp hM hRp hcoord hcol hrow
  have hlargeStep (i : I) := preparation_large_side hp hδ (Nat.succ_le_of_lt u.isLt)
    heGlobal hcoord (hlarge i)
  have hcaps := preparation_step_caps s (Fintype.card I) M R u.val He
    (Fintype.card (L u).Coord) hp hδ (Nat.succ_le_of_lt u.isLt) heGlobal hcoord
  by_cases hu : u.val = 0
  · obtain ⟨a, e, q, S, ip, c, err, ha, heH, hpotential, hvalid, hq, hqbound, hlength,
      hscore, hip, herr, hid⟩ := exists_absorb_slice_step L u hu N
        (fun i => preparationHeight p (s - 1 - i.val)) (fun _ => preparationHeight_pos hp _)
        hR hδ hN hheight hfail f hlargeStep
    let L' := (L.absorb u a e).reindex S.polynomial
    refine ⟨q, S, L', ip, c, err, hpotential, (hsize.absorb u a e).reindex S.polynomial,
      hvalid, hq, hqbound.trans hcaps.1, ?_, hscore, ?_, ?_, hid⟩
    · intro i
      exact ⟨(hlength i).1, preparation_side_loss hp hδ (Nat.succ_le_of_lt u.isLt)
        heGlobal hcoord hqbound (Nat.cast_nonneg _) (hlength i).2⟩
    · intro j
      exact (hip j).trans (Nat.succ_le_of_lt u.isLt)
    · intro x j
      exact (herr x j).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcoord) hδ.le)
  · let v : Fin s := ⟨u.val - 1, by omega⟩
    have hlevel : u.val = v.val + 1 := by dsimp [v]; omega
    obtain ⟨a, e, q, S, l, ip, c, err, ha, heH, hpotential, hvalid, hq, hqbound, hlength,
      hscore, hip, herr, hid⟩ := exists_descend_slice_step L u v hlevel N
        (fun i => preparationHeight p (s - 1 - i.val)) (fun _ => preparationHeight_pos hp _)
        hR hδ hN hheight hfail f hlargeStep
    let L' := (L.descend u v a e l).reindex S.polynomial
    refine ⟨q, S, L', ip, c, err, hpotential,
      (hsize.descend u v hlevel a e l).reindex S.polynomial, ?_, hq,
      hqbound.trans hcaps.1, ?_, hscore, ?_, ?_, hid⟩
    · intro i
      apply (hvalid i).mono_height
      split_ifs with hi
      · subst i
        apply max_le le_rfl
        have hd : s - 1 - v.val = (s - 1 - u.val) + 1 := by omega
        rwa [hd]
      · exact le_rfl
    · intro i
      exact ⟨(hlength i).1, preparation_side_loss hp hδ (Nat.succ_le_of_lt u.isLt)
        heGlobal hcoord hqbound (Nat.cast_nonneg _) (hlength i).2⟩
    · intro j
      exact (hip j).trans (Nat.succ_le_of_lt u.isLt)
    · intro x j
      exact (herr x j).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcoord) hδ.le)

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators

theorem exists_prepared_family {I J : Type} [Fintype I] [DecidableEq I] [DecidableEq J]
    {s D t T R : ℕ} {p δ : ℝ} (r : ℕ) (L : RankPreparationFamily I J s) (N : I → ℕ)
    (hp : 0 ≤ p) (hR : 1 ≤ R) (hRp : (R : ℝ) ≤ Real.exp p) (hδ : 0 < δ)
    (hpot : L.potential ≤ r) (ht : t + r ≤ T)
    (hsize : L.Sized D t) (hheight : L.PreparedHeights p R)
    (hM : (preparationCoordinateCap s D T : ℝ) ≤ p)
    (f : (∀ i, Fin (N i)) → ℝ) :
    let M := preparationCoordinateCap s D T
    let Q := preparationModulusCap s M R p
    let C := preparationShrink s (Fintype.card I) M R p δ
    (∀ i, C ^ (r + 1) ≤ N i) →
    ∃ (q : ℕ) (S : ResidueBoxSlice N q) (L' : RankPreparationFamily I J s)
      (ip : J → MvPolynomial I ℤ) (c : J → ℝ) (err : (∀ i, Fin (S.length i)) → J → ℝ),
      L'.potential ≤ L.potential ∧ L'.Sized D (t + r) ∧ L'.PreparedHeights p R ∧
      (∀ u, HasLayerSamplingRank (u.val + 1) (fun i => (S.length i : ℝ)) R (L' u).space (L' u).poly) ∧
      0 < q ∧ q ≤ Q ^ r ∧ (∀ i, 0 < S.length i ∧ (N i : ℝ) ≤ C ^ r * S.length i) ∧
      ((𝔼 x, f x) ≤ 𝔼 x : (∀ i, Fin (S.length i)), f (S.point x)) ∧
      (∀ j, (ip j).totalDegree ≤ s) ∧ (∀ x j, |err x j| ≤ r * M * δ) ∧
      ∀ x j, L.value (fun i => ((S.point x i).val : ℝ)) j =
        L'.value (fun i => ((x i).val : ℝ)) j +
        (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (ip j) : ℝ) + c j + err x j := by
  classical
  intro M Q C hlarge
  induction r using Nat.strong_induction_on generalizing t L N with
  | h r ih =>
    have hC : 1 ≤ C := preparationShrink_one_le s (Fintype.card I) M hR hp hδ
    have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
    have hQ : 1 ≤ Q := Nat.mul_pos hR (pow_pos (preparationHeight_pos hp s) M)
    have hN (i : I) : 0 < N i := by
      have hn : (1 : ℝ) ≤ N i := (one_le_pow₀ hC).trans (hlarge i)
      exact_mod_cast hn
    by_cases hgood : ∀ u, HasLayerSamplingRank (u.val + 1) (fun i => (N i : ℝ)) R (L u).space (L u).poly
    · refine ⟨1, ResidueBoxSlice.identity N, L, fun _ => 0, fun _ => 0, fun _ _ => 0,
        le_rfl, hsize.mono (Nat.le_add_right t r), hheight, hgood, by omega,
        one_le_pow₀ hQ, ?_, ?_, ?_, ?_, ?_⟩
      · intro i
        refine ⟨hN i, ?_⟩
        exact le_mul_of_one_le_left (Nat.cast_nonneg _) (one_le_pow₀ hC)
      · change (𝔼 x, f x) ≤ 𝔼 x : (∀ i, Fin (N i)), f ((ResidueBoxSlice.identity N).point x)
        simp only [ResidueBoxSlice.identity_point, le_refl]
      · intro j
        simp
      · intro x j
        simp only [abs_zero]
        positivity
      · intro x j
        change (∀ i, Fin (N i)) at x
        simp only [ResidueBoxSlice.identity_point, map_zero, Int.cast_zero, add_zero]
    · have hside (i : I) : C ≤ N i := by
        have hpow : C ≤ C ^ (r + 1) := by
          simpa only [pow_one] using pow_le_pow_right₀ hC (Nat.le_add_left 1 r)
        exact hpow.trans (hlarge i)
      obtain ⟨q₁, S₁, L₁, ip₁, c₁, e₁, hdrop, hsize₁, hheight₁, hq₁, hq₁bound,
        hlength₁, hscore₁, hip₁, he₁, hid₁⟩ :=
        exists_uniform_step L N hp hR hRp hδ (by omega) hsize hheight hM hgood f hside
      have hr : 0 < r := by omega
      obtain ⟨r', hr'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
      subst r
      have hnext (i : I) : C ^ (r' + 1) ≤ S₁.length i := by
        apply le_of_mul_le_mul_left (a := C) _ hCpos
        calc
          C * C ^ (r' + 1) = C ^ (r' + 1 + 1) := by rw [pow_succ]; ring
          _ ≤ N i := hlarge i
          _ ≤ C * S₁.length i := (hlength₁ i).2
      obtain ⟨q₂, S₂, L₂, ip₂, c₂, e₂, hpot₂, hsize₂, hheight₂, hgood₂, hq₂,
        hq₂bound, hlength₂, hscore₂, hip₂, he₂, hid₂⟩ :=
        ih r' (Nat.lt_succ_self r') L₁ S₁.length (by omega) (by omega) hsize₁ hheight₁
          (fun x => f (S₁.point x)) hnext
      refine ⟨q₁ * q₂, S₁.comp S₂, L₂,
        fun j => S₂.reindexInteger (ip₁ j) + ip₂ j, fun j => c₁ j + c₂ j,
        fun x j => e₁ (S₂.point x) j + e₂ x j,
        hpot₂.trans (by omega), ?_, hheight₂, hgood₂, Nat.mul_pos hq₁ hq₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · convert hsize₂ using 1; omega
      · calc
          q₁ * q₂ ≤ Q * Q ^ r' := Nat.mul_le_mul hq₁bound hq₂bound
          _ = Q ^ (r' + 1) := by rw [pow_succ]; ring
      · intro i
        refine ⟨(hlength₂ i).1, ?_⟩
        calc
          (N i : ℝ) ≤ C * S₁.length i := (hlength₁ i).2
          _ ≤ C * (C ^ r' * S₂.length i) := mul_le_mul_of_nonneg_left (hlength₂ i).2 hCpos.le
          _ = C ^ (r' + 1) * (S₁.comp S₂).length i := by
            change C * (C ^ r' * (S₂.length i : ℝ)) = C ^ (r' + 1) * S₂.length i
            rw [pow_succ]
            ring
      · change (𝔼 x, f x) ≤ 𝔼 x : (∀ i, Fin (S₂.length i)), f ((S₁.comp S₂).point x)
        simpa only [ResidueBoxSlice.comp_point] using hscore₁.trans hscore₂
      · intro j
        exact (MvPolynomial.totalDegree_add _ _).trans
          (max_le (S₂.reindexInteger_degree _ (hip₁ j)) (hip₂ j))
      · intro x j
        calc
          |e₁ (S₂.point x) j + e₂ x j| ≤ |e₁ (S₂.point x) j| + |e₂ x j| := abs_add_le _ _
          _ ≤ M * δ + r' * M * δ := add_le_add (he₁ _ _) (he₂ _ _)
          _ = (r' + 1 : ℕ) * M * δ := by push_cast; ring
      · exact compose_slice_identity S₁ S₂ ip₁ ip₂ c₁ c₂ e₁ e₂ hid₁ hid₂

end Erdos3.RankPreparationFamily

end

end OAI
