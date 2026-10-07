import OAI.Combinatorics.Progressions.Linear.RankPreparationIteration

namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

theorem exists_prepared_polynomial_layer {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {j R : ℕ} {p δ : ℝ} (P : VectorPolynomial I ℝ (J → ℝ))
    (hP : DegreeLE (fun _ => 1) (j + 1) P) (hp : 0 ≤ p)
    (hR : 1 ≤ R) (hRp : (R : ℝ) ≤ Real.exp p) (hδ : 0 < δ)
    (N : I → ℕ) (f : (∀ i, Fin (N i)) → ℝ) :
    let D := Fintype.card J
    let T := (j + 1) * D
    let M := preparationCoordinateCap (j + 1) D T
    let share := δ / ((T : ℝ) * M + 1)
    let Q := preparationModulusCap (j + 1) M R p
    let C := preparationShrink (j + 1) (Fintype.card I) M R p share
    (M : ℝ) ≤ p → (∀ i, C ^ (T + 1) ≤ N i) →
    ∃ (q : ℕ) (S : ResidueBoxSlice N q) (L : RankPreparationFamily I J (j + 1))
      (ip : J → MvPolynomial I ℤ) (c : J → ℝ) (err : (∀ i, Fin (S.length i)) → J → ℝ),
      (∑ u, (L u).rank) ≤ T ∧ L.Sized D T ∧ L.PreparedHeights p R ∧
      (∀ u, HasLayerSamplingRank (u.val + 1) (fun i => (S.length i : ℝ)) R (L u).space (L u).poly) ∧
      0 < q ∧ q ≤ Q ^ T ∧ (∀ i, 0 < S.length i ∧ (N i : ℝ) ≤ C ^ T * S.length i) ∧
      ((𝔼 x, f x) ≤ 𝔼 x : (∀ i, Fin (S.length i)), f (S.point x)) ∧
      (∀ k, (ip k).totalDegree ≤ j + 1) ∧ (∀ x k, |err x k| ≤ δ) ∧
      ∀ x k, eval (fun i => ((S.point x i).val : ℝ)) P k =
        L.value (fun i => ((x i).val : ℝ)) k +
        (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (ip k) : ℝ) + c k + err x k := by
  classical
  intro D T M share Q C hM hlarge
  have hshare : 0 < share := by dsimp [share]; positivity
  let L₀ := RankPreparationFamily.initial (j := j) P
  have hpot : L₀.potential = T := RankPreparationFamily.initial_potential P
  obtain ⟨q, S, L, ip, c, err, hpotL, hsize, hheight, hgood, hq, hqbound, hlength,
    hscore, hip, herr, hid⟩ :=
    RankPreparationFamily.exists_prepared_family (t := 0) (T := T) T L₀ N hp hR hRp hshare
      hpot.le (by omega) (RankPreparationFamily.initial_sized P)
      (RankPreparationFamily.initial_heights P hp hP) hM f hlarge
  refine ⟨q, S, L, ip, c, err, ?_, ?_, hheight, hgood, hq, hqbound, hlength,
    hscore, hip, ?_, ?_⟩
  · exact (sum_ranks_le_potential (fun u => (L u).rank)).trans (hpotL.trans hpot.le)
  · simpa only [Nat.zero_add] using hsize
  · intro x k
    apply (herr x k).trans
    have hden : 0 < (T : ℝ) * M + 1 := by positivity
    change (T : ℝ) * M * (δ / ((T : ℝ) * M + 1)) ≤ δ
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  · intro x k
    have h := hid x k
    rw [RankPreparationFamily.initial_value] at h
    exact h

end Erdos3

end

end OAI
