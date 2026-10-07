import OAI.Combinatorics.Progressions.Geometry.IntervalBoxDifference

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem product_difference_bias_approximation (e : ℕ) (N : Fin e → ℕ) (M : ℕ)
    (hM : 0 < M) {a θ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hN : ∀ i, denseProductDensityBudget e (a/(2*3^e)) ≤ N i)
    (hMlarge : denseProductDensityBudget e (a/(2*3^e)) ≤ (M : ℝ)*a)
    (hbias : a ≤ 𝔼 y : (∀ i : Fin e, Fin (N i)), 𝔼 x : (∀ i : Fin e, Fin (N i)),
      ‖geometricCharacterMean M
        ((θ * (∏ i : Fin e, (((x i).val : ℝ)-((y i).val : ℝ))) : ℝ) : CircleFourier.Circle)‖) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ denseProductDensityBudget e (a/(2*3^e)) ∧
      NearInteger
        (denseProductDensityBudget e (a/(2*3^e))/((M : ℝ)*a*∏ i, (N i : ℝ)))
        ((q : ℝ)*θ) := by
  let η := a/(2*3^e)
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by
    have hp : (1 : ℝ) ≤ 3^e := one_le_pow₀ (by norm_num)
    apply (div_le_one (by positivity : (0 : ℝ) < 2*3^e)).mpr
    linarith
  have hNp : ∀ i, 0 < N i := by
    intro i
    have h := (denseProductDensityBudget_pos e hη).trans_le (hN i)
    exact_mod_cast h
  let : ∀ i, Nonempty (Fin (N i)) := fun i => ⟨⟨0, hNp i⟩⟩
  let f := fun (y x : ∀ i, Fin (N i)) =>
    θ * (∏ i : Fin e, (((x i).val : ℝ)-((y i).val : ℝ)))
  have hsplit : (𝔼 p : (∀ i, Fin (N i)) × (∀ i, Fin (N i)),
      ‖geometricCharacterMean M (f p.1 p.2 : CircleFourier.Circle)‖) =
      𝔼 y, 𝔼 x, ‖geometricCharacterMean M (f y x : CircleFourier.Circle)‖ := by
    simpa using (Finset.expect_product' Finset.univ Finset.univ
      (fun y x => ‖geometricCharacterMean M (f y x : CircleFourier.Circle)‖))
  have hpair := nearIntegerDensity_of_geometric_mean
    (fun p : (∀ i, Fin (N i)) × (∀ i, Fin (N i)) => f p.1 p.2) hM ha
    (hbias.trans_eq hsplit.symm)
  rw [nearIntegerDensity_product f] at hpair
  have hdiff : a/2/3^e ≤ nearIntegerDensity
      (fun x : ∀ i, SymmetricIntegerInterval (N i) => θ * ∏ i, ((x i : ℤ) : ℝ))
      (1/((M : ℝ)*a)) := by
    simpa only [Fintype.card_fin] using nearIntegerDensity_interval_differences N hNp
      (fun x => θ * ∏ i, ((x i : ℤ) : ℝ)) (1/((M : ℝ)*a)) (by positivity : 0 ≤ a/2)
      (by simpa only [f, intervalBoxDifference, intervalDifference, Int.cast_sub,
        Int.cast_natCast] using hpair)
  have hsmall : 1/((M : ℝ)*a) ≤ 1/denseProductDensityBudget e η :=
    one_div_le_one_div_of_le (denseProductDensityBudget_pos e hη) hMlarge
  obtain ⟨q, hq, hqB, hnear⟩ := dense_product_signed_box e N hη hη1 hN
    (by positivity : 0 ≤ 1/((M : ℝ)*a)) hsmall
    (by simpa only [η, div_div] using hdiff)
  refine ⟨q, hq, hqB, ?_⟩
  convert hnear using 1
  ring

end Erdos3

end

end OAI
