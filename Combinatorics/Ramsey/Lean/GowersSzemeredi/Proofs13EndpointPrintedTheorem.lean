import GowersSzemeredi.Proofs13EndpointGlobalFourier
import GowersSzemeredi.Proofs13FejerPrintedRange
import GowersSzemeredi.Proofs08AffineFrequencyProgression

/-! Close the near-maximal range by using the whole prime cyclic group
as both progressions. Together with quantitative Fejer extraction this
proves Theorem 13.12 with its exact printed bounds for every parameter. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem theorem_13_12_near_one :
    ∀ alpha : Real, 1023 / 1024 < alpha → alpha ≤ 1 → ∃ N₀ : Nat,
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
        ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
        ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
          P.step != 0 ∧ P.step = Q.step ∧ P.IsProper ∧ Q.IsProper ∧ P.length = Q.length ∧
          (N : Real) ^ ((1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 70))) ≤ P.length ∧
          B ⊆ P.carrier.product Q.carrier ∧
          (alpha / 2) ^ ((2 : Nat) ^ 76) * P.length * Q.length ≤ B.card ∧
          BilinearOn (P.carrier.product Q.carrier) phi ∧
          ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ := by
  intro alpha hαnear hαone
  classical
  refine ⟨0, fun N _ _ _ f hf hnot => ?_⟩
  have hα : 0 < alpha := lt_trans (by norm_num) hαnear
  have hnear : 1 - (1 - alpha) ≤ endpointCubeMean f 4 := by
    have hgt : alpha < endpointCubeMean f 4 := by
      exact lt_of_not_ge ((uniformOfDegree_iff_endpointCubeMean (d := 3) f alpha).not.mp hnot)
    linarith only [hgt]
  obtain ⟨c, B, hmass, hfourier⟩ := endpoint_global_fourier f hf (1 - alpha) hnear
  let P : ModAP N := modInterval N 0 N
  have hPuniv : P.carrier = Finset.univ := modInterval_zero_modulus_carrier N
  have hP : P.IsProper := by
    change P.carrier.card = N
    rw [hPuniv, Finset.card_univ, ZMod.card]
  let phi : Pair N → ZMod N := fun p => c * p.1 * p.2
  refine ⟨P, P, B, phi, ?_, rfl, hP, hP, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [P, modInterval]
  · have hγ : (1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 70)) ≤ 1 :=
      Real.rpow_le_one (by norm_num) (by norm_num) (by positivity)
    have hN : (1 : Real) ≤ N := by exact_mod_cast NeZero.pos N
    calc
      _ ≤ (N : Real) ^ (1 : Real) := Real.rpow_le_rpow_of_exponent_le hN hγ
      _ = _ := by rw [Real.rpow_one]; rfl
  · rw [hPuniv]
    intro p _
    simp [Finset.product]
  · have hd : (alpha / 2) ^ ((2 : Nat) ^ 76) ≤ 1 / 2 := by
      calc
        _ ≤ (alpha / 2) ^ (1 : Nat) :=
          pow_le_pow_of_le_one (by positivity) (by linarith only [hαone]) (by norm_num)
        _ ≤ _ := by rw [pow_one]; linarith only [hαone]
    have hcoef : (alpha / 2) ^ ((2 : Nat) ^ 76) ≤ 1 - 332 * (1 - alpha) := by
      exact hd.trans (by linarith only [hαnear])
    change (alpha / 2) ^ ((2 : Nat) ^ 76) * (N : Real) * N ≤ B.card
    calc
      _ = (alpha / 2) ^ ((2 : Nat) ^ 76) * (N : Real) ^ 2 := by rw [pow_two, mul_assoc]
      _ ≤ (1 - 332 * (1 - alpha)) * (N : Real) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef (sq_nonneg (N : Real))
      _ ≤ _ := hmass
  · refine ⟨phi, ⟨0, 0, 0, c, ?_⟩, fun _ _ => rfl⟩
    intro p
    simp [phi]
  · intro p hp
    have hcoef : alpha / 2 ≤ 3 / 4 - 4 * (1 - alpha) := by
      linarith only [hαnear, hαone]
    have ht := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg N : (0 : Real) ≤ N)
    have hlarge := hfourier p hp
    change alpha * N / 2 ≤ ‖secondDifferenceFourier f p.1 p.2 (c * p.1 * p.2)‖
    nlinarith only [ht, hlarge]

theorem theorem_13_12_holds : theorem_13_12 := by
  intro alpha hα hαone
  by_cases haway : alpha ≤ 1023 / 1024
  · exact theorem_13_12_away_from_one alpha hα haway
  · exact theorem_13_12_near_one alpha (lt_of_not_ge haway) hαone

end LeanProofs.GowersSzemeredi
