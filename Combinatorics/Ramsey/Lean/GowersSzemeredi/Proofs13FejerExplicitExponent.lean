import GowersSzemeredi.Proofs13FejerFourierExtraction
import GowersSzemeredi.Proofs13ExplicitFourierExponent

/-! The purified graph improves the explicit all-parameter length exponent
from top power 2^88 to 2^53. The density bound is simultaneously 2^42. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section13_fejer_spectral_upper {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    15 * section13Q ((alpha / 2) ^ (4207554485 : Nat)) ≤
      (2 / alpha) ^ ((2 : Nat) ^ 53) := by
  let t := 2 / alpha
  have ht : 2 ≤ t := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have htpos : 0 < t := (by norm_num : (0 : Real) < 2).trans_le ht
  have htone : 1 ≤ t := (by norm_num : (1 : Real) ≤ 2).trans ht
  have ha : 0 < alpha / 2 := by positivity
  have hinv : (alpha / 2)⁻¹ = t := by dsimp [t]; field_simp
  have hcollapse : ((alpha / 2) ^ (4207554485 : Nat)) ^ (-((2 : Real) ^ 21)) =
      t ^ ((4207554485 : Nat) * (2 : Nat) ^ 21) := by
    rw [← Real.rpow_natCast (alpha / 2) (4207554485 : Nat), ← Real.rpow_mul ha.le]
    rw [show ((4207554485 : Nat) : Real) * (-((2 : Real) ^ 21)) =
      -((((4207554485 : Nat) * (2 : Nat) ^ 21 : Nat) : Real)) by norm_num]
    rw [Real.rpow_neg_eq_inv_rpow, hinv, Real.rpow_natCast]
  have hc : 15 * (2 : Real) ^ ((2 : Nat) ^ 20) ≤ t ^ ((2 : Nat) ^ 20 + 4) := by
    calc
      _ ≤ (2 : Real) ^ ((2 : Nat) ^ 20) * (2 : Real) ^ (4 : Nat) := by
        have hh : (15 : Real) ≤ (2 : Real) ^ (4 : Nat) := by norm_num
        exact (mul_le_mul_of_nonneg_right hh (pow_nonneg (by norm_num) _)).trans_eq (mul_comm _ _)
      _ = (2 : Real) ^ ((2 : Nat) ^ 20 + 4) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) ht _
  unfold section13Q
  rw [hcollapse]
  calc
    _ = (15 * (2 : Real) ^ ((2 : Nat) ^ 20)) * t ^ ((4207554485 : Nat) * (2 : Nat) ^ 21) := (mul_assoc _ _ _).symm
    _ ≤ t ^ ((2 : Nat) ^ 20 + 4) * t ^ ((4207554485 : Nat) * (2 : Nat) ^ 21) :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg htpos.le _)
    _ = t ^ ((2 : Nat) ^ 20 + 4 + (4207554485 : Nat) * (2 : Nat) ^ 21) := (pow_add _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ htone (by norm_num)

theorem section13_fejer_exponent_lower {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    (1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 53)) ≤
      section13SquareExponent ((alpha / 2) ^ (4207554485 : Nat)) := by
  have hδ : 0 < (alpha / 2) ^ (4207554485 : Nat) := pow_pos (by positivity) _
  have hδone : (alpha / 2) ^ (4207554485 : Nat) ≤ 1 :=
    pow_le_one₀ (by positivity) (by linarith only [hαone])
  calc
    _ = (2 : Real) ^ (-((2 / alpha) ^ ((2 : Nat) ^ 53))) := by
      rw [Real.rpow_neg_eq_inv_rpow, one_div]
    _ ≤ (2 : Real) ^ (-(15 * section13Q ((alpha / 2) ^ (4207554485 : Nat)))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (neg_le_neg (section13_fejer_spectral_upper hα hαone))
    _ ≤ _ := section13SquareExponent_ge_spectral_power hδ hδone

theorem theorem_13_12_with_fejer_explicit_bound :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 → ∃ N₀ : Nat,
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
        ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
        ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
          P.step != 0 ∧ P.step = Q.step ∧ P.IsProper ∧ Q.IsProper ∧ P.length = Q.length ∧
          (N : Real) ^ ((1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 53))) ≤ P.length ∧
          B ⊆ P.carrier.product Q.carrier ∧
          (alpha / 2) ^ ((2 : Nat) ^ 42) * P.length * Q.length ≤ B.card ∧
          BilinearOn (P.carrier.product Q.carrier) phi ∧
          ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ := by
  intro alpha hα hαone
  obtain ⟨N₀, hN₀⟩ := theorem_13_12_with_fejer_extraction_exponent alpha hα hαone
  refine ⟨N₀, fun N _ _ hN f hf hnot => ?_⟩
  obtain ⟨P, Q, B, phi, hs, hs', hP, hQ, hlen, hsize, hbox, hmass, hbil, hfourier⟩ :=
    hN₀ N hN f hf hnot
  refine ⟨P, Q, B, phi, hs, hs', hP, hQ, hlen, ?_, hbox, hmass, hbil, hfourier⟩
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast NeZero.pos N
  exact (Real.rpow_le_rpow_of_exponent_le hNreal (section13_fejer_exponent_lower hα hαone)).trans hsize

end LeanProofs.GowersSzemeredi
