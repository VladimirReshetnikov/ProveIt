import GowersSzemeredi.Proofs13ExplicitGeometricThreshold
import GowersSzemeredi.Proofs13ExplicitFrequencyGraph
import GowersSzemeredi.Proofs13FejerExplicitExponent

/-! A fully explicit modulus threshold for the bilinear Fourier square.
The improved Fejer density and length exponents are retained. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The older cubic localization exponent is bounded by the improved
Fejer exponent; this transports existing downstream constants unchanged. -/
theorem section13_legacy_exponent_le_fejer {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    (1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88)) ≤
      (1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 53)) := by
  have ht : (1 : Real) ≤ 2 / alpha := (le_div_iff₀ hα).mpr (by linarith)
  exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
    (pow_le_pow_right₀ ht (by norm_num : (2 : Nat) ^ 53 ≤ (2 : Nat) ^ 88))

/-- Explicit-threshold extraction in the original downstream parameter
convention, deduced from the stronger Fejer extraction. -/
theorem theorem_13_12_legacy_explicit_threshold
    (alpha : Real) (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (N : Nat) [NeZero N] [Fact N.Prime] (hN : section13FourierThreshold alpha ≤ N)
    (f : ZMod N → Complex) (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha 3) :
    ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
      P.step != 0 ∧ P.step = Q.step ∧ P.IsProper ∧ Q.IsProper ∧ P.length = Q.length ∧
      (N : Real) ^ ((1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88))) ≤ P.length ∧
      B ⊆ P.carrier.product Q.carrier ∧
      (alpha / 2) ^ ((2 : Nat) ^ 76) * P.length * Q.length ≤ B.card ∧
      BilinearOn (P.carrier.product Q.carrier) phi ∧
      ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ := by
  obtain ⟨P, Q, B, phi, hs, hs', hP, hQ, hlen, hsize, hbox, hmass, hbil, hfourier⟩ :=
    theorem_13_12_fejer_explicit_threshold alpha hα hαone N hN f hf hnot
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast NeZero.pos N
  refine ⟨P, Q, B, phi, hs, hs', hP, hQ, hlen, ?_, hbox, ?_, hbil, hfourier⟩
  · exact (Real.rpow_le_rpow_of_exponent_le hNreal
      (section13_legacy_exponent_le_fejer hα hαone)).trans hsize
  · have hp : (alpha / 2) ^ ((2 : Nat) ^ 76) ≤ (alpha / 2) ^ ((2 : Nat) ^ 42) :=
      pow_le_pow_of_le_one (by positivity) (by linarith only [hαone])
        (by norm_num : (2 : Nat) ^ 42 ≤ (2 : Nat) ^ 76)
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp
      (Nat.cast_nonneg _)) (Nat.cast_nonneg _)).trans hmass

end LeanProofs.GowersSzemeredi
