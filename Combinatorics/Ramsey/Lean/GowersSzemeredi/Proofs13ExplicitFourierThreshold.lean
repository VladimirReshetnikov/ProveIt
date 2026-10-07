import GowersSzemeredi.Proofs13ExplicitGeometricThreshold
import GowersSzemeredi.Proofs13ExplicitFrequencyGraph
import GowersSzemeredi.Proofs13FejerExplicitExponent

/-! A fully explicit modulus threshold for the bilinear Fourier square.
The improved Fejer density and length exponents are retained. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section13FourierThreshold (alpha : Real) : Real :=
  max (section13FrequencyGraphThreshold alpha)
    (section13GeometricThreshold ((alpha / 2) ^ (4207554485 : Nat)))

theorem theorem_13_12_fejer_extraction_explicit :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 →
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], section13FourierThreshold alpha ≤ N →
        ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
        ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
          P.step != 0 ∧ P.step = Q.step ∧ P.IsProper ∧ Q.IsProper ∧ P.length = Q.length ∧
          (N : Real) ^ section13SquareExponent ((alpha / 2) ^ (4207554485 : Nat)) ≤ P.length ∧
          B ⊆ P.carrier.product Q.carrier ∧
          (alpha / 2) ^ ((2 : Nat) ^ 42) * P.length * Q.length ≤ B.card ∧
          BilinearOn (P.carrier.product Q.carrier) phi ∧
          ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ := by
  intro alpha hα hαone
  let delta := (alpha / 2) ^ (4207554485 : Nat)
  have hδ : 0 < delta := pow_pos (by positivity) _
  intro N _ _ hN f hf hnot
  have hNgraph : section13FrequencyGraphThreshold alpha ≤ N := by
    exact_mod_cast ((le_max_left _ _).trans hN : (section13FrequencyGraphThreshold alpha : Real) ≤ N)
  obtain ⟨A, psi, hA, hfreiman, hmostly, hfourier⟩ := section13_fejer_frequency_graph_explicit alpha hα hαone N hNgraph f hf hnot
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hN2 : 0 < (N : Real) ^ 2 := pow_pos hNpos _
  let beta := (A.card : Real) / (N : Real) ^ 2
  have hδβ : delta ≤ beta := (le_div_iff₀ hN2).mpr hA
  have hcard : (A.card : Real) ≤ (N : Real) ^ 2 := by
    have hc : A.card ≤ N * N := by simpa only [Pair, Fintype.card_prod, ZMod.card] using Finset.card_le_univ A
    exact_mod_cast (by simpa only [pow_two] using hc : A.card ≤ N ^ 2)
  have hβone : beta ≤ 1 := (div_le_one hN2).mpr hcard
  let S : Section13Context N := {
    A := A
    phi := psi
    alpha := beta
    eta := (2 : Real) ^ (-(44 : Int))
    alpha_pos := hδ.trans_le hδβ
    alpha_at_most_one := hβone
    card_A := (div_mul_cancel₀ (A.card : Real) hN2.ne').symm
    separately_freiman := hfreiman
    eta_value := rfl
    mostly_respected := hmostly }
  obtain ⟨P, Q, B, hPs, hPQ, hP, hQ, hlen, hsize, hBA, hbox, hmass, hbil⟩ :=
    section13_complete_square_extraction_explicit hδ N S hδβ ((le_max_right _ _).trans hN)
  obtain ⟨mu, hmu, hagree⟩ := hbil
  refine ⟨P, Q, B, mu, hPs, hPQ, hP, hQ, hlen, hsize, hbox, ?_,
    ⟨mu, hmu, fun _ _ => rfl⟩, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (section13_fejer_square_density hα hαone) (Nat.cast_nonneg P.length))
      (Nat.cast_nonneg Q.length)).trans hmass
  · intro z hz
    have heq : psi z = mu z := hagree z hz
    rw [← heq]
    exact hfourier z (hBA hz)


theorem theorem_13_12_fejer_explicit_threshold :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 →
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], section13FourierThreshold alpha ≤ N →
        ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
        ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
          P.step != 0 ∧ P.step = Q.step ∧ P.IsProper ∧ Q.IsProper ∧ P.length = Q.length ∧
          (N : Real) ^ ((1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 53))) ≤ P.length ∧
          B ⊆ P.carrier.product Q.carrier ∧
          (alpha / 2) ^ ((2 : Nat) ^ 42) * P.length * Q.length ≤ B.card ∧
          BilinearOn (P.carrier.product Q.carrier) phi ∧
          ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ := by
  intro alpha hα hαone
  intro N _ _ hN f hf hnot
  obtain ⟨P, Q, B, phi, hs, hs', hP, hQ, hlen, hsize, hbox, hmass, hbil, hfourier⟩ :=
    theorem_13_12_fejer_extraction_explicit alpha hα hαone N hN f hf hnot
  refine ⟨P, Q, B, phi, hs, hs', hP, hQ, hlen, ?_, hbox, hmass, hbil, hfourier⟩
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast NeZero.pos N
  exact (Real.rpow_le_rpow_of_exponent_le hNreal (section13_fejer_exponent_lower hα hαone)).trans hsize

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
