import GowersSzemeredi.Proofs13UniformSquareExtraction
import GowersSzemeredi.Proofs13FejerFrequencyGraph

/-! Propagate the purified frequency density into square extraction.
The explicit exponent comparison is performed in the next module. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The purified density implies a stronger Fourier-set density bound. -/
theorem section13_fejer_square_density {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    (alpha / 2) ^ ((2 : Nat) ^ 42) ≤
      (2 : Real) ^ (-(137 : Int)) * ((alpha / 2) ^ (4207554485 : Nat)) ^ 704 := by
  let a := alpha / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hahalf : a ≤ 1 / 2 := by dsimp [a]; linarith only [hαone]
  have haone : a ≤ 1 := hahalf.trans (by norm_num)
  have hc : a ^ 137 ≤ (2 : Real) ^ (-(137 : Int)) := by
    calc
      _ ≤ (1 / 2 : Real) ^ 137 := pow_le_pow_left₀ ha.le hahalf _
      _ = _ := by norm_num
  calc
    _ ≤ a ^ (137 + (4207554485 : Nat) * 704) :=
      pow_le_pow_of_le_one ha.le haone (by norm_num)
    _ = a ^ 137 * (a ^ (4207554485 : Nat)) ^ 704 := by rw [pow_add, pow_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

/-- Failure of cubic uniformity yields a dense bilinear Fourier square, with
an explicit positive exponent gamma((alpha/2)^4207554485). This proves the whole
analytic-to-geometric extraction with a uniform sufficiently-large threshold;
it does not assert the different printed Theorem 13.12 length exponent. -/
theorem theorem_13_12_with_fejer_extraction_exponent :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 → ∃ N₀ : Nat,
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
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
  obtain ⟨N₁, hN₁⟩ := section13_fejer_frequency_graph alpha hα hαone
  obtain ⟨N₂, hN₂⟩ := section13_complete_square_extraction_uniform_density hδ
  refine ⟨max N₁ N₂, fun N _ _ hN f hf hnot => ?_⟩
  obtain ⟨A, psi, hA, hfreiman, hmostly, hfourier⟩ := hN₁ N (by omega) f hf hnot
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
    hN₂ N S hδβ (by omega)
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

end LeanProofs.GowersSzemeredi
