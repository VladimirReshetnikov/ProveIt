import GowersSzemeredi.Proofs08OddFrequencyProgression
import GowersSzemeredi.Proofs17LocalizedPhaseRemoval
import GowersSzemeredi.Proofs17PartitionEnergy

/-! Quadratic nonuniformity yields a quadratic phase twist with a local
linear obstruction. The actual partition cells retain their upper bounds. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- A dense set of large derivative Fourier coefficients supplies the
one-dimensional box energy required by localized phase removal. -/
theorem affineFrequencyProgression_energy {N m : Nat} [NeZero N]
    (P : ModAP N) (D : Finset (ZMod N)) (f : ZMod N → Complex)
    (a b : ZMod N) (alpha delta : Real)
    (hα : 0 ≤ alpha) (hD : D ⊆ P.carrier)
    (hmass : delta * m ≤ (D.card : Real))
    (hlarge : ∀ x ∈ D, alpha / 2 * N ≤ ‖fourier (difference f x) (a * x + b)‖) :
    (delta * alpha ^ 2 / 4) * (N : Real) ^ 2 * (m : Real) ≤
      ∑ x ∈ P.asBox.carrier, ‖fourier (cubeDifference f x) (a * x 0 + b)‖ ^ 2 := by
  classical
  let E := D.image (pointOneEquiv N)
  have hE : E ⊆ P.asBox.carrier := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_constant_box_one P.asBox z).mpr (hD hz)
  have hcard : E.card = D.card := Finset.card_image_iff.mpr (pointOneEquiv N).injective.injOn
  have hpoint : ∀ x ∈ E, (alpha / 2 * N) ^ 2 ≤
      ‖fourier (cubeDifference f x) (a * x 0 + b)‖ ^ 2 := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    rw [cubeDifference_pointOne]
    exact pow_le_pow_left₀ (by positivity) (hlarge z hz) 2
  have hmass' := mul_le_mul_of_nonneg_right hmass (sq_nonneg (alpha / 2 * N))
  calc
    _ ≤ (D.card : Real) * (alpha / 2 * N) ^ 2 := by nlinarith only [hmass']
    _ = ∑ _x ∈ E, (alpha / 2 * N) ^ 2 := by simp [hcard]
    _ ≤ ∑ x ∈ E, ‖fourier (cubeDifference f x) (a * x 0 + b)‖ ^ 2 :=
      Finset.sum_le_sum hpoint
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hE (fun _ _ _ ↦ sq_nonneg _)

/-- A quadratic twist lowers the obstruction degree on a partition into
proper progressions, with explicit surviving parameter and length exponent. -/
theorem quadratic_nonuniformity_localized_phase_removal :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 → ∃ N₀ : Nat,
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
        ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 2 →
        ∃ phi : ZMod N → ZMod N, ∃ M l : Nat, ∃ Q : Fin M → ModAP N,
          PolynomialOn 2 Finset.univ phi ∧
          IsPartition (fun i ↦ (Q i).carrier) Finset.univ ∧
          (∀ i, (Q i).IsProper ∧ ((Q i).length = l ∨ (Q i).length = l + 1)) ∧
          (N : Real) ^ cor711Exponent ((alpha / 2) ^ (12359 : Nat)) 1 / 6 ≤ l ∧
          (∀ i, ((Q i).length : Real) ≤ Real.sqrt N) ∧
          ¬ UniformOnPartition (phaseTwist f phi) 1
            ((2 : Real) ^ (-(19 : Int)) * alpha ^ 2 * (alpha / 2) ^ (12359 : Nat)) Q (l + 1) := by
  intro alpha hα hαone
  obtain ⟨N₀, hN₀⟩ := quadratic_nonuniformity_odd_affine_frequencies alpha hα hαone
  refine ⟨N₀, fun N _ _ hN f hf hnot ↦ ?_⟩
  obtain ⟨m, P, D, a, b, hodd, hm, hmsqrt, hsize, hs, hP, hPl, hD, hmass, hfourier⟩ :=
    hN₀ N hN f hf hnot
  let delta := (alpha / 2) ^ (12359 : Nat) / 2
  let rho := delta * alpha ^ 2 / 4
  have hrho : 0 < rho := by dsimp [rho, delta]; positivity
  have henergy := affineFrequencyProgression_energy P D f a b alpha delta hα.le hD hmass hfourier
  have hwidth : P.asBox.width = m := (BaseCase.boxOne_width P.asBox).trans hPl
  obtain ⟨phi, M, l, Q, hpoly, hpart, hproper, hlength, hupper, hfail⟩ :=
    proposition_17_7_with_upper N 1 m f P.asBox (fun x ↦ a * x 0 + b) rho hrho
      (by omega) hodd hwidth (fun _ ↦ hPl) hs hmsqrt hf
      (BaseCase.isMultilinear_affine_one a b) (by simpa only [pow_one] using henergy)
  have hconstant : (2 : Real) ^ (-(2 * (1 + 1) ^ 3 : Int)) * rho =
      (2 : Real) ^ (-(19 : Int)) * alpha ^ 2 * (alpha / 2) ^ (12359 : Nat) := by
    dsimp [rho, delta]
    generalize (alpha / 2) ^ (12359 : Nat) = c
    norm_num
    ring
  refine ⟨phi, M, l, Q, hpoly, hpart, hproper, ?_, ?_, ?_⟩
  · norm_num only [Nat.cast_one, mul_one] at hlength
    linarith only [hsize, hlength]
  · intro i
    exact (by exact_mod_cast hupper i : ((Q i).length : Real) ≤ m).trans hmsqrt
  · simpa only [Nat.cast_one, hconstant] using hfail

end LeanProofs.GowersSzemeredi
