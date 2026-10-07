import GowersSzemeredi.Proofs17CubicLocalization
import GowersSzemeredi.Proofs13ExplicitOddSquare

/-! Cubic polynomial localization at an explicit starting modulus. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem cubic_nonuniformity_localized_phase_removal_explicit :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 →
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], section13OddSquareThreshold alpha ≤ N →
        ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
        ∃ phi : ZMod N → ZMod N, ∃ M l : Nat, ∃ Q : Fin M → ModAP N,
          PolynomialOn 3 Finset.univ phi ∧
          IsPartition (fun i => (Q i).carrier) Finset.univ ∧
          (∀ i, (Q i).IsProper ∧ ((Q i).length = l ∨ (Q i).length = l + 1)) ∧
          (N : Real) ^ ((1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88))) / 12 ≤ l ∧
          (∀ i, ((Q i).length : Real) ≤ Real.sqrt N) ∧
          ¬ UniformOnPartition (phaseTwist f phi) 2
            ((2 : Real) ^ (-(58 : Int)) * alpha ^ 2 * (alpha / 2) ^ ((2 : Nat) ^ 76)) Q (l + 1) := by
  intro alpha hα hαone
  intro N _ _ hN f hf hnot
  obtain ⟨m, P, R, B, psi, hmodd, hmpos, hmsqrt, hsize, hPs, hPR, hP, hR,
    hPl, hRl, hB, hmass, hbil, hfourier⟩ := theorem_13_12_odd_square_explicit alpha hα hαone N hN f hf hnot
  obtain ⟨mu, hmu, hagree⟩ := hbil
  let delta := (alpha / 2) ^ ((2 : Nat) ^ 76) / 4
  let rho := delta * alpha ^ 2 / 4
  let S := fourierSquareBox P R hPR
  let sigma : Point N 2 → ZMod N := fun x => mu ((fourierSquareEquiv N).symm x)
  have hrho : 0 < rho := by dsimp [rho, delta]; positivity
  have hlarge : ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (mu z)‖ := by
    intro z hz
    rw [← hagree z (hB hz)]
    exact hfourier z hz
  have henergy := fourierSquare_energy P R hPR B f mu alpha delta hα.le hB hmass hlarge
  obtain ⟨phi, M, l, Q, hpoly, hpartition, hproper, hlength, hupper, hnonuniform⟩ :=
    proposition_17_7_with_upper N 2 m f S sigma rho hrho (by omega) hmodd
      (fourierSquareBox_width P R hPR hPl hRl)
      (fourierSquareBox_axis_length P R hPR hPl hRl) hPs hmsqrt hf hmu.to_multilinear henergy
  have hconstant : (2 : Real) ^ (-(2 * (2 + 1) ^ 3 : Int)) * rho =
      (2 : Real) ^ (-(58 : Int)) * alpha ^ 2 * (alpha / 2) ^ ((2 : Nat) ^ 76) := by
    dsimp [rho, delta]
    generalize (alpha / 2) ^ ((2 : Nat) ^ 76) = a
    norm_num
    ring
  refine ⟨phi, M, l, Q, hpoly, hpartition, hproper, ?_, ?_, ?_⟩
  · norm_num only [Nat.cast_ofNat] at hlength
    linarith only [hsize, hlength]
  · intro i
    exact (by exact_mod_cast hupper i : ((Q i).length : Real) ≤ m).trans hmsqrt
  · simpa only [Nat.cast_ofNat, hconstant] using hnonuniform


end LeanProofs.GowersSzemeredi
