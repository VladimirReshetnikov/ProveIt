import GowersSzemeredi.Proofs13FourierBoxTransport
import GowersSzemeredi.Proofs17LocalizedPhaseRemoval
import GowersSzemeredi.Proofs17PartitionEnergy

/-! The complete Section 13 extraction supplies the hypotheses of localized
cubic phase removal, without assuming a bilinear square or its geometry. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Failure of cubic uniformity yields a cubic polynomial twist that fails
quadratic uniformity on a proper progression partition. Both the cell-length
bound and the surviving uniformity parameter are explicit. -/
theorem cubic_nonuniformity_localized_phase_removal_with_upper :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 → ∃ N₀ : Nat,
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
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
  obtain ⟨N₀, hN₀⟩ := theorem_13_12_odd_square alpha hα hαone
  refine ⟨N₀, fun N _ _ hN f hf hnot => ?_⟩
  obtain ⟨m, P, R, B, psi, hmodd, hmpos, hmsqrt, hsize, hPs, hPR, hP, hR,
    hPl, hRl, hB, hmass, hbil, hfourier⟩ := hN₀ N hN f hf hnot
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

/-- The original localization interface is preserved as a specialization. -/
theorem cubic_nonuniformity_localized_phase_removal :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 → ∃ N₀ : Nat,
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
        ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
        ∃ phi : ZMod N → ZMod N, ∃ M l : Nat, ∃ Q : Fin M → ModAP N,
          PolynomialOn 3 Finset.univ phi ∧
          IsPartition (fun i => (Q i).carrier) Finset.univ ∧
          (∀ i, (Q i).IsProper ∧ ((Q i).length = l ∨ (Q i).length = l + 1)) ∧
          (N : Real) ^ ((1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88))) / 12 ≤ l ∧
          ¬ UniformOnPartition (phaseTwist f phi) 2
            ((2 : Real) ^ (-(58 : Int)) * alpha ^ 2 * (alpha / 2) ^ ((2 : Nat) ^ 76)) Q (l + 1) := by
  intro alpha hα hαone
  obtain ⟨N₀, hN₀⟩ := cubic_nonuniformity_localized_phase_removal_with_upper alpha hα hαone
  refine ⟨N₀, fun N _ _ hN f hf hnot => ?_⟩
  obtain ⟨phi, M, l, Q, hpoly, hpart, hproper, hlower, _, hfail⟩ := hN₀ N hN f hf hnot
  exact ⟨phi, M, l, Q, hpoly, hpart, hproper, hlower, hfail⟩

/-- An individual proper progression carrying the quadratic obstruction.
The displayed normalization is in the original ambient modulus; transfer to
another modulus requires its own argument. -/
theorem cubic_nonuniformity_has_local_quadratic_obstruction :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 → ∃ N₀ : Nat,
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
        ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
        ∃ phi : ZMod N → ZMod N, ∃ l : Nat, ∃ P : ModAP N,
          PolynomialOn 3 Finset.univ phi ∧ P.IsProper ∧
          (P.length = l ∨ P.length = l + 1) ∧
          (N : Real) ^ ((1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88))) / 12 ≤ l ∧
          DiscValued (restrictToCell P.carrier (phaseTwist f phi)) ∧
          ¬ UniformOfDegree (restrictToCell P.carrier (phaseTwist f phi))
            (((2 : Real) ^ (-(58 : Int)) * alpha ^ 2 * (alpha / 2) ^ ((2 : Nat) ^ 76)) *
              (((l + 1 : Nat) : Real) / N) ^ 4) 2 := by
  intro alpha hα hαone
  obtain ⟨N₀, hN₀⟩ := cubic_nonuniformity_localized_phase_removal alpha hα hαone
  refine ⟨N₀, fun N _ _ hN f hf hnot => ?_⟩
  obtain ⟨phi, M, l, Q, hpoly, _, hproper, hlength, hfail⟩ := hN₀ N hN f hf hnot
  obtain ⟨i, hi⟩ := not_uniformOnPartition_exists_cell (phaseTwist f phi) Q _ hfail
  exact ⟨phi, l, Q i, hpoly, (hproper i).1, (hproper i).2, hlength,
    restrictToCell_discValued (phaseTwist_discValued hf phi) _, hi⟩

end LeanProofs.GowersSzemeredi
