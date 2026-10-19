import GowersSzemeredi.Proofs13FourierBoxTransport
import GowersSzemeredi.Proofs17LocalizedPhaseRemoval
import GowersSzemeredi.Proofs17PartitionEnergy
import GowersSzemeredi.Proofs13FejerOddSquare

/-! Cubic polynomial localization at an explicit starting modulus.

`fejer_cubic_nonuniformity_localized_phase_removal` is in
`Proofs17FejerCubicLocalizationSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def fejerCubicPrimeModelThreshold (alpha T : Real) : Real :=
  max 256 (max (section13FejerOddSquareThreshold alpha)
    (positivePowerThreshold (12 * max 2 T) 1
      ((1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 53)))))

/-- **Cubic localization** (Section 17) at any odd-square exponent. -/
theorem FejerOddSquareAt.localized {alpha e T : Real} (h : FejerOddSquareAt alpha e T)
    (hα : 0 < alpha) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], T ≤ N →
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
      ∃ phi : ZMod N → ZMod N, ∃ M l : Nat, ∃ Q : Fin M → ModAP N,
        PolynomialOn 3 Finset.univ phi ∧
        IsPartition (fun i => (Q i).carrier) Finset.univ ∧
        (∀ i, (Q i).IsProper ∧ ((Q i).length = l ∨ (Q i).length = l + 1)) ∧
        (N : Real) ^ e / 12 ≤ l ∧
        (∀ i, ((Q i).length : Real) ≤ Real.sqrt N) ∧
        ¬ UniformOnPartition (phaseTwist f phi) 2
          ((2 : Real) ^ (-(58 : Int)) * alpha ^ 2 * (alpha / 2) ^ ((2 : Nat) ^ 42)) Q (l + 1) := by
  intro N _ _ hN f hf hnot
  obtain ⟨m, P, R, B, psi, hmodd, _, hmsqrt, hsize, hPs, hPR, _, _, hPl, hRl, hB, hmass,
    ⟨mu, hmu, hagree⟩, hfourier⟩ := h N hN f hf hnot
  let delta := (alpha / 2) ^ ((2 : Nat) ^ 42) / 4
  have henergy := fourierSquare_energy P R hPR B f mu alpha delta hα.le hB hmass
    fun z hz => hagree z (hB hz) ▸ hfourier z hz
  obtain ⟨phi, M, l, Q, hpoly, hpartition, hproper, hlength, hupper, hnonuniform⟩ :=
    proposition_17_7_with_upper N 2 m f (fourierSquareBox P R hPR)
      (fun x => mu ((fourierSquareEquiv N).symm x)) (delta * alpha ^ 2 / 4) (by positivity)
      (by omega) hmodd (fourierSquareBox_width P R hPR hPl hRl)
      (fourierSquareBox_axis_length P R hPR hPl hRl) hPs hmsqrt hf hmu.to_multilinear henergy
  have hconstant : (2 : Real) ^ (-(2 * (2 + 1) ^ 3 : Int)) * (delta * alpha ^ 2 / 4) =
      (2 : Real) ^ (-(58 : Int)) * alpha ^ 2 * (alpha / 2) ^ ((2 : Nat) ^ 42) := by
    dsimp [delta]
    generalize (alpha / 2) ^ ((2 : Nat) ^ 42) = a
    norm_num
    ring
  refine ⟨phi, M, l, Q, hpoly, hpartition, hproper, ?_,
    fun i => (by exact_mod_cast hupper i : ((Q i).length : Real) ≤ m).trans hmsqrt,
    by simpa only [Nat.cast_ofNat, hconstant] using hnonuniform⟩
  norm_num only [Nat.cast_ofNat] at hlength
  linarith only [hsize, hlength]

end LeanProofs.GowersSzemeredi
