import GowersSzemeredi.Proofs13ExplicitFourierThreshold
import GowersSzemeredi.Proofs13OddFourierSquare

/-! Odd Fourier-square extraction above a completely explicit modulus. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section13OddSquareThreshold (alpha : Real) : Real :=
  max (section13FourierThreshold alpha)
    (positivePowerThreshold 4 1 ((1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88))))

theorem theorem_13_12_odd_square_explicit :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 →
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], section13OddSquareThreshold alpha ≤ N →
        ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
        ∃ m : Nat, ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
          Odd m ∧ 0 < m ∧ (m : Real) ≤ Real.sqrt N ∧
          (N : Real) ^ ((1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88))) / 2 ≤ m ∧
          P.step != 0 ∧ P.step = Q.step ∧ P.IsProper ∧ Q.IsProper ∧ P.length = m ∧ Q.length = m ∧
          B ⊆ P.carrier.product Q.carrier ∧
          (alpha / 2) ^ ((2 : Nat) ^ 76) / 4 * m * m ≤ B.card ∧
          BilinearOn (P.carrier.product Q.carrier) phi ∧
          ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ := by
  intro alpha hα hαone
  let e := (1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88))
  obtain ⟨he, hehalf⟩ := section13_explicit_exponent_bounds hα hαone
  intro N _ _ hN f hf hnot
  have hlarge : 4 ≤ (N : Real) ^ e := by
    have h := positivePowerThreshold_spec zero_lt_one he
      ((le_max_right _ _).trans hN : positivePowerThreshold 4 1 e ≤ (N : Real))
    simpa only [one_mul] using h
  obtain ⟨m, hmodd, hmpos, hmlower, hmupper⟩ := exists_odd_nat_between_half hlarge
  obtain ⟨S, T, D, psi, hSs, hST, hS, hT, hlen, hsize, hD, hmass, hbil, hfourier⟩ :=
    theorem_13_12_legacy_explicit_threshold alpha hα hαone N ((le_max_left _ _).trans hN) f hf hnot
  have hmS : m ≤ S.length := by exact_mod_cast hmupper.trans hsize
  have hmT : m ≤ T.length := by omega
  have hTstep : T.step != 0 := by rwa [← hST]
  obtain ⟨mu, hmu, hagree⟩ := hbil
  have hbilD : BilinearOn D psi := ⟨mu, hmu, fun z hz => hagree z (hD hz)⟩
  obtain ⟨P, Q, B, hPs, hQs, hP, hQ, hPl, hQl, hBD, hbox, hmass', _⟩ :=
    bilinear_square_of_integer_step_fit S T D psi ((alpha / 2) ^ ((2 : Nat) ^ 76)) 1 m
      hS hT hTstep (by simpa only [Nat.cast_one, one_mul] using hST.symm)
      (by omega) hmpos (by simpa only [one_mul] using hmS) hmT (by positivity) hD hmass hbilD
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast NeZero.pos N
  have hmsqrt : (m : Real) ≤ Real.sqrt N := by
    calc
      _ ≤ (N : Real) ^ e := hmupper
      _ ≤ (N : Real) ^ (1 / 2 : Real) := Real.rpow_le_rpow_of_exponent_le hNreal hehalf
      _ = _ := (Real.sqrt_eq_rpow _).symm
  refine ⟨m, P, Q, B, mu, hmodd, hmpos, hmsqrt, hmlower, ?_, hPs.trans hQs.symm,
    hP, hQ, hPl, hQl, hbox, hmass', ⟨mu, hmu, fun _ _ => rfl⟩, ?_⟩
  · rwa [hPs]
  · intro z hz
    rw [← hagree z (hD (hBD hz))]
    exact hfourier z (hBD hz)

end LeanProofs.GowersSzemeredi
