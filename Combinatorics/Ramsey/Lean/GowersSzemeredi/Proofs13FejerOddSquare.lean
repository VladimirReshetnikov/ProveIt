import GowersSzemeredi.Proofs13OddSquareBounds
import GowersSzemeredi.Proofs13FejerExplicitExponent

/-! Odd Fourier-square extraction above a completely explicit modulus.

`section13_fejer_explicit_exponent_bounds` and
`theorem_13_12_fejer_odd_square_explicit` are in `Proofs13FejerOddSquareSide`,
outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A Fejér square extraction at exponent `e` above `T`. -/
def FejerSquareAt (alpha e T : Real) : Prop :=
  ∀ (N : Nat) [NeZero N] [Fact N.Prime], T ≤ N →
    ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
    ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
      P.step != 0 ∧ P.step = Q.step ∧ P.IsProper ∧ Q.IsProper ∧ P.length = Q.length ∧
      (N : Real) ^ e ≤ P.length ∧
      B ⊆ P.carrier.product Q.carrier ∧
      (alpha / 2) ^ ((2 : Nat) ^ 42) * P.length * Q.length ≤ B.card ∧
      BilinearOn (P.carrier.product Q.carrier) phi ∧
      ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖

/-- An odd Fejér square extraction at exponent `e` above `T`. -/
def FejerOddSquareAt (alpha e T : Real) : Prop :=
  ∀ (N : Nat) [NeZero N] [Fact N.Prime], T ≤ N →
    ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
    ∃ m : Nat, ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
      Odd m ∧ 0 < m ∧ (m : Real) ≤ Real.sqrt N ∧ (N : Real) ^ e / 2 ≤ m ∧
      P.step != 0 ∧ P.step = Q.step ∧ P.IsProper ∧ Q.IsProper ∧ P.length = m ∧ Q.length = m ∧
      B ⊆ P.carrier.product Q.carrier ∧
      (alpha / 2) ^ ((2 : Nat) ^ 42) / 4 * m * m ≤ B.card ∧
      BilinearOn (P.carrier.product Q.carrier) phi ∧
      ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖

/-- **The odd square** at any exponent in `(0, 1/2]`. -/
theorem FejerSquareAt.oddSquare {alpha e T : Real} (h : FejerSquareAt alpha e T)
    (hα : 0 < alpha) (he : 0 < e) (hehalf : e ≤ 1 / 2) :
    FejerOddSquareAt alpha e (max T (positivePowerThreshold 4 1 e)) := by
  intro N _ _ hN f hf hnot
  obtain ⟨m, hmodd, hmpos, hmlower, hmupper⟩ := exists_odd_nat_between_half
    ((positivePowerThreshold_spec zero_lt_one he ((le_max_right _ _).trans hN)).trans_eq
      (one_mul _))
  obtain ⟨S, T, D, psi, hSs, hST, hS, hT, hlen, hsize, hD, hmass, ⟨mu, hmu, hagree⟩,
    hfourier⟩ := h N ((le_max_left _ _).trans hN) f hf hnot
  have hmS : m ≤ S.length := by exact_mod_cast hmupper.trans hsize
  have hTstep : T.step != 0 := hST ▸ hSs
  obtain ⟨P, Q, B, hPs, hQs, hP, hQ, hPl, hQl, hBD, hbox, hmass', _⟩ :=
    bilinear_square_of_integer_step_fit S T D psi ((alpha / 2) ^ ((2 : Nat) ^ 42)) 1 m
      hS hT hTstep (by simpa only [Nat.cast_one, one_mul] using hST.symm) one_pos hmpos
      (by omega) (by omega) (by positivity) hD hmass ⟨mu, hmu, fun z hz ↦ hagree z (hD hz)⟩
  refine ⟨m, P, Q, B, mu, hmodd, hmpos, hmupper.trans ((Real.rpow_le_rpow_of_exponent_le
    (Nat.one_le_cast.mpr (NeZero.pos N)) hehalf).trans_eq (Real.sqrt_eq_rpow _).symm), hmlower,
    hPs ▸ hTstep, hPs.trans hQs.symm, hP, hQ, hPl, hQl, hbox, hmass', ⟨mu, hmu, fun _ _ ↦ rfl⟩,
    fun z hz ↦ hagree z (hD (hBD hz)) ▸ hfourier z (hBD hz)⟩

def section13FejerOddSquareThreshold (alpha : Real) : Real :=
  max (section13FourierThreshold alpha)
    (positivePowerThreshold 4 1 ((1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 53))))

end LeanProofs.GowersSzemeredi
