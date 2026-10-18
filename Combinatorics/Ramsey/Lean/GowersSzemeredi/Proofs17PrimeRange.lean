import GowersSzemeredi.Proofs17PhaseRemoval
import GowersSzemeredi.Proofs17PhaseRemovalSide

/-! The prime-range statements require no separate factorial-unit premise.
The characteristic restriction remains explicit; this does not assert the
original unrestricted characteristic version. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

private theorem factorial_unit_below_prime {N q : Nat} [NeZero N]
    [Fact N.Prime] (hqN : q < N) :
    IsUnit ((Nat.factorial q : Nat) : ZMod N) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.factorial_succ, Nat.cast_mul]
      apply IsUnit.mul
      · rw [isUnit_iff_ne_zero]
        intro hz
        rw [ZMod.natCast_eq_zero_iff] at hz
        have hpos : 0 < q + 1 := by omega
        exact (Nat.not_lt_of_ge (Nat.le_of_dvd hpos hz)) hqN
      · exact ih (Nat.lt_trans (Nat.lt_succ_self q) hqN)

/-- Lemma17.1 throughout the documented prime characteristic range. -/
theorem lemma_17_1_prime_range (N k : Nat) [NeZero N] [Fact N.Prime]
    (hk : k < N) (sigma : Point N k → ZMod N) (hsigma : IsMultilinear sigma) :
    ∃ phi : (Fin k → Bool) → ZMod N → ZMod N,
      (∀ e, PolynomialOn k Finset.univ (phi e)) ∧
      ∀ s x, sigma x = signedCubeSum phi s x :=
  lemma_17_1_holds N k hk (factorial_unit_below_prime hk) sigma hsigma

/-- Proposition17.2 with the corrected degree and no redundant unit premise. -/
theorem proposition_17_2_prime_range (N k : Nat) [NeZero N] [Fact N.Prime]
    (f : ZMod N → Complex) (sigma : Point N k → ZMod N) (alpha : Real)
    (hk : k + 1 < N) (hf : DiscValued f) (hsigma : IsMultilinear sigma)
    (henergy : alpha * (N : Real) ^ (k + 2) ≤
      ∑ x : Point N k, ‖fourier (cubeDifference f x) (sigma x)‖ ^ 2) :
    ∃ phi : ZMod N → ZMod N,
      PolynomialOn (k + 1) Finset.univ phi ∧
      alpha * (N : Real) ^ (k + 2) ≤
        ∑ x : Point N k, ‖∑ s : ZMod N, cubeDifference (phaseTwist f phi) x s‖ ^ 2 :=
  proposition_17_2_holds N k f sigma alpha hk (factorial_unit_below_prime hk)
    hf hsigma henergy

end LeanProofs.GowersSzemeredi
