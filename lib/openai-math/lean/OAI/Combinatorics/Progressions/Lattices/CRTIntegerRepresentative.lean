import OAI.Combinatorics.Progressions.Fourier.CRTConfigurationTorus
import OAI.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators
open MvPolynomial

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

noncomputable def crtIntegerCoefficient (j : J) : ℤ :=
  ((ZMod.prodEquivPi N hN).symm (Pi.single j (1 : ZMod (N j)))).val

noncomputable def crtIntegerRepresentative (u : J → ℤ) : ℤ :=
  ∑ j, crtIntegerCoefficient N hN j * u j

theorem crtIntegerRepresentative_cast (u : J → ℤ) :
    (crtIntegerRepresentative N hN u : ZMod (∏ j, N j)) =
      (ZMod.prodEquivPi N hN).symm (fun j => (u j : ZMod (N j))) := by
  let E := ZMod.prodEquivPi N hN
  have hcoeff (j : J) : (crtIntegerCoefficient N hN j : ZMod (∏ j, N j)) =
      E.symm (Pi.single j (1 : ZMod (N j))) := by
    simp only [crtIntegerCoefficient, Int.cast_natCast, ZMod.natCast_zmod_val, E]
  calc
    _ = ∑ j, E.symm (Pi.single j (1 : ZMod (N j))) * (u j : ZMod (∏ j, N j)) := by
      simp only [crtIntegerRepresentative, Int.cast_sum, Int.cast_mul, hcoeff]
    _ = E.symm (∑ j, Pi.single j (1 : ZMod (N j)) * (u j : (j : J) → ZMod (N j))) := by
      simp only [map_sum, map_mul, map_intCast]
    _ = _ := by
      congr 1
      funext j
      simp only [Finset.sum_apply, Pi.mul_apply, Pi.intCast_apply]
      rw [Finset.sum_eq_single j]
      · simp only [Pi.single_eq_same, one_mul]
      · intro i _ hij
        rw [Pi.single_eq_of_ne hij.symm, zero_mul]
      · simp

noncomputable def crtRepresentativePolynomial : MvPolynomial J ℝ :=
  ∑ j, ((crtIntegerCoefficient N hN j : ℝ) / (∏ i, N i : ℕ)) • X j

omit [NeZero (∏ j, N j)] in
theorem crtRepresentativePolynomial_degree :
    crtRepresentativePolynomial N hN ∈ weightedSupportLE (fun _ => 1) 1 := by
  apply Submodule.sum_mem
  intro j _
  exact (weightedSupportLE _ _).smul_mem _ (weightedSupportLE_X _ j)

omit [NeZero (∏ j, N j)] in
theorem crtRepresentativePolynomial_eval (u : J → ℤ) :
    aeval (fun j => (u j : ℝ)) (crtRepresentativePolynomial N hN) =
      (crtIntegerRepresentative N hN u : ℝ) / (∏ i, N i : ℕ) := by
  simp only [crtRepresentativePolynomial, map_sum, map_smul, aeval_X,
    smul_eq_mul, crtIntegerRepresentative, Int.cast_sum, Int.cast_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Erdos3

end

end OAI
