import GowersSzemeredi.Proofs16BoundedFrequencySpan
import GowersSzemeredi.Proofs16TrapezoidL1

/-! A quantitative bridge from a truncated trapezoid product to the bounded
span containing large Bohr Fourier coefficients. The remaining analytic
input is a uniform approximation of the trapezoid product. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- An explicit approximation budget forces a large Fourier coefficient
of a Bohr indicator into the bounded span of its defining frequencies. -/
theorem large_bohr_fourier_mem_boundedFrequencySpan {N : Nat} [NeZero N] [Fact N.Prime]
    (K : Finset (ZMod N)) (a c R : Nat) (hca : c ≤ a)
    (coeff : K → centeredBall N R → Complex) {delta epsilon : Real}
    (happrox : ∀ x : ZMod N,
      ‖((∏ gamma ∈ K, trapezoid a c (gamma * x) : Real) : Complex) -
        boundedCharacterProduct (fun gamma : K => (gamma : ZMod N)) R coeff x‖ ≤ delta)
    (hbudget : K.card * (4 * (c : Real) + 2) + delta * N < epsilon * N)
    {xi : ZMod N} (hlarge : epsilon * N ≤ ‖fourier (indicator (bohr K ((a : Real) / N))) xi‖) :
    xi ∈ boundedFrequencySpan (fun gamma : K => (gamma : ZMod N)) R := by
  apply large_fourier_mem_boundedFrequencySpan _ R coeff _ _ hlarge
  have htri : (∑ x : ZMod N, ‖indicator (bohr K ((a : Real) / N)) x -
      boundedCharacterProduct (fun gamma : K => (gamma : ZMod N)) R coeff x‖) ≤
      (∑ x : ZMod N, ‖indicator (bohr K ((a : Real) / N)) x -
        ((∏ gamma ∈ K, trapezoid a c (gamma * x) : Real) : Complex)‖) + delta * N := by
    calc
      _ ≤ ∑ x : ZMod N,
          (‖indicator (bohr K ((a : Real) / N)) x -
            ((∏ gamma ∈ K, trapezoid a c (gamma * x) : Real) : Complex)‖ + delta) := by
        apply Finset.sum_le_sum
        intro x _
        have ht := dist_triangle (indicator (bohr K ((a : Real) / N)) x)
          (((∏ gamma ∈ K, trapezoid a c (gamma * x) : Real) : Complex))
          (boundedCharacterProduct (fun gamma : K => (gamma : ZMod N)) R coeff x)
        simp only [dist_eq_norm] at ht
        linarith [happrox x]
      _ = _ := by rw [Finset.sum_add_distrib]; simp [mul_comm]
  have hL1 := trapezoid_product_l1_le K a c hca
  linarith

end LeanProofs.GowersSzemeredi
