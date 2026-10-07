import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped ContDiff

theorem contDiff_mvPolynomial_aeval {σ R E : Type*} [CommSemiring R] [Algebra R ℝ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ∞ω}
    (P : MvPolynomial σ R) (f : σ → E → ℝ)
    (hf : ∀ i, ContDiff ℝ n (f i)) :
    ContDiff ℝ n (fun x => aeval (fun i => f i x) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa only [aeval_C] using (contDiff_const (c := algebraMap R ℝ a))
  | add P Q hP hQ => simpa only [map_add] using hP.add hQ
  | mul_X P i hP => simpa only [map_mul, aeval_X] using hP.mul (hf i)

theorem contDiff_mvPolynomial {σ R : Type*} [Fintype σ] [CommSemiring R] [Algebra R ℝ]
    (P : MvPolynomial σ R) (n : ℕ∞ω) :
    ContDiff ℝ n (fun x : σ → ℝ => aeval x P) :=
  contDiff_mvPolynomial_aeval (E := σ → ℝ) (n := n) P
    (fun i (x : σ → ℝ) => x i) (fun i => contDiff_apply ℝ ℝ i)

end Erdos3

end

end OAI
