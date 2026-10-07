import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped ContDiff

theorem mvPolynomial_contDiff_eval {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) : ContDiff ℝ ∞ (fun a : ι → ℝ => MvPolynomial.eval a p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simpa only [MvPolynomial.eval_C] using (contDiff_const (c := r))
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
    have h := hp.mul (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).contDiff
    simp only [ContinuousLinearMap.proj_apply] at h
    simp only [map_mul, MvPolynomial.eval_X]
    exact h

theorem mvPolynomial_hasDerivAt_update {ι : Type*} [DecidableEq ι]
    (p : MvPolynomial ι ℝ) (j : ι) (a : ι → ℝ) :
    HasDerivAt (fun t => MvPolynomial.eval (Function.update a j t) p)
      (MvPolynomial.eval a (MvPolynomial.pderiv j p)) (a j) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    simpa only [MvPolynomial.eval_C, MvPolynomial.pderiv_C, map_zero] using hasDerivAt_const (a j) r
  | add p q hp hq =>
    have h := HasDerivAt.add hp hq
    simp only [map_add]
    exact h
  | mul_X p i hp =>
    by_cases hi : i = j
    · subst i
      have h := hp.mul (hasDerivAt_id (a j))
      simp only [id_eq, Function.update_eq_self, mul_one] at h
      simp only [map_mul, MvPolynomial.eval_X, Function.update_self, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_X_self, map_add, mul_one]
      exact h
    · have h := hp.mul (hasDerivAt_const (a j) (a i))
      simp only [Function.update_eq_self, mul_zero, add_zero] at h
      simp only [map_mul, MvPolynomial.eval_X, Function.update_of_ne hi, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_X_of_ne hi, mul_zero,
        add_zero]
      exact h

theorem mvPolynomial_fderiv_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) (a : ι → ℝ) (j : ι) :
    fderiv ℝ (fun x : ι → ℝ => MvPolynomial.eval x p) a (Pi.single j 1) =
      MvPolynomial.eval a (MvPolynomial.pderiv j p) := by
  have hupdate : HasDerivAt (fun t => Function.update a j t) (Pi.single j 1) (a j) := by
    apply hasDerivAt_pi.mpr
    intro i
    by_cases hi : i = j
    · subst i
      simp only [Function.update_self, Pi.single_eq_same]
      exact hasDerivAt_id (a j)
    · simpa [Function.update_of_ne hi, Pi.single_eq_of_ne hi] using hasDerivAt_const (a j) (a i)
  have hp := (mvPolynomial_contDiff_eval p).differentiable (by norm_num)
  have hf : HasFDerivAt (fun x : ι → ℝ => MvPolynomial.eval x p)
      (fderiv ℝ (fun x : ι → ℝ => MvPolynomial.eval x p) a) (Function.update a j (a j)) := by
    rw [Function.update_eq_self]
    exact (hp a).hasFDerivAt
  have h := hf.comp_hasDerivAt (a j) hupdate
  simp only [Function.comp_def] at h
  exact h.unique (mvPolynomial_hasDerivAt_update p j a)

end Erdos3

end

end OAI
