import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import OAI.Combinatorics.Progressions.Estimates.SquarefreeSplitCount

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped Classical

variable {R : Type*} [CommRing R]

theorem multiaffine_eval_fin_cons {n : ℕ} (P : MvPolynomial (Fin (n + 1)) R)
    (hP : degreeOf 0 P ≤ 1) (x : R) (y : Fin n → R) :
    eval (Fin.cons x y) P =
      x * eval y ((finSuccEquiv R n P).coeff 1) +
        eval y ((finSuccEquiv R n P).coeff 0) := by
  rw [eval_eq_eval_mv_eval']
  have hd : (finSuccEquiv R n P).natDegree ≤ 1 := by
    rwa [natDegree_finSuccEquiv]
  calc
    _ = Polynomial.eval x (Polynomial.map (eval y)
        (Polynomial.C ((finSuccEquiv R n P).coeff 1) * Polynomial.X +
          Polynomial.C ((finSuccEquiv R n P).coeff 0))) :=
      congrArg (fun Q => Polynomial.eval x (Polynomial.map (eval y) Q))
        (Polynomial.eq_X_add_C_of_natDegree_le_one hd)
    _ = _ := by simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]; rw [mul_comm]

theorem multiaffine_finSuccEquiv_coeff {n : ℕ} (P : MvPolynomial (Fin (n + 1)) R)
    (hP : ∀ j, degreeOf j P ≤ 1) (i : ℕ) :
    ∀ j, degreeOf j ((finSuccEquiv R n P).coeff i) ≤ 1 := by
  intro j
  exact (degreeOf_coeff_finSuccEquiv P j i).trans (hP j.succ)

theorem fullSquarefree_finSuccEquiv_coeff {n : ℕ} (P : MvPolynomial (Fin (n + 1)) R) :
    ((finSuccEquiv R n P).coeff 1).coeff
        (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val =
      P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n + 1)))).val := by
  rw [finSuccEquiv_coeff_coeff]
  congr 1
  ext j
  refine Fin.cases ?_ (fun i => ?_) j <;>
    simp [SquarefreeIndex.ofFinset_apply]

end Erdos3

end

end OAI
