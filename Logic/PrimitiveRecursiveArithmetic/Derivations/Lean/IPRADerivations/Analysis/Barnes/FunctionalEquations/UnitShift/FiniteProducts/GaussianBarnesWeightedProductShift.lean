import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalFiniteProduct
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalPowerAlgebra

/-!
# The finite weighted product shift in the Barnes recurrence

At every cutoff (N), multiplying the shifted weighted product by the
unweighted product clears all denominators that would come from taking
the ratio. The identity also covers zero factors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesWeightedProductShift

open_ipra
open GaussianRationalFiniteProduct (qprod product_zero product_succ)
open GaussianRationalHorner (qmul)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (power power_succ power_zero)
open GaussianRationalSyntheticDivision (qmul_congr qone)
open GaussianReciprocalHorner (qmul_associative)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def weighted (f : PR 2) : PTm 2 := power (ap2 f (var 0) (var 1)) (succ (var 0))
def shifted (f : PR 2) : PTm 2 := power (ap2 f (succ (var 0)) (var 1)) (succ (var 0))
def unweighted (f : PR 2) : PTm 2 := ap2 f (var 0) (var 1)

def shiftLaw (f : PR 2) (N x : PTm n) : Fm PTm n :=
  qmul (qprod (shifted f) N x) (qprod (unweighted f) N x) ≐
    qmul (qprod (weighted f) N x) (power (ap2 f N x) N)

@[simp] theorem subst_shiftLaw {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (N x : PTm n) :
    (shiftLaw f N x).subst σ = shiftLaw f (Syn.subst σ N) (Syn.subst σ x) := by
  simp [shiftLaw]

theorem at_zero (f : PR 2) (x : PTm n) : Γ ⊢[PRAAx] shiftLaw f zero x :=
  (qmul_congr (product_zero (shifted f) x) (product_zero (unweighted f) x)).eqTrans
    (qmul_congr (product_zero (weighted f) x) (power_zero (ap2 f zero x))).eqSymm

private theorem rotate (a b c d : PTm n) : Γ ⊢[PRAAx]
    qmul (qmul a b) (qmul c d) ≐ qmul (qmul (qmul a c) d) b := by
  have reassociate := qmul_associative (Γ := Γ) a b (qmul c d)
  have swap := qmul_congr (.eqRefl a) (qmul_commutative (Γ := Γ) b (qmul c d))
  exact reassociate.eqTrans (swap.eqTrans
    ((qmul_associative a (qmul c d) b).eqSymm.eqTrans
      (qmul_congr (qmul_associative a c d).eqSymm (.eqRefl b))))

theorem at_succ (f : PR 2) (N x : PTm n) (h : Γ ⊢[PRAAx] shiftLaw f N x) :
    Γ ⊢[PRAAx] shiftLaw f (succ N) x := by
  let P := qprod (weighted f) N x
  let Q := qprod (shifted f) N x
  let U := qprod (unweighted f) N x
  let a := ap2 f N x
  let b := power (ap2 f (succ N) x) (succ N)
  have p : Γ ⊢[PRAAx] qprod (weighted f) (succ N) x ≐ qmul P (power a (succ N)) := by
    simpa [weighted,inst2,P,a] using product_succ (Γ := Γ) (weighted f) N x
  have q : Γ ⊢[PRAAx] qprod (shifted f) (succ N) x ≐ qmul Q b := by
    simpa [shifted,inst2,Q,b] using product_succ (Γ := Γ) (shifted f) N x
  have u : Γ ⊢[PRAAx] qprod (unweighted f) (succ N) x ≐ qmul U a := by
    simpa [unweighted,inst2,U,a] using product_succ (Γ := Γ) (unweighted f) N x
  have middle : Γ ⊢[PRAAx] qmul (qmul Q U) a ≐ qmul P (power a (succ N)) :=
    (qmul_congr h (.eqRefl a)).eqTrans
      ((qmul_associative P (power a N) a).eqTrans (qmul_congr (.eqRefl P) (power_succ a N).eqSymm))
  exact (qmul_congr q u).eqTrans ((rotate Q b U a).eqTrans
    (qmul_congr (middle.eqTrans p.eqSymm) (.eqRefl b)))

theorem shift_product (f : PR 2) (N x : PTm n) : Γ ⊢[PRAAx] shiftLaw f N x := by
  have h : Γ ⊢[PRAAx] .all (shiftLaw f (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_shiftLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using at_zero (Γ := Γ) f x
    · simpa only [subst_shiftLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        at_succ f (var 0) (Syn.shift x) (Prf.hyp0 (Ax := PRAAx))
  simpa only [subst_shiftLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE N

theorem actual_finite_Barnes_weighted_product_shift_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (shiftLaw f (var 0) (var 1)) :=
  closeUniv 2 (shift_product f _ _)

end LeanProofs.IPRA.Analysis.GaussianBarnesWeightedProductShift
