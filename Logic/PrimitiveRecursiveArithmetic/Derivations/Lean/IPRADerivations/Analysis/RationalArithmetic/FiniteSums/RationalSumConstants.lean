import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalSumLinearity
import IPRADerivations.Analysis.RationalArithmetic.Powers.RationalReciprocalPowerTail

/-!
# Exact rational sums of a constant

A finite scalar sum of a canonical rational constant equals that
constant multiplied by the literal natural length of the sum.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalSumConstants

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product)
open RationalAlgebra (add_congr multiply_congr)
open RationalArithmetic (add multiply)
open RationalFiniteSum (sum term)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private def oneBody : PTm 2 := fraction one one
def constantBody : PTm 2 := var 1

theorem term_constant (i c : PTm n) : term constantBody i c = c := by
  simp [term,constantBody,inst2]

theorem multiply_one_right (c : PTm n) (hc : Γ ⊢[PRAAx] RationalNormalForm.wellFormed c) :
    Γ ⊢[PRAAx] multiply c (fraction one one) ≐ c := by
  have hD := RationalArgmin.denominator_positive (Γ := Γ) c
  have e := RationalRepresentations.represents_multiply _ _ _ _ _ _
    (RationalRepresentations.represents_self (Γ := Γ) c) (fraction_represents one one (le_refl one))
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.multiply_guard _ _) hc e
    (RationalRepresentations.represents_self c) (positive_product _ _ hD (le_refl _)) hD
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,IPRA.Q.mk_one,map_one,IPRA.Q.mk_mul,_root_.mul_one]

theorem count_add (j k : PTm n) : Γ ⊢[PRAAx] add (fraction j one) (fraction k one) ≐ fraction (j+k) one := by
  have D : Γ ⊢[PRAAx] le one (one*one : PTm n) := by ipra_le 0
  have e := RationalRepresentations.represents_add _ _ _ _ _ _
    (fraction_represents j one (le_refl one : Γ ⊢[PRAAx] _)) (fraction_represents k one (le_refl one))
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one)) e (fraction_represents _ _ (le_refl one)) D (le_refl one)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_add]
  ipra_simps
  ring

private theorem fraction_add_one (j : PTm n) : Γ ⊢[PRAAx] add (fraction j one) (fraction one one) ≐ fraction (succ j) one :=
  (count_add j one).eqTrans (RationalNonnegativePowers.fraction_congr (succ_eq_add_one j).eqSymm (.eqRefl one))

private theorem sum_ones (j : PTm n) : Γ ⊢[PRAAx] sum oneBody j zero ≐ fraction j one := by
  have all : Γ ⊢[PRAAx] .all (sum oneBody (var 0) zero ≐ fraction (var 0) one) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp [Syn.inst_zero]
      exact (RationalFiniteSum.sum_zero oneBody zero).eqTrans RationalReciprocalPowerTail.zero_fraction.eqSymm
    · simp [Syn.repl_zero]
      have ei : term oneBody (var 0 : PTm (n+1)) zero = fraction one one := by
        simp [term,oneBody,inst2]
      have hterm : (sum oneBody (var 0) zero ≐ fraction (var 0) one) :: Γ.map Fm.shift ⊢[PRAAx]
          term oneBody (var 0) zero ≐ fraction one one := by
        rw [ei]
        exact .eqRefl _
      exact (RationalFiniteSum.sum_succ oneBody (var 0) zero).eqTrans
        ((add_congr Prf.hyp0 hterm).eqTrans (fraction_add_one _))
  simpa [Syn.inst_zero] using all.allE j

theorem sum_constant (K c : PTm n) (hc : Γ ⊢[PRAAx] RationalNormalForm.wellFormed c) :
    Γ ⊢[PRAAx] sum constantBody K c ≐ multiply c (fraction K one) := by
  have h : Γ ⊢[PRAAx] RationalFiniteSum.termwiseEq constantBody (RationalSumLinearity.scaledBody oneBody) K
      c (pairT c zero) := by
    refine .allI (.impI ?_)
    have h₁ := RationalSumLinearity.scaled_term (Γ := lt (var 0) (Syn.shift K) :: Γ.map Fm.shift)
      oneBody (var 0) (Syn.shift c) zero
    simp only [term_constant,Syn.shift,subst_pairT,ConciseIPRA.PTm.subst_zero]
    apply RationalArgmin.rationalEq_congr (.eqRefl _) h₁.eqSymm
    have e : term oneBody (var 0 : PTm (n+1)) zero = fraction one one := by simp [term,oneBody,inst2]
    rw [e]
    have hc' : Γ.map Fm.shift ⊢[PRAAx] RationalNormalForm.wellFormed (Syn.shift c) :=
      by simpa [Fm.shift,Syn.shift] using hc.shift
    exact RationalArgmin.rationalEq_congr (.eqRefl _) (multiply_one_right _ hc'.wk).eqSymm (.eqRefl _)
  exact (RationalFiniteSum.sum_ext _ _ _ _ _ h).eqTrans ((RationalSumLinearity.sum_homogeneous oneBody K c zero).eqTrans
    (multiply_congr (.eqRefl _) (sum_ones K)))

end LeanProofs.IPRA.Analysis.RationalSumConstants
