import IPRADerivations.Analysis.Gamma.EulerProducts.Gauss.Heads.GaussianGammaGaussEulerHeads
import IPRADerivations.Analysis.Gamma.EulerProducts.Factorials.GaussianGammaFallingFactorial

/-!
# Gauss denominator cancellation across two arguments

Use the same positive factorial at the Gauss cutoff for both arguments.
The common grouping factor cancels from the cross product of the
maintained Euler heads. The argument heads may vanish.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussEulerHeadCancellation

open_ipra
open ComplexLogarithmRemainder (scale)
open GaussianGammaEulerHead (run)
open GaussianGammaFallingFactorial (factorialInverse factorial_inverse_unit)
open GaussianGammaGaussEulerHeads (cutoff shiftedHeads grouped_euler_heads)
open GaussianRationalHorner (canonical qmul qmul_canonical)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem undo_factorial (q L : PTm n) (hq : Γ ⊢[PRAAx] canonical q) :
    Γ ⊢[PRAAx] qmul (qmul (naturalPoint (fact L)) q) (factorialInverse L) ≐ q := by
  let d := naturalPoint (fact L)
  let v := factorialInverse L
  exact (qmul_associative d q v).eqTrans
    ((qmul_congr (.eqRefl _) (qmul_commutative q v)).eqTrans
      ((qmul_associative d v q).eqSymm.eqTrans
        ((qmul_congr (factorial_inverse_unit L) (.eqRefl _)).eqTrans
          ((qmul_commutative _ _).eqTrans (qmul_one_right q hq)))))

theorem relative_head_grouping (z w B D m N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] qmul (run (scale m z) B (cutoff m N)) (shiftedHeads w D m N) ≐
      qmul (run (scale m w) D (cutoff m N)) (shiftedHeads z B m N) := by
  let L := cutoff m N
  let u := run (scale m z) B L
  let v := run (scale m w) D L
  let a := shiftedHeads z B m N
  let b := shiftedHeads w D m N
  let d := naturalPoint (fact L)
  have h₁ := grouped_euler_heads z B m N hB hm
  have h₂ := grouped_euler_heads w D m N hD hm
  have common : Γ ⊢[PRAAx] qmul d (qmul u b) ≐ qmul d (qmul v a) :=
    (qmul_associative _ _ _).eqSymm.eqTrans
      ((qmul_congr h₁ (.eqRefl _)).eqTrans
        ((qmul_associative _ _ _).eqTrans
          ((qmul_congr (.eqRefl _) (qmul_commutative a b)).eqTrans
            ((qmul_associative _ _ _).eqSymm.eqTrans
              ((qmul_congr h₂.eqSymm (.eqRefl _)).eqTrans (qmul_associative _ _ _))))))
  exact (undo_factorial (qmul u b) L (qmul_canonical _ _)).eqSymm.eqTrans
    ((qmul_congr common (.eqRefl _)).eqTrans (undo_factorial (qmul v a) L (qmul_canonical _ _)))

theorem original_Gauss_relative_head_grouping_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 2) ⟶ le one (var 3) ⟶ le one (var 4) ⟶
      qmul (run (scale (var 4) (var 0)) (var 2) (cutoff (var 4) (var 5)))
        (shiftedHeads (var 1) (var 3) (var 4) (var 5)) ≐
      qmul (run (scale (var 4) (var 1)) (var 3) (cutoff (var 4) (var 5)))
        (shiftedHeads (var 0) (var 2) (var 4) (var 5))) :=
  closeUniv 6 (.impI (.impI (.impI (relative_head_grouping _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGaussEulerHeadCancellation
