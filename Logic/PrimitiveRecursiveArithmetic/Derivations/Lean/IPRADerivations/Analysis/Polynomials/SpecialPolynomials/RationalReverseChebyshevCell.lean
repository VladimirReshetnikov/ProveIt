import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.RationalHalfNinthProductLower
import IPRADerivations.Analysis.RationalArithmetic.Powers.RationalPowerBounds.RationalReciprocalPowerTail

/-!
# A margin-preserving cell for reverse Chebyshev sums

The gap between the crossed and uncrossed products is
(b-a)(u-v). The rational code for that product preserves the product
of any two certified nonnegative lower gaps.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalReverseChebyshevCell

open_ipra
open GaussianPositiveRealArithmetic (sign)
open GaussianRationalL1 (nonnegative_of_lower)
open GaussianRationalSyntheticBounds (add_monotone)
open RationalAlgebra (add_congr add_associative add_commutative multiply_congr multiply_commutative multiply_add)
open RationalArgmin (rationalLE rationalLE_congr reflexive transitive)
open RationalArithmetic (add multiply negative add_guard multiply_monotone)
open RationalHalfNinthProductLower (add_negative_cancel)
open RationalNormalForm (wellFormed)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def difference (b a : PTm n) : PTm n := add b (negative a)

theorem restore (b a : PTm n) (hb : Γ ⊢[PRAAx] wellFormed b) :
    Γ ⊢[PRAAx] add a (difference b a) ≐ b :=
  (add_associative a b (negative a)).eqSymm.eqTrans
    ((add_congr (add_commutative a b) (.eqRefl _)).eqTrans (add_negative_cancel b a hb))

theorem lower_gap (a b c : PTm n) (hc : Γ ⊢[PRAAx] wellFormed c)
    (h : Γ ⊢[PRAAx] rationalLE (add a c) b) :
    Γ ⊢[PRAAx] rationalLE c (difference b a) := by
  let q := negative a
  have t := add_monotone (add a c) b q q h (reflexive q)
  have e := (add_congr (add_commutative a c) (.eqRefl q)).eqTrans (add_negative_cancel c a hc)
  exact rationalLE_congr e (.eqRefl _) t

private theorem add_multiply (a b c : PTm n) : Γ ⊢[PRAAx]
    multiply (add a b) c ≐ add (multiply a c) (multiply b c) :=
  (multiply_commutative _ _).eqTrans ((multiply_add c a b).eqTrans
    (add_congr (multiply_commutative c a) (multiply_commutative c b)))

private theorem swap_middle (a b c : PTm n) :
    Γ ⊢[PRAAx] add b (add a c) ≐ add a (add b c) :=
  (add_associative _ _ _).eqSymm.eqTrans
    ((add_congr (add_commutative _ _) (.eqRefl _)).eqTrans (add_associative _ _ _))

theorem rectangle_balance (a b u v : PTm n) (hb : Γ ⊢[PRAAx] wellFormed b) (hu : Γ ⊢[PRAAx] wellFormed u) :
    Γ ⊢[PRAAx] add (add (multiply a u) (multiply b v)) (multiply (difference b a) (difference u v)) ≐
      add (multiply a v) (multiply b u) := by
  let e := difference b a
  let f := difference u v
  let x := multiply a v
  let y := multiply a f
  let z := multiply e v
  let w := multiply e f
  have eb := restore b a hb
  have eu := restore u v hu
  have h₁ := (multiply_congr (.eqRefl a) eu.eqSymm).eqTrans (multiply_add a v f)
  have h₂ := (multiply_congr eb.eqSymm (.eqRefl v)).eqTrans (add_multiply a e v)
  have h₃ := (multiply_congr eb.eqSymm eu.eqSymm).eqTrans
    ((add_multiply a e (add v f)).eqTrans (add_congr (multiply_add a v f) (multiply_add e v f)))
  have group : Γ ⊢[PRAAx] add (add (add x y) (add x z)) w ≐ add x (add (add x y) (add z w)) :=
    (add_congr (swap_middle x (add x y) z) (.eqRefl _)).eqTrans
      ((add_associative x (add (add x y) z) w).eqTrans
        (add_congr (.eqRefl x) (add_associative (add x y) z w)))
  exact (add_congr (add_congr h₁ h₂) (.eqRefl _)).eqTrans
    (group.eqTrans (add_congr (.eqRefl x) h₃.eqSymm))

theorem rectangle_margin (a b u v c d : PTm n) (hb : Γ ⊢[PRAAx] wellFormed b)
    (hu : Γ ⊢[PRAAx] wellFormed u) (hc : Γ ⊢[PRAAx] wellFormed c) (hd : Γ ⊢[PRAAx] wellFormed d)
    (sc : Γ ⊢[PRAAx] sign c) (sd : Γ ⊢[PRAAx] sign d)
    (h₁ : Γ ⊢[PRAAx] rationalLE (add a c) b) (h₂ : Γ ⊢[PRAAx] rationalLE (add v d) u) :
    Γ ⊢[PRAAx] rationalLE (add (add (multiply a u) (multiply b v)) (multiply c d))
      (add (multiply a v) (multiply b u)) := by
  let e := difference b a
  let f := difference u v
  let l := add (multiply a u) (multiply b v)
  have hce := lower_gap a b c hc h₁
  have hdf := lower_gap v u d hd h₂
  have se := nonnegative_of_lower c e sc hce
  have first : Γ ⊢[PRAAx] rationalLE (multiply c d) (multiply e d) :=
    rationalLE_congr (multiply_commutative d c) (multiply_commutative d e) (multiply_monotone d c e sd hce)
  have second := multiply_monotone e d f se hdf
  exact rationalLE_congr (.eqRefl _) (rectangle_balance a b u v hb hu)
    (add_monotone l l (multiply c d) (multiply e f) (reflexive l) (transitive first second))

theorem reverse_Chebyshev_cell_margin_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (wellFormed (var 1) ⟶ wellFormed (var 2) ⟶ wellFormed (var 4) ⟶ wellFormed (var 5) ⟶
      sign (var 4) ⟶ sign (var 5) ⟶ rationalLE (add (var 0) (var 4)) (var 1) ⟶
      rationalLE (add (var 3) (var 5)) (var 2) ⟶
      rationalLE (add (add (multiply (var 0) (var 2)) (multiply (var 1) (var 3))) (multiply (var 4) (var 5)))
        (add (multiply (var 0) (var 3)) (multiply (var 1) (var 2)))) := by
  refine closeUniv 6 (.impI (.impI (.impI (.impI (.impI (.impI (.impI (.impI ?_))))))))
  exact rectangle_margin _ _ _ _ _ _ Prf.hyp1.wk.wk.wk.wk.wk.wk Prf.hyp1.wk.wk.wk.wk.wk Prf.hyp1.wk.wk.wk.wk
    Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0

end LeanProofs.IPRA.Analysis.RationalReverseChebyshevCell
