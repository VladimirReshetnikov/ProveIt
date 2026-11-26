import IPRADerivations.Analysis.RationalArithmetic.GaussianPositiveRealArithmetic
import IPRADerivations.Analysis.RationalArithmetic.RationalGaussianRealPart
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalUpperRepresentation

/-!
# Sign certificates for original digamma grid observations

The bounded-search test reads the signed numerator of a rational code.
These finite lemmas transfer the represented endpoint margins to that
test and the adjacent-cell error to a two-sided radius about zero.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaGridSign

open_ipra
open GaussianPositiveRealArithmetic (sign)
open GaussianRationalHorner (positive_product)
open RationalGaussianEmbedding (scalarZero)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalArgmin (rationalLE left)
open RationalValueBounds (upper radius upper_of_order upper_order_left upper_order_right radius_of_upper positive_cancel)
open RationalUpperRepresentation (upper_from_representations)
open RationalArithmetic (represents)
open RationalIntegerNormalization (integerCode positivePart negativePart)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

private theorem zero_code : Γ ⊢[PRAAx] (scalarZero : PTm n) ≐ pairT (pairT zero zero) zero := by
  refine RationalGaussianRealPart.scalar_zero_integer.eqTrans ?_
  dsimp only [integerCode,positivePart,negativePart,ZT.natLit,ZT.ofNat]
  exact congrPairT (congrPairT (monus_self zero) (monus_self zero)) (.eqRefl _)

private theorem zero_left (x : PTm n) : Γ ⊢[PRAAx] left scalarZero x ≐ (numeratorOf x).neg := by
  have e := zero_code (Γ := Γ) (n := n)
  have p := ((congrFst (congrFst e)).eqTrans (congrFst (fst_pair _ _))).eqTrans (fst_pair _ _)
  have d := congrSucc e.sndE
  exact (congrAdd (congrMul p (.eqRefl _)) (congrMul (.eqRefl _) d)).eqTrans (by ipra_ring)

private theorem zero_right (x : PTm n) : Γ ⊢[PRAAx] left x scalarZero ≐ (numeratorOf x).pos := by
  have e := zero_code (Γ := Γ) (n := n)
  have k := ((congrSnd (congrFst e)).eqTrans (congrSnd (fst_pair _ _))).eqTrans (snd_pair _ _)
  have d := congrSucc e.sndE
  exact (congrAdd (congrMul (.eqRefl _) d) (congrMul k (.eqRefl _))).eqTrans (by ipra_ring)

theorem zero_le_of_sign (x : PTm n) (h : Γ ⊢[PRAAx] sign x) :
    Γ ⊢[PRAAx] rationalLE scalarZero x :=
  le_congr (zero_left x).eqSymm (zero_right x).eqSymm h

theorem sign_of_zero_le (x : PTm n) (h : Γ ⊢[PRAAx] rationalLE scalarZero x) :
    Γ ⊢[PRAAx] sign x :=
  le_congr (zero_left x) (zero_right x) h

theorem sign_iff_zero_le (x : PTm n) : Γ ⊢[PRAAx] Fm.iff (sign x) (rationalLE scalarZero x) :=
  .andI (.impI (zero_le_of_sign x Prf.hyp0)) (.impI (sign_of_zero_le x Prf.hyp0))

theorem le_zero_of_negative (x : PTm n) (h : Γ ⊢[PRAAx] neg (sign x)) :
    Γ ⊢[PRAAx] rationalLE x scalarZero := by
  apply le_congr (zero_right x).eqSymm (zero_left x).eqSymm
  exact .orE (le_total (numeratorOf x).pos (numeratorOf x).neg) Prf.hyp0 (.botE _ (.impE h.wk Prf.hyp0))

private theorem quarter_margin (U D : PTm n) (hU : Γ ⊢[PRAAx] le (num 16) U)
    (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] lt ((U+U)*D*num 4) ((U*U)*D) := by
  have hp : Γ ⊢[PRAAx] le one U := le_trans (by ipra_le 15) hU
  unfold lt
  ipra_le 𝔞(U)*𝔞(D)*sl hU+8*𝔞(U)*sl hD+8*sl hp+7

theorem negative_from_upper (x c U : PTm n) (hU : Γ ⊢[PRAAx] le (num 16) U)
    (hc : Γ ⊢[PRAAx] represents c (-ZT.ofNat one) (num 4))
    (h : Γ ⊢[PRAAx] upper x c (U+U) (U*U)) :
    Γ ⊢[PRAAx] neg (sign x) := by
  let D := denominatorOf x
  let P := (U*U)*num 4
  let A := (U+U)*D*num 4
  let v := numeratorOf x
  let l := ZT.ofNat P*v
  let r := ZT.ofNat ((U*U)*D)*(-ZT.ofNat one)+ZT.ofNat A
  have hs : Γ ⊢[PRAAx] zle l r :=
    upper_from_representations x c D (num 4) (U+U) (U*U) v (-ZT.ofNat one)
      (RationalRepresentations.represents_self x) hc h
  have clear : Γ ⊢[PRAAx] le (P*v.pos+(U*U)*D) (P*v.neg+A) := by
    apply le_of_eq_add (d := PolynomialBisection.slack l r)
    have e := zle_toZ hs
    apply deriveNat
    change ZT.toZ Γ (ZT.ofNat P*v)+𝔞(PolynomialBisection.slack l r) =
      ZT.toZ Γ (ZT.ofNat ((U*U)*D)*(-ZT.ofNat one)+ZT.ofNat A) at e
    simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_neg,ZT.toZ_ofNat] at e
    simp only [ZT.toZ] at e
    ipra_simps
    linear_combination -e
  refine .impI ?_
  have m : (sign x :: Γ) ⊢[PRAAx] lt A ((U*U)*D) :=
    quarter_margin U D hU.wk (RationalValueBounds.denominator_positive x)
  have impossible : (sign x :: Γ) ⊢[PRAAx] lt (P*v.neg+A) (P*v.neg+A) := by
    unfold lt at m ⊢
    have s : (sign x :: Γ) ⊢[PRAAx] le v.neg v.pos := Prf.hyp0
    ipra_le sl clear.wk+sl m+Groth.ι (Q.mk (sign x :: Γ) P)*sl s
  exact lt_irrefl _ _ impossible

theorem nonnegative_from_upper (x c U : PTm n) (hU : Γ ⊢[PRAAx] le (num 16) U)
    (hc : Γ ⊢[PRAAx] represents c (ZT.ofNat one) (num 4))
    (h : Γ ⊢[PRAAx] upper c x (U+U) (U*U)) :
    Γ ⊢[PRAAx] sign x := by
  let D := denominatorOf x
  let P := (U*U)*num 4
  let A := (U+U)*D*num 4
  let v := numeratorOf x
  let l := ZT.ofNat ((U*U)*D)*ZT.ofNat one
  let r := ZT.ofNat P*v+ZT.ofNat ((U+U)*num 4*D)
  have hs : Γ ⊢[PRAAx] zle l r :=
    upper_from_representations c x (num 4) D (U+U) (U*U) (ZT.ofNat one) v hc
      (RationalRepresentations.represents_self x) h
  have clear : Γ ⊢[PRAAx] le (P*v.neg+(U*U)*D) (P*v.pos+A) := by
    apply le_of_eq_add (d := PolynomialBisection.slack l r)
    have e := zle_toZ hs
    apply deriveNat
    change ZT.toZ Γ (ZT.ofNat ((U*U)*D)*ZT.ofNat one)+𝔞(PolynomialBisection.slack l r) =
      ZT.toZ Γ (ZT.ofNat P*v+ZT.ofNat ((U+U)*num 4*D)) at e
    simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at e
    simp only [ZT.toZ] at e
    dsimp only [A]
    ipra_simps
    linear_combination -e
  have m := le_trans (le_succ_self A) (quarter_margin U D hU (RationalValueBounds.denominator_positive x))
  have hp : Γ ⊢[PRAAx] le one U := le_trans (by ipra_le 15) hU
  apply positive_cancel (c := P) (positive_product _ _ (positive_product _ _ hp hp) (by ipra_le 3))
  ipra_le sl clear+sl m

theorem near_zero_left (x y A B : PTm n)
    (hx : Γ ⊢[PRAAx] neg (sign x)) (hy : Γ ⊢[PRAAx] sign y) (h : Γ ⊢[PRAAx] upper y x A B) :
    Γ ⊢[PRAAx] radius x scalarZero A B :=
  radius_of_upper x scalarZero A B (upper_of_order _ _ _ _ (le_zero_of_negative x hx))
    (upper_order_left _ _ _ _ _ (zero_le_of_sign y hy) h)

theorem near_zero_right (x y A B : PTm n)
    (hx : Γ ⊢[PRAAx] neg (sign x)) (hy : Γ ⊢[PRAAx] sign y) (h : Γ ⊢[PRAAx] upper y x A B) :
    Γ ⊢[PRAAx] radius y scalarZero A B :=
  radius_of_upper y scalarZero A B (upper_order_right _ _ _ _ _ h (le_zero_of_negative x hx))
    (upper_of_order _ _ _ _ (zero_le_of_sign y hy))

theorem actual_original_digamma_grid_quarter_signs_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (le (num 16) (var 2) ⟶
        ((represents (var 1) (-ZT.ofNat one) (num 4) ⋏ upper (var 0) (var 1) (var 2+var 2) (var 2*var 2)) ⟶ neg (sign (var 0))) ⋏
        ((represents (var 1) (ZT.ofNat one) (num 4) ⋏ upper (var 1) (var 0) (var 2+var 2) (var 2*var 2)) ⟶ sign (var 0))) :=
  closeUniv 3 (.impI (.andI
    (.impI (negative_from_upper _ _ _ Prf.hyp1 Prf.hyp0.andE₁ Prf.hyp0.andE₂))
    (.impI (nonnegative_from_upper _ _ _ Prf.hyp1 Prf.hyp0.andE₁ Prf.hyp0.andE₂))))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaGridSign
