import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalRepresentations
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalIdentities.RationalFiniteSum

/-!
# Canonical rational algebra and affine order

Associativity, distribution, negation and midpoint identities are literal
equalities of actual canonical output codes. Input codes may be unreduced
and have noncanonical signed numerator pairs. Representation composition
keeps independent decoded denominators and cancels only positive natural
factors. The affine order lemmas support the concrete slab closure laws.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalAlgebra

open_ipra
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Analysis.RationalArithmetic
open LeanProofs.IPRA.Analysis.RationalRepresentations
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE rationalEq left denominator_positive)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCenters
  (midpoint midpointNumerator midpointDenominator midpoint_denominator_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem positive_product {A B : PTm n} (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] le one (A*B) :=
  le_congr (one_mul one) (.eqRefl _) (le_mul_mono hA hB)

theorem add_congr {a a' b b' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] add a b ≐ add a' b' :=
  (add_at a b).eqSymm.eqTrans ((congrAp2 addF ha hb).eqTrans (add_at a' b'))
theorem multiply_congr {a a' b b' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] multiply a b ≐ multiply a' b' :=
  (multiply_at a b).eqSymm.eqTrans ((congrAp2 multiplyF ha hb).eqTrans (multiply_at a' b'))
theorem negative_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] negative a ≐ negative b :=
  (negative_at a).eqSymm.eqTrans ((congrAp1 negativeF h).eqTrans (negative_at b))

theorem add_commutative (a b : PTm n) : Γ ⊢[PRAAx] add a b ≐ add b a := by
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (add_guard a b) (add_guard b a)
    (add_value a b) (add_value b a) (product_denominator_positive a b) (product_denominator_positive b a)
  ipra_lc [addNumerator, productDenominator]

theorem multiply_commutative (a b : PTm n) : Γ ⊢[PRAAx] multiply a b ≐ multiply b a := by
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (multiply_guard a b) (multiply_guard b a)
    (multiply_value a b) (multiply_value b a) (product_denominator_positive a b) (product_denominator_positive b a)
  ipra_lc [productDenominator]

theorem add_associative (a b c : PTm n) : Γ ⊢[PRAAx] add (add a b) c ≐ add a (add b c) := by
  have hl := represents_add (Γ := Γ) (add a b) c _ _ _ _ (add_value a b) (represents_self c)
  have hr := represents_add (Γ := Γ) a (add b c) _ _ _ _ (represents_self a) (add_value b c)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (add_guard _ _) (add_guard _ _) hl hr
    (positive_product (product_denominator_positive a b) (denominator_positive c))
    (positive_product (denominator_positive a) (product_denominator_positive b c))
  ipra_lc [addNumerator, productDenominator]

theorem multiply_associative (a b c : PTm n) : Γ ⊢[PRAAx]
    multiply (multiply a b) c ≐ multiply a (multiply b c) := by
  have hl := represents_multiply (Γ := Γ) (multiply a b) c _ _ _ _ (multiply_value a b) (represents_self c)
  have hr := represents_multiply (Γ := Γ) a (multiply b c) _ _ _ _ (represents_self a) (multiply_value b c)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (multiply_guard _ _) (multiply_guard _ _) hl hr
    (positive_product (product_denominator_positive a b) (denominator_positive c))
    (positive_product (denominator_positive a) (product_denominator_positive b c))
  ipra_lc [productDenominator]

theorem multiply_add (a b c : PTm n) : Γ ⊢[PRAAx]
    multiply a (add b c) ≐ add (multiply a b) (multiply a c) := by
  have hl := represents_multiply (Γ := Γ) a (add b c) _ _ _ _ (represents_self a) (add_value b c)
  have hr := represents_add (Γ := Γ) (multiply a b) (multiply a c) _ _ _ _
    (multiply_value a b) (multiply_value a c)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (multiply_guard _ _) (add_guard _ _) hl hr
    (positive_product (denominator_positive a) (product_denominator_positive b c))
    (positive_product (product_denominator_positive a b) (product_denominator_positive a c))
  ipra_lc [productDenominator, addNumerator]

theorem multiply_negative (a b : PTm n) : Γ ⊢[PRAAx]
    multiply a (negative b) ≐ negative (multiply a b) := by
  have hl := represents_multiply (Γ := Γ) a (negative b) _ _ _ _ (represents_self a) (negative_value b)
  have hr := represents_negative (Γ := Γ) (multiply a b) _ _ (multiply_value a b)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (multiply_guard _ _) (negative_guard _) hl hr
    (product_denominator_positive a b) (product_denominator_positive a b)
  ipra_lc [productDenominator]

theorem negative_involution (a : PTm n) : Γ ⊢[PRAAx] negative (negative a) ≐ recode a := by
  have hl := represents_negative (Γ := Γ) (negative a) _ _ (negative_value a)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (negative_guard _) (recode_guard _) hl
    (recode_value a) (denominator_positive a) (denominator_positive a)
  ipra_lc

def half : PTm n := RationalIntegerNormalization.normalize (ZT.natLit 1) two
def minusOne : PTm n := RationalIntegerNormalization.normalize (-(ZT.natLit 1)) one

ipra_subst half
ipra_subst minusOne

alias two_positive := Common.one_le_two
theorem half_value : Γ ⊢[PRAAx] represents (half : PTm n) (ZT.natLit 1) two :=
  RationalIntegerNormalization.normalize_preserves_value _ _ two_positive
theorem minus_one_value : Γ ⊢[PRAAx] represents (minusOne : PTm n) (-(ZT.natLit 1)) one :=
  RationalIntegerNormalization.normalize_preserves_value _ _ (le_refl one)

theorem negative_minus_multiply (a : PTm n) : Γ ⊢[PRAAx] negative a ≐ multiply minusOne a := by
  have hr := represents_multiply (Γ := Γ) minusOne a _ _ _ _ minus_one_value (represents_self a)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (negative_guard _) (multiply_guard _ _)
    (negative_value a) hr (denominator_positive a) (positive_product (le_refl one) (denominator_positive a))
  ipra_lc

theorem midpoint_value (a b : PTm n) : Γ ⊢[PRAAx]
    represents (midpoint a b) (addNumerator a b) (two*productDenominator a b) := by
  apply ZT.derive
  have e := ZT.toZ_eq (RationalIntegerNormalization.normalize_preserves_value (Γ := Γ)
    (midpointNumerator a b) (midpointDenominator a b) (midpoint_denominator_positive a b))
  simp only [ZT.toZ_mul,ZT.toZ_ofNat] at e
  change ZT.toZ Γ (addNumerator a b)*𝔞(denominatorOf (midpoint a b)) =
    ZT.toZ Γ (numeratorOf (midpoint a b))*𝔞(midpointDenominator a b) at e
  simp only [represents,ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [midpointDenominator,productDenominator,Q.mk_mul,map_mul] at e ⊢
  linear_combination e

theorem midpoint_half_add (a b : PTm n) : Γ ⊢[PRAAx] midpoint a b ≐ multiply half (add a b) := by
  have hr := represents_multiply (Γ := Γ) half (add a b) _ _ _ _ half_value (add_value a b)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalNormalForm.normalize_well_formed _ _ (midpoint_denominator_positive a b))
    (multiply_guard _ _) (midpoint_value a b) hr
    (positive_product two_positive (product_denominator_positive a b))
    (positive_product two_positive (product_denominator_positive a b))
  ipra_lc

theorem multiply_midpoint (c a b : PTm n) : Γ ⊢[PRAAx]
    multiply c (midpoint a b) ≐ midpoint (multiply c a) (multiply c b) :=
  (multiply_congr (.eqRefl c) (midpoint_half_add a b)).eqTrans
    ((multiply_associative c half (add a b)).eqSymm.eqTrans
      ((multiply_congr (multiply_commutative c half) (.eqRefl _)).eqTrans
        ((multiply_associative half c (add a b)).eqTrans
          ((multiply_congr (.eqRefl _) (multiply_add c a b)).eqTrans
            (midpoint_half_add (multiply c a) (multiply c b)).eqSymm))))

theorem midpoint_self (a : PTm n) : Γ ⊢[PRAAx] midpoint a a ≐ recode a := by
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalNormalForm.normalize_well_formed _ _ (midpoint_denominator_positive a a)) (recode_guard a)
    (midpoint_value a a) (recode_value a)
    (positive_product two_positive (product_denominator_positive a a)) (denominator_positive a)
  ipra_lc [addNumerator, productDenominator]

theorem negative_antitone (a b : PTm n) (h : Γ ⊢[PRAAx] rationalLE a b) :
    Γ ⊢[PRAAx] rationalLE (negative b) (negative a) := by
  apply order_of_representations _ _ _ _ _ _ (negative_value b) (negative_value a)
    (denominator_positive b) (denominator_positive a)
  let gap := PTm.monus (left b a) (left a b)
  apply zle_of_toZ gap
  have ord : Γ ⊢[PRAAx] left b a ≐ left a b+gap := eq_add_of_le h
  have ab := natEq ord
  simp only [ZT.toZ_mul,ZT.toZ_neg,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  unfold left at ab
  ipra_simps
  linear_combination -ab

theorem midpoint_monotone (a b c d : PTm n) (hac : Γ ⊢[PRAAx] rationalLE a c)
    (hbd : Γ ⊢[PRAAx] rationalLE b d) :
    Γ ⊢[PRAAx] rationalLE (midpoint a b) (midpoint c d) := by
  apply order_of_representations _ _ _ _ _ _ (midpoint_value a b) (midpoint_value c d)
    (positive_product two_positive (product_denominator_positive a b))
    (positive_product two_positive (product_denominator_positive c d))
  let g := PTm.monus (left c a) (left a c)
  let h := PTm.monus (left d b) (left b d)
  apply zle_of_toZ (two*(denominatorOf b*denominatorOf d*g+denominatorOf a*denominatorOf c*h))
  have ord1 : Γ ⊢[PRAAx] left c a ≐ left a c+g := eq_add_of_le hac
  have ord2 : Γ ⊢[PRAAx] left d b ≐ left b d+h := eq_add_of_le hbd
  have ac := natEq ord1
  have bd := natEq ord2
  simp only [addNumerator,productDenominator,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  unfold left at ac bd
  ipra_simps
  linear_combination -2*𝔞(denominatorOf b)*𝔞(denominatorOf d)*ac-
    2*𝔞(denominatorOf a)*𝔞(denominatorOf c)*bd

theorem canonical_algebra_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((add (add (var 0) (var 1)) (var 2) ≐ add (var 0) (add (var 1) (var 2))) ⋏
      ((multiply (multiply (var 0) (var 1)) (var 2) ≐ multiply (var 0) (multiply (var 1) (var 2))) ⋏
        (multiply (var 0) (add (var 1) (var 2)) ≐ add (multiply (var 0) (var 1)) (multiply (var 0) (var 2))))) :=
  closeUniv 3 (.andI (add_associative _ _ _) (.andI (multiply_associative _ _ _) (multiply_add _ _ _)))

theorem canonical_affine_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((multiply (var 0) (negative (var 1)) ≐ negative (multiply (var 0) (var 1))) ⋏
      ((multiply (var 0) (midpoint (var 1) (var 2)) ≐ midpoint (multiply (var 0) (var 1)) (multiply (var 0) (var 2))) ⋏
        ((negative (negative (var 0)) ≐ recode (var 0)) ⋏ (midpoint (var 0) (var 0) ≐ recode (var 0))))) :=
  closeUniv 3 (.andI (multiply_negative _ _) (.andI (multiply_midpoint _ _ _)
    (.andI (negative_involution _) (midpoint_self _))))

theorem affine_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((rationalLE (var 0) (var 2) ⟶ rationalLE (negative (var 2)) (negative (var 0))) ⋏
      (rationalLE (var 0) (var 2) ⟶ rationalLE (var 1) (var 3) ⟶
        rationalLE (midpoint (var 0) (var 1)) (midpoint (var 2) (var 3)))) :=
  closeUniv 4 (.andI (.impI (negative_antitone _ _ Prf.hyp0))
    (.impI (.impI (midpoint_monotone _ _ _ _ Prf.hyp1 Prf.hyp0))))

open RationalArithmetic (add)

theorem add_shuffle (a b c d : PTm n) : Γ ⊢[PRAAx] add (add a b) (add c d) ≐ add (add a c) (add b d) :=
  (add_associative a b (add c d)).eqTrans
    ((add_congr (.eqRefl a) (add_associative b c d).eqSymm).eqTrans
      ((add_congr (.eqRefl a) (add_congr (add_commutative b c) (.eqRefl d))).eqTrans
        ((add_congr (.eqRefl a) (add_associative c b d)).eqTrans (add_associative a c (add b d)).eqSymm)))

end LeanProofs.IPRA.Analysis.RationalAlgebra
