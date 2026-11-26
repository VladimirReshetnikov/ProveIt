import IPRADerivations.Algebra.QuadraticRationalCongruence

/-!
# Changing a positive rational radicand to an integer radicand

Decode the original positive rational radicand as `p/q`. The actual
coefficient map sends `(a,b)` to `(a,b/q)` in the stage with radicand
`p*q`. It preserves addition, negation, and the original rational
pair product at the level of both rational coefficient values.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Algebra.QuadraticRationalRadicand

open_ipra
open LeanProofs.IPRA.Analysis
open RationalSupMetric (numeratorOf denominatorOf)
open RationalArgmin (rationalEq)
open RationalAlgebra (positive_product)
open RationalIntegerNormalization (normalize normalize_preserves_value)
open QuadraticSignCertificates (encode first second first_value second_value positivePart negativePart)
open QuadraticRationalClearing (clear denominator represents sameCoefficients clear_represents denominator_positive)
open QuadraticPositiveScaling (scale scale_first scale_second)
open QuadraticConeOrder (add_first add_second)
open QuadraticRationalPairArithmetic (add negative scalar_code_congr scalar_value_congr scalar_add_same)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def isPositive (d : PTm n) : Fm PTm n := zle (ZT.ofNat one) (numeratorOf d)
def positiveNumerator (d : PTm n) : PTm n := positivePart (numeratorOf d)
def integerRadicand (d : PTm n) : PTm n := positiveNumerator d * denominatorOf d

def reciprocalNatural (q : PTm n) : PTm n := normalize (ZT.ofNat one) q
def divideBy (x q : PTm n) : PTm n := RationalArithmetic.multiply x (reciprocalNatural q)
def rescale (q x : PTm n) : PTm n := pairT (fstT x) (divideBy (sndT x) q)
def stretch (q A : PTm n) : PTm n := encode (ZT.ofNat q * first A) (second A)

def multiply (d x y : PTm n) : PTm n := pairT
  (RationalArithmetic.add (RationalArithmetic.multiply (fstT x) (fstT y))
    (RationalArithmetic.multiply d (RationalArithmetic.multiply (sndT x) (sndT y))))
  (RationalArithmetic.add (RationalArithmetic.multiply (fstT x) (sndT y)) (RationalArithmetic.multiply (sndT x) (fstT y)))

ipra_subst positiveNumerator

ipra_subst integerRadicand

ipra_subst rescale [divideBy, reciprocalNatural, one]

ipra_subst multiply

theorem numerator_value (d : PTm n) (h : Γ ⊢[PRAAx] isPositive d) :
    ZT.toZ Γ (numeratorOf d) = 𝔞(positiveNumerator d) := by
  have hs : Nonneg Γ (ZT.toZ Γ (numeratorOf d)-1) := by
    simpa only [zsl_def,ZT.toZ_ofNat,Q.mk_one,map_one] using nn_zsl h
  have hN : Nonneg Γ (ZT.toZ Γ (numeratorOf d)) := by
    (convert nn_add nn_one hs using 1; ring)
  have h0 := QuadraticSignCertificates.nonnegative_of_value (numeratorOf d) hN
  rw [QuadraticSignCertificates.parts_value, natEq (QuadraticSignCertificates.negative_part_zero _ h0)]
  simp [positiveNumerator]

theorem numerator_positive (d : PTm n) (h : Γ ⊢[PRAAx] isPositive d) : Γ ⊢[PRAAx] le one (positiveNumerator d) := by
  apply le_of_nonneg
  rw [← numerator_value d h,Q.mk_one,map_one]
  simpa only [zsl_def,ZT.toZ_ofNat,Q.mk_one,map_one] using nn_zsl h

theorem integer_radicand_positive (d : PTm n) (h : Γ ⊢[PRAAx] isPositive d) : Γ ⊢[PRAAx] le one (integerRadicand d) :=
  positive_product (numerator_positive d h) (RationalArgmin.denominator_positive d)

theorem radicand_represents (d : PTm n) (h : Γ ⊢[PRAAx] isPositive d) : Γ ⊢[PRAAx]
    RationalArithmetic.represents d (ZT.ofNat (positiveNumerator d)) (denominatorOf d) := by
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,numerator_value d h]

theorem stretch_first (q A : PTm n) : ZT.toZ Γ (first (stretch q A)) = 𝔞(q) * ZT.toZ Γ (first A) := by
  simp [stretch,first_value,ZT.toZ_mul,ZT.toZ_ofNat]

theorem stretch_second (q A : PTm n) : ZT.toZ Γ (second (stretch q A)) = ZT.toZ Γ (second A) := by
  simp [stretch,second_value]

theorem divide_represents (x q D : PTm n) (a : ZT n) (hq : Γ ⊢[PRAAx] le one q)
    (h : Γ ⊢[PRAAx] RationalArithmetic.represents x a D) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (divideBy x q) a (D*q) :=
  scalar_value_congr _ _ _ _ (by simp [ZT.toZ_mul,ZT.toZ_ofNat,map_one])
    (RationalRepresentations.represents_multiply x (reciprocalNatural q) a (ZT.ofNat one) D q h
      (normalize_preserves_value _ _ hq))

theorem rescale_represents (q x A D : PTm n) (hq : Γ ⊢[PRAAx] le one q)
    (h : Γ ⊢[PRAAx] represents x A D) : Γ ⊢[PRAAx] represents (rescale q x) (stretch q A) (D*q) := by
  refine .andI (scalar_code_congr _ _ (fst_pair _ _) ?_) (scalar_code_congr _ _ (snd_pair _ _) ?_)
  · ipra_lc [stretch_first] 𝔞(q)*ZT.toZ_eq (.andE₁ h)
  · exact scalar_value_congr _ _ _ _ (stretch_second q A).symm (divide_represents _ _ _ _ hq (.andE₂ h))

theorem equal_from_representations (x y A B : PTm n) (a b : ZT n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hx : Γ ⊢[PRAAx] RationalArithmetic.represents x a A) (hy : Γ ⊢[PRAAx] RationalArithmetic.represents y b B)
    (hCross : Γ ⊢[PRAAx] ZT.eq (a*ZT.ofNat B) (b*ZT.ofNat A)) : Γ ⊢[PRAAx] rationalEq x y := by
  apply RationalArithmetic.value_equality
  apply RationalNormalForm.positive_integer_cancel (A*B) _ _ (positive_product hA hB)
  ipra_lc -(𝔞(B)*𝔞(denominatorOf y))*ZT.toZ_eq hx+
    𝔞(A)*𝔞(denominatorOf x)*ZT.toZ_eq hy+ 𝔞(denominatorOf x)*𝔞(denominatorOf y)*ZT.toZ_eq hCross

theorem equal_pairs_from_representations (x y A B D E : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hE : Γ ⊢[PRAAx] le one E)
    (hx : Γ ⊢[PRAAx] represents x A D) (hy : Γ ⊢[PRAAx] represents y B E)
    (hFirst : ZT.toZ Γ (first A)*𝔞(E) = ZT.toZ Γ (first B)*𝔞(D))
    (hSecond : ZT.toZ Γ (second A)*𝔞(E) = ZT.toZ Γ (second B)*𝔞(D)) : Γ ⊢[PRAAx] sameCoefficients x y := by
  refine .andI (equal_from_representations _ _ _ _ _ _ hD hE (.andE₁ hx) (.andE₁ hy) (ZT.derive ?_))
    (equal_from_representations _ _ _ _ _ _ hD hE (.andE₂ hx) (.andE₂ hy) (ZT.derive ?_))
  · simpa only [ZT.toZ_mul,ZT.toZ_ofNat] using hFirst
  · simpa only [ZT.toZ_mul,ZT.toZ_ofNat] using hSecond

theorem rescale_add (q x y : PTm n) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx]
    sameCoefficients (rescale q (add x y)) (add (rescale q x) (rescale q y)) := by
  let D := denominator x
  let E := denominator y
  have hD := denominator_positive (Γ := Γ) x
  have hE := denominator_positive (Γ := Γ) y
  have hx := rescale_represents q x (clear x) D hq (clear_represents x)
  have hy := rescale_represents q y (clear y) E hq (clear_represents y)
  have ho := rescale_represents q (add x y) _ (D*E) hq
    (QuadraticRationalPairArithmetic.add_represents _ _ _ _ _ _ (clear_represents x) (clear_represents y))
  apply equal_pairs_from_representations _ _ _ _ _ _ (positive_product (positive_product hD hE) hq)
    (positive_product (positive_product hD hq) (positive_product hE hq)) ho
      (QuadraticRationalPairArithmetic.add_represents _ _ _ _ _ _ hx hy)
  all_goals (simp only [stretch_first,stretch_second,add_first,add_second,scale_first,scale_second,Q.mk_mul,map_mul]; ring)

theorem rescale_negative (q x : PTm n) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx]
    sameCoefficients (rescale q (negative x)) (negative (rescale q x)) := by
  let D := denominator x
  have hD := positive_product (denominator_positive (Γ := Γ) x) hq
  have hx := rescale_represents q x (clear x) D hq (clear_represents x)
  have ho := rescale_represents q (negative x) _ D hq
    (QuadraticRationalPairArithmetic.negative_represents _ _ _ (clear_represents x))
  apply equal_pairs_from_representations _ _ _ _ _ _ hD hD ho
    (QuadraticRationalPairArithmetic.negative_represents _ _ _ hx)
  all_goals simp only [stretch_first,stretch_second,QuadraticSignCertificates.negative_first,
    QuadraticSignCertificates.negative_second] <;> ring

theorem scale_representation (x D q : PTm n) (a : ZT n) (h : Γ ⊢[PRAAx] RationalArithmetic.represents x a D) :
    Γ ⊢[PRAAx] RationalArithmetic.represents x (ZT.ofNat q*a) (q*D) := by
  ipra_lc 𝔞(q)*ZT.toZ_eq h

def productNumerator (p q A B : PTm n) : PTm n := encode
  (ZT.ofNat q*(first A*first B)+ZT.ofNat p*(second A*second B))
  (ZT.ofNat q*(first A*second B+second A*first B))

theorem product_numerator_first (p q A B : PTm n) : ZT.toZ Γ (first (productNumerator p q A B)) =
    𝔞(q)*(ZT.toZ Γ (first A)*ZT.toZ Γ (first B))+𝔞(p)*(ZT.toZ Γ (second A)*ZT.toZ Γ (second B)) := by
  simp only [productNumerator,first_value,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]

theorem product_numerator_second (p q A B : PTm n) : ZT.toZ Γ (second (productNumerator p q A B)) =
    𝔞(q)*(ZT.toZ Γ (first A)*ZT.toZ Γ (second B)+ZT.toZ Γ (second A)*ZT.toZ Γ (first B)) := by
  simp only [productNumerator,second_value,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]

theorem multiply_represents (d x y A B D E : PTm n) (hd : Γ ⊢[PRAAx] isPositive d)
    (hD : Γ ⊢[PRAAx] le one D) (hE : Γ ⊢[PRAAx] le one E)
    (hx : Γ ⊢[PRAAx] represents x A D) (hy : Γ ⊢[PRAAx] represents y B E) : Γ ⊢[PRAAx]
    represents (multiply d x y) (productNumerator (positiveNumerator d) (denominatorOf d) A B) (denominatorOf d*(D*E)) := by
  let q := denominatorOf d
  let p := positiveNumerator d
  let ac := RationalRepresentations.represents_multiply (fstT x) (fstT y) (first A) (first B) D E (.andE₁ hx) (.andE₁ hy)
  let be := RationalRepresentations.represents_multiply (sndT x) (sndT y) (second A) (second B) D E (.andE₂ hx) (.andE₂ hy)
  let ae := RationalRepresentations.represents_multiply (fstT x) (sndT y) (first A) (second B) D E (.andE₁ hx) (.andE₂ hy)
  let bc := RationalRepresentations.represents_multiply (sndT x) (fstT y) (second A) (first B) D E (.andE₂ hx) (.andE₁ hy)
  have hDE := positive_product hD hE
  have firstRep := scalar_add_same _ _ (q*(D*E)) _ _ (positive_product (RationalArgmin.denominator_positive d) hDE)
    (scale_representation _ _ q _ ac)
    (RationalRepresentations.represents_multiply d _ (ZT.ofNat p) _ q (D*E) (radicand_represents d hd) be)
  have secondRep := scale_representation _ _ q _ (scalar_add_same _ _ (D*E) _ _ hDE ae bc)
  refine .andI (scalar_code_congr _ _ (fst_pair _ _) ?_) (scalar_code_congr _ _ (snd_pair _ _) ?_)
  · exact scalar_value_congr _ _ _ _ (by simp only [productNumerator,first_value,q,p]) firstRep
  · exact scalar_value_congr _ _ _ _ (by simp only [productNumerator,second_value,q]) secondRep

theorem rescale_multiply (d x y : PTm n) (hd : Γ ⊢[PRAAx] isPositive d) : Γ ⊢[PRAAx]
    sameCoefficients (rescale (denominatorOf d) (multiply d x y))
      (QuadraticRationalPairArithmetic.multiply (integerRadicand d) (rescale (denominatorOf d) x) (rescale (denominatorOf d) y)) := by
  let D := denominator x
  let E := denominator y
  let q := denominatorOf d
  have hD := denominator_positive (Γ := Γ) x
  have hE := denominator_positive (Γ := Γ) y
  have hq := RationalArgmin.denominator_positive (Γ := Γ) d
  have hx := rescale_represents q x (clear x) D hq (clear_represents x)
  have hy := rescale_represents q y (clear y) E hq (clear_represents y)
  have ho := rescale_represents q (multiply d x y) _ (q*(D*E)) hq
    (multiply_represents _ _ _ _ _ _ _ hd hD hE (clear_represents x) (clear_represents y))
  have hDQ := positive_product hD hq
  have hEQ := positive_product hE hq
  apply equal_pairs_from_representations _ _ _ _ _ _ (positive_product (positive_product hq (positive_product hD hE)) hq)
    (positive_product hDQ hEQ) ho (QuadraticRationalPairArithmetic.multiply_represents _ _ _ _ _ _ _ hDQ hEQ hx hy)
  all_goals (simp only [stretch_first,stretch_second,product_numerator_first,product_numerator_second,integerRadicand,
    QuadraticSignCertificates.multiply_first,QuadraticSignCertificates.multiply_second,Q.mk_mul,map_mul]; ring)

theorem rescale_difference (q x y : PTm n) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx]
    sameCoefficients (rescale q (QuadraticRationalEqualityOrder.difference x y))
      (QuadraticRationalEqualityOrder.difference (rescale q x) (rescale q y)) := by
  let D := denominator x
  let E := denominator y
  have hD := denominator_positive (Γ := Γ) x
  have hE := denominator_positive (Γ := Γ) y
  have hx := rescale_represents q x (clear x) D hq (clear_represents x)
  have hy := rescale_represents q y (clear y) E hq (clear_represents y)
  have ho := rescale_represents q (QuadraticRationalEqualityOrder.difference x y) _ (D*E) hq
    (QuadraticRationalEqualityOrder.cross_represents _ _ _ _ _ _ (clear_represents x) (clear_represents y))
  apply equal_pairs_from_representations _ _ _ _ _ _ (positive_product (positive_product hD hE) hq)
    (positive_product (positive_product hD hq) (positive_product hE hq)) ho
      (QuadraticRationalEqualityOrder.cross_represents _ _ _ _ _ _ hx hy)
  all_goals (simp only [QuadraticRationalEqualityOrder.cross,QuadraticIntegerOrder.difference,
    QuadraticSignCertificates.negative_first,QuadraticSignCertificates.negative_second,
    stretch_first,stretch_second,add_first,add_second,scale_first,scale_second,Q.mk_mul,map_mul]; ring)

def changeBasis (d x : PTm n) : PTm n := rescale (denominatorOf d) x

def sign (d x : PTm n) : PTm n := QuadraticRationalClearing.sign (integerRadicand d) (changeBasis d x)

def equivalent (d x y : PTm n) : Fm PTm n := sign d (QuadraticRationalEqualityOrder.difference x y) ≐ zero

def less (d x y : PTm n) : Fm PTm n := sign d (QuadraticRationalEqualityOrder.difference y x) ≐ one

theorem difference_sign (d x y : PTm n) (hd : Γ ⊢[PRAAx] isPositive d) : Γ ⊢[PRAAx]
    sign d (QuadraticRationalEqualityOrder.difference x y) ≐ QuadraticRationalClearing.sign (integerRadicand d)
      (QuadraticRationalEqualityOrder.difference (changeBasis d x) (changeBasis d y)) :=
  QuadraticRationalClearing.sign_congr (integerRadicand d) _ _ (integer_radicand_positive d hd)
    (rescale_difference (denominatorOf d) x y (RationalArgmin.denominator_positive d))

theorem equivalent_iff (d x y : PTm n) (hd : Γ ⊢[PRAAx] isPositive d) : Γ ⊢[PRAAx]
    Fm.iff (equivalent d x y) (QuadraticRationalEqualityOrder.equivalent (integerRadicand d) (changeBasis d x) (changeBasis d y)) := by
  have h := difference_sign d x y hd
  exact .andI (.impI (h.wk.eqSymm.eqTrans Prf.hyp0)) (.impI (h.wk.eqTrans Prf.hyp0))

theorem less_iff (d x y : PTm n) (hd : Γ ⊢[PRAAx] isPositive d) : Γ ⊢[PRAAx]
    Fm.iff (less d x y) (QuadraticRationalEqualityOrder.less (integerRadicand d) (changeBasis d x) (changeBasis d y)) := by
  have h := difference_sign d y x hd
  exact .andI (.impI (h.wk.eqSymm.eqTrans Prf.hyp0)) (.impI (h.wk.eqTrans Prf.hyp0))

def output (d x : PTm n) : PTm n := pairT (integerRadicand d) (pairT (changeBasis d x) (sign d x))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (d x : PTm n) : PTm n := ap2 outputF d x

theorem program_at (d x : PTm n) : Γ ⊢[PRAAx] run d x ≐ output d x := by
  simpa [run,outputF,ap2,output,changeBasis,sign] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![d,x]

theorem actual_rational_radicand_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (isPositive (var 0) ⟶ sameCoefficients (changeBasis (var 0) (multiply (var 0) (var 1) (var 2)))
      (QuadraticRationalPairArithmetic.multiply (integerRadicand (var 0)) (changeBasis (var 0) (var 1)) (changeBasis (var 0) (var 2)))) :=
  closeUniv 3 (.impI (rescale_multiply _ _ _ Prf.hyp0))

theorem actual_rational_radicand_comparisons_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (isPositive (var 0) ⟶ (Fm.iff (equivalent (var 0) (var 1) (var 2))
      (QuadraticRationalEqualityOrder.equivalent (integerRadicand (var 0)) (changeBasis (var 0) (var 1)) (changeBasis (var 0) (var 2)))) ⋏
      (Fm.iff (less (var 0) (var 1) (var 2))
        (QuadraticRationalEqualityOrder.less (integerRadicand (var 0)) (changeBasis (var 0) (var 1)) (changeBasis (var 0) (var 2))))) :=
  closeUniv 3 (.impI (.andI (equivalent_iff _ _ _ Prf.hyp0) (less_iff _ _ _ Prf.hyp0)))

theorem actual_rational_radicand_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)

end LeanProofs.IPRA.Algebra.QuadraticRationalRadicand
