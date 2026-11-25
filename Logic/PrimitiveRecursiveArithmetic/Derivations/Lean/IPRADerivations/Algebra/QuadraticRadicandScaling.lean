import IPRADerivations.Algebra.QuadraticRationalRadicand
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.CertificateTactics

/-!
# Square scaling of the actual positive quadratic sign

The coefficient map `(a,b) ↦ (k*a,b)` changes the numerical radicand
`D` to `D*k*k`. Actual multiplier certificates transport through this
map and positive scalar multiplication. The resulting computed signs
agree for positive numerical `D,k`. Equivalent original raw positive
rational radicands then give the same actual sign, by a derived common
square-scaled integer radicand. Positivity and zero numerator are also
preserved by rational value equality. All pair equalities compare signed
coefficient values; the zero stage remains the separate projection.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Algebra.QuadraticRadicandScaling

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open QuadraticSignCertificates (first second equal cone multiply negative sign multiplier zeroCode
  multiply_first multiply_second negative_first negative_second zero_first_value zero_second_value)
open QuadraticConeOrder (equal_of_values equal_first equal_second equal_symm equal_trans
  cone_of_nonnegative cone_congr sign_unique_positive sign_unique_negative sign_unique_zero)
open QuadraticPositiveScaling (scale scale_first scale_second)
open QuadraticRationalRadicand (stretch stretch_first stretch_second)
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalEq)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def squareRadicand (D k : PTm n) : PTm n := D*k*k

@[simp] theorem subst_squareRadicand {l : ℕ} (σ : Fin n → PTm l) (D k : PTm n) :
    Syn.subst σ (squareRadicand D k) = squareRadicand (Syn.subst σ D) (Syn.subst σ k) := by
  simp [squareRadicand]
@[simp] theorem subst_stretch {l : ℕ} (σ : Fin n → PTm l) (k x : PTm n) :
    Syn.subst σ (stretch k x) = stretch (Syn.subst σ k) (Syn.subst σ x) := by
  simp [stretch]

theorem square_radicand_positive (D k : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx] le one (squareRadicand D k) :=
  LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product
    (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product hD hk) hk

theorem cone_stretch (k x : PTm n) (hk : Γ ⊢[PRAAx] le one k)
    (hx : Γ ⊢[PRAAx] cone x) : Γ ⊢[PRAAx] cone (stretch k x) := by
  have ha := QuadraticConeOrder.first_nonnegative x hx
  have hb := QuadraticConeOrder.second_nonnegative x hx
  have hs : Nonneg Γ (ZT.toZ Γ (first x)+ZT.toZ Γ (second x)-1) := by
    simpa only [zsl_def,ZT.toZ_add,ZT.toZ_ofNat,Q.mk_one,map_one] using nn_zsl (.andE₂ (.andE₂ hx))
  have ht : Nonneg Γ (𝔞(k)-1) := by simpa only [sl_def,Q.mk_one,map_one] using nn_sl hk
  apply cone_of_nonnegative
  · rw [stretch_first]; exact nn_mul (nn_term k) ha
  · rw [stretch_second]; exact hb
  · rw [stretch_first,stretch_second]
    convert nn_add (nn_mul ht ha) hs using 1 <;> ring

theorem cone_scale (k x : PTm n) (hk : Γ ⊢[PRAAx] le one k)
    (hx : Γ ⊢[PRAAx] cone x) : Γ ⊢[PRAAx] cone (scale k x) := by
  have ha := QuadraticConeOrder.first_nonnegative x hx
  have hb := QuadraticConeOrder.second_nonnegative x hx
  have hs : Nonneg Γ (ZT.toZ Γ (first x)+ZT.toZ Γ (second x)-1) := by
    simpa only [zsl_def,ZT.toZ_add,ZT.toZ_ofNat,Q.mk_one,map_one] using nn_zsl (.andE₂ (.andE₂ hx))
  have ht : Nonneg Γ (𝔞(k)-1) := by simpa only [sl_def,Q.mk_one,map_one] using nn_sl hk
  apply cone_of_nonnegative
  · rw [scale_first]; exact nn_mul (nn_term k) ha
  · rw [scale_second]; exact nn_mul (nn_term k) hb
  · rw [scale_first,scale_second]
    convert nn_add (nn_mul ht (nn_add ha hb)) hs using 1 <;> ring

theorem stretch_product (D k u x : PTm n) : Γ ⊢[PRAAx]
    equal (multiply (squareRadicand D k) (stretch k u) (stretch k x))
      (scale k (stretch k (multiply D u x))) := by
  apply equal_of_values <;>
    simp only [multiply_first,multiply_second,stretch_first,stretch_second,scale_first,scale_second,
      squareRadicand,Q.mk_mul,map_mul] <;> ring

theorem stretch_negative_product (D k u x : PTm n) : Γ ⊢[PRAAx]
    equal (negative (multiply (squareRadicand D k) (stretch k u) (stretch k x)))
      (scale k (stretch k (negative (multiply D u x)))) := by
  apply equal_of_values <;>
    simp only [negative_first,negative_second,multiply_first,multiply_second,stretch_first,stretch_second,
      scale_first,scale_second,squareRadicand,Q.mk_mul,map_mul] <;> ring

theorem stretch_zero_product (D k u x : PTm n)
    (hz : Γ ⊢[PRAAx] equal (multiply D u x) zeroCode) : Γ ⊢[PRAAx]
    equal (multiply (squareRadicand D k) (stretch k u) (stretch k x)) zeroCode := by
  apply equal_trans (stretch_product D k u x)
  apply equal_of_values
  · rw [scale_first,stretch_first,equal_first hz,zero_first_value]; ring
  · rw [scale_second,stretch_second,equal_second hz,zero_second_value]; ring

theorem positive_certificate (D k u x : PTm n) (hk : Γ ⊢[PRAAx] le one k)
    (hp : Γ ⊢[PRAAx] cone (multiply D u x)) : Γ ⊢[PRAAx]
    cone (multiply (squareRadicand D k) (stretch k u) (stretch k x)) :=
  cone_congr (equal_symm (stretch_product D k u x)) (cone_scale _ _ hk (cone_stretch _ _ hk hp))

theorem negative_certificate (D k u x : PTm n) (hk : Γ ⊢[PRAAx] le one k)
    (hp : Γ ⊢[PRAAx] cone (negative (multiply D u x))) : Γ ⊢[PRAAx]
    cone (negative (multiply (squareRadicand D k) (stretch k u) (stretch k x))) :=
  cone_congr (equal_symm (stretch_negative_product D k u x)) (cone_scale _ _ hk (cone_stretch _ _ hk hp))

theorem square_radicand_sign (D k x : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    sign (squareRadicand D k) (stretch k x) ≐ sign D x := by
  have actual := QuadraticSignCertificates.actual_certificate (Γ := Γ) D x
  have hu := cone_stretch k (multiplier x) hk (.andE₁ actual)
  have hd := square_radicand_positive D k hD hk
  refine .orE (.andE₂ actual) ?_ ?_
  · exact (sign_unique_positive _ _ _ hd.wk hu.wk
      (positive_certificate _ _ _ _ hk.wk (.andE₂ Prf.hyp0))).eqTrans (Prf.andE₁ Prf.hyp0).eqSymm
  · refine .orE Prf.hyp0 ?_ ?_
    · exact (sign_unique_negative _ _ _ hd.wk.wk hu.wk.wk
        (negative_certificate _ _ _ _ hk.wk.wk (.andE₂ Prf.hyp0))).eqTrans (Prf.andE₁ Prf.hyp0).eqSymm
    · exact (sign_unique_zero _ _ _ hd.wk.wk hu.wk.wk
        (stretch_zero_product _ _ _ _ (.andE₂ Prf.hyp0))).eqTrans (Prf.andE₁ Prf.hyp0).eqSymm

theorem sign_radicand_congr (D E x : PTm n) (h : Γ ⊢[PRAAx] D ≐ E) : Γ ⊢[PRAAx]
    sign D x ≐ sign E x := by
  ipra_congr (sign (var 0) (var 1) : PTm 2) with [h, .eqRefl x]

theorem common_square_sign (D E k l x y : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hE : Γ ⊢[PRAAx] le one E) (hk : Γ ⊢[PRAAx] le one k) (hl : Γ ⊢[PRAAx] le one l)
    (hRad : Γ ⊢[PRAAx] squareRadicand D k ≐ squareRadicand E l)
    (hPair : Γ ⊢[PRAAx] equal (stretch k x) (stretch l y)) : Γ ⊢[PRAAx] sign D x ≐ sign E y :=
  (square_radicand_sign D k x hD hk).eqSymm.eqTrans
    ((sign_radicand_congr _ _ _ hRad).eqTrans
      ((QuadraticConeOrder.sign_congr _ _ _ (square_radicand_positive E l hE hl) hPair).eqTrans
        (square_radicand_sign E l y hE hl)))

theorem stretch_commute (k l x : PTm n) : Γ ⊢[PRAAx] equal (stretch k (stretch l x)) (stretch l (stretch k x)) := by
  apply equal_of_values <;> simp only [stretch_first,stretch_second] <;> ring

theorem numerator_cross (d e : PTm n) (h : Γ ⊢[PRAAx] rationalEq d e) : Γ ⊢[PRAAx]
    ZT.eq (numeratorOf d*ZT.ofNat (denominatorOf e)) (numeratorOf e*ZT.ofNat (denominatorOf d)) := by
  apply ZT.derive
  have eq := natEq h
  simp only [LeanProofs.IPRA.Analysis.RationalArgmin.left,Q.mk_add,Q.mk_mul,map_add,map_mul] at eq
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  linear_combination eq

theorem rational_positive_congr (d e : PTm n)
    (hd : Γ ⊢[PRAAx] QuadraticRationalRadicand.isPositive d)
    (h : Γ ⊢[PRAAx] rationalEq d e) : Γ ⊢[PRAAx] QuadraticRationalRadicand.isPositive e := by
  have cross := ZT.toZ_eq (numerator_cross d e h)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat] at cross
  have pairs : Γ ⊢[PRAAx] equal
      (scale (denominatorOf e) (QuadraticIntegerEmbedding.integer (numeratorOf d)))
      (scale (denominatorOf d) (QuadraticIntegerEmbedding.integer (numeratorOf e))) := by
    apply equal_of_values
    · simp only [scale_first,QuadraticIntegerEmbedding.integer_first]
      linear_combination cross
    · simp only [scale_second,QuadraticIntegerEmbedding.integer_second]; ring
  have signs := QuadraticPositiveScaling.cross_scale_sign one _ _ _ _ (le_refl one)
    (LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive e)
    (LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive d) pairs
  exact QuadraticIntegerEmbedding.integer_positive_reflect one (numeratorOf e) (le_refl one)
    (signs.eqSymm.eqTrans (QuadraticIntegerEmbedding.integer_positive one (numeratorOf d) (le_refl one) hd))

theorem rational_zero_congr (d e : PTm n) (hd : Γ ⊢[PRAAx] ZT.eq (numeratorOf d) (ZT.ofNat zero))
    (h : Γ ⊢[PRAAx] rationalEq d e) : Γ ⊢[PRAAx] ZT.eq (numeratorOf e) (ZT.ofNat zero) := by
  apply LeanProofs.IPRA.Analysis.RationalNormalForm.positive_integer_cancel (denominatorOf d) _ _
    (LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive d)
  apply ZT.derive
  have cross := ZT.toZ_eq (numerator_cross d e h)
  have z := ZT.toZ_eq hd
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_zero,map_zero] at cross z ⊢
  rw [z] at cross
  linear_combination -cross

theorem common_integer_radicand (d e : PTm n)
    (hd : Γ ⊢[PRAAx] QuadraticRationalRadicand.isPositive d)
    (he : Γ ⊢[PRAAx] QuadraticRationalRadicand.isPositive e)
    (h : Γ ⊢[PRAAx] LeanProofs.IPRA.Analysis.RationalArgmin.rationalEq d e) : Γ ⊢[PRAAx]
    squareRadicand (QuadraticRationalRadicand.integerRadicand d)
        (LeanProofs.IPRA.Analysis.RationalSupMetric.denominatorOf e) ≐
      squareRadicand (QuadraticRationalRadicand.integerRadicand e)
        (LeanProofs.IPRA.Analysis.RationalSupMetric.denominatorOf d) := by
  have cross := ZT.toZ_eq (numerator_cross d e h)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat] at cross
  rw [QuadraticRationalRadicand.numerator_value d hd,QuadraticRationalRadicand.numerator_value e he] at cross
  ipra_lc [squareRadicand, QuadraticRationalRadicand.integerRadicand] 𝔞(LeanProofs.IPRA.Analysis.RationalSupMetric.denominatorOf d)* 𝔞(LeanProofs.IPRA.Analysis.RationalSupMetric.denominatorOf e)*cross

theorem native_rational_radicand_sign (d e A : PTm n)
    (hd : Γ ⊢[PRAAx] QuadraticRationalRadicand.isPositive d)
    (he : Γ ⊢[PRAAx] QuadraticRationalRadicand.isPositive e)
    (h : Γ ⊢[PRAAx] LeanProofs.IPRA.Analysis.RationalArgmin.rationalEq d e) : Γ ⊢[PRAAx]
    sign (QuadraticRationalRadicand.integerRadicand d)
        (stretch (LeanProofs.IPRA.Analysis.RationalSupMetric.denominatorOf d) A) ≐
      sign (QuadraticRationalRadicand.integerRadicand e)
        (stretch (LeanProofs.IPRA.Analysis.RationalSupMetric.denominatorOf e) A) :=
  common_square_sign _ _ _ _ _ _ (QuadraticRationalRadicand.integer_radicand_positive d hd)
    (QuadraticRationalRadicand.integer_radicand_positive e he)
    (LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive e)
    (LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive d)
    (common_integer_radicand d e hd he h) (stretch_commute _ _ _)

theorem rational_representation_sign (d x A D : PTm n)
    (hd : Γ ⊢[PRAAx] QuadraticRationalRadicand.isPositive d)
    (hD : Γ ⊢[PRAAx] le one D)
    (hx : Γ ⊢[PRAAx] QuadraticRationalClearing.represents x A D) : Γ ⊢[PRAAx]
    QuadraticRationalRadicand.sign d x ≐
      sign (QuadraticRationalRadicand.integerRadicand d)
        (stretch (LeanProofs.IPRA.Analysis.RationalSupMetric.denominatorOf d) A) :=
  QuadraticRationalClearing.representation_sign _ _ _ _
    (QuadraticRationalRadicand.integer_radicand_positive d hd)
    (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product hD
      (LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive d))
    (QuadraticRationalRadicand.rescale_represents _ _ _ _
      (LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive d) hx)

theorem rational_radicand_sign (d e x : PTm n)
    (hd : Γ ⊢[PRAAx] QuadraticRationalRadicand.isPositive d)
    (he : Γ ⊢[PRAAx] QuadraticRationalRadicand.isPositive e)
    (h : Γ ⊢[PRAAx] LeanProofs.IPRA.Analysis.RationalArgmin.rationalEq d e) : Γ ⊢[PRAAx]
    QuadraticRationalRadicand.sign d x ≐ QuadraticRationalRadicand.sign e x :=
  (rational_representation_sign d x _ _ hd (QuadraticRationalClearing.denominator_positive x)
    (QuadraticRationalClearing.clear_represents x)).eqTrans
    ((native_rational_radicand_sign d e (QuadraticRationalClearing.clear x) hd he h).eqTrans
      (rational_representation_sign e x _ _ he (QuadraticRationalClearing.denominator_positive x)
        (QuadraticRationalClearing.clear_represents x)).eqSymm)

theorem rational_radicand_sign_of_equal (d e x : PTm n)
    (hd : Γ ⊢[PRAAx] QuadraticRationalRadicand.isPositive d)
    (h : Γ ⊢[PRAAx] rationalEq d e) : Γ ⊢[PRAAx]
    QuadraticRationalRadicand.sign d x ≐ QuadraticRationalRadicand.sign e x :=
  rational_radicand_sign d e x hd (rational_positive_congr d e hd h) h

def output (D k x : PTm n) : PTm n := pairT (squareRadicand D k)
  (pairT (stretch k x) (pairT (sign D x) (sign (squareRadicand D k) (stretch k x))))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (D k x : PTm n) : PTm n := ap3 outputF D k x
def rationalOutput (d e x : PTm n) : PTm n :=
  pairT (QuadraticRationalRadicand.sign d x) (QuadraticRationalRadicand.sign e x)
def rationalOutputF : PR 3 := PTm.toPR (rationalOutput (var 0) (var 1) (var 2))
def rationalRun (d e x : PTm n) : PTm n := ap3 rationalOutputF d e x

@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (D k x : PTm n) :
    Syn.subst σ (output D k x) = output (Syn.subst σ D) (Syn.subst σ k) (Syn.subst σ x) := by
  simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (D k x : PTm n) :
    Syn.subst σ (run D k x) = run (Syn.subst σ D) (Syn.subst σ k) (Syn.subst σ x) := by simp [run]
@[simp] theorem subst_rationalOutput {l : ℕ} (σ : Fin n → PTm l) (d e x : PTm n) :
    Syn.subst σ (rationalOutput d e x) = rationalOutput (Syn.subst σ d) (Syn.subst σ e) (Syn.subst σ x) := by
  simp [rationalOutput,QuadraticRationalRadicand.sign,QuadraticRationalRadicand.changeBasis]
@[simp] theorem subst_rationalRun {l : ℕ} (σ : Fin n → PTm l) (d e x : PTm n) :
    Syn.subst σ (rationalRun d e x) = rationalRun (Syn.subst σ d) (Syn.subst σ e) (Syn.subst σ x) := by
  simp [rationalRun]

theorem program_at (D k x : PTm n) : Γ ⊢[PRAAx] run D k x ≐ output D k x := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![D,k,x]
theorem returned_radicand (D k x : PTm n) : Γ ⊢[PRAAx] fstT (run D k x) ≐ squareRadicand D k :=
  (congrFst (program_at _ _ _)).eqTrans (fst_pair _ _)
theorem returned_stretch (D k x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run D k x)) ≐ stretch k x :=
  (congrFst ((congrSnd (program_at _ _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_signs (D k x : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run D k x)) ≐ pairT (sign D x) (sign (squareRadicand D k) (stretch k x)) :=
  (congrSnd ((congrSnd (program_at _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_equal_signs (D k x : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run D k x))) ≐ sndT (sndT (sndT (run D k x))) :=
  ((congrFst (returned_signs _ _ _)).eqTrans (fst_pair _ _)).eqTrans
    ((square_radicand_sign _ _ _ hD hk).eqSymm.eqTrans
      ((congrSnd (returned_signs _ _ _)).eqTrans (snd_pair _ _)).eqSymm)
theorem rational_program_at (d e x : PTm n) : Γ ⊢[PRAAx] rationalRun d e x ≐ rationalOutput d e x := by
  simpa [rationalRun,rationalOutputF,ap3] using toPR_eq (Γ := Γ)
    (rationalOutput (var 0) (var 1) (var 2) : PTm 3) ![d,e,x]
theorem returned_rational_signs (d e x : PTm n)
    (hd : Γ ⊢[PRAAx] QuadraticRationalRadicand.isPositive d)
    (h : Γ ⊢[PRAAx] rationalEq d e) : Γ ⊢[PRAAx]
    fstT (rationalRun d e x) ≐ sndT (rationalRun d e x) :=
  ((congrFst (rational_program_at _ _ _)).eqTrans (fst_pair _ _)).eqTrans
    ((rational_radicand_sign_of_equal _ _ _ hd h).eqTrans
      ((congrSnd (rational_program_at _ _ _)).eqTrans (snd_pair _ _)).eqSymm)

theorem actual_square_radicand_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ le one (var 1) ⟶
      sign (squareRadicand (var 0) (var 1)) (stretch (var 1) (var 2)) ≐ sign (var 0) (var 2)) :=
  closeUniv 3 (.impI (.impI (square_radicand_sign _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_positive_cone_stretch_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ cone (var 1) ⟶ cone (stretch (var 0) (var 1))) :=
  closeUniv 2 (.impI (.impI (cone_stretch _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_stretched_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (equal (multiply (squareRadicand (var 0) (var 1)) (stretch (var 1) (var 2)) (stretch (var 1) (var 3)))
      (scale (var 1) (stretch (var 1) (multiply (var 0) (var 2) (var 3))))) :=
  closeUniv 4 (stretch_product _ _ _ _)
theorem actual_rational_positive_representation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (QuadraticRationalRadicand.isPositive (var 0) ⟶ rationalEq (var 0) (var 1) ⟶
      QuadraticRationalRadicand.isPositive (var 1)) :=
  closeUniv 2 (.impI (.impI (rational_positive_congr _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rational_zero_representation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ZT.eq (numeratorOf (var 0)) (ZT.ofNat zero) ⟶ rationalEq (var 0) (var 1) ⟶
      ZT.eq (numeratorOf (var 1)) (ZT.ofNat zero)) :=
  closeUniv 2 (.impI (.impI (rational_zero_congr _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_positive_rational_radicand_independence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (QuadraticRationalRadicand.isPositive (var 0) ⟶ rationalEq (var 0) (var 1) ⟶
      QuadraticRationalRadicand.sign (var 0) (var 2) ≐ QuadraticRationalRadicand.sign (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (rational_radicand_sign_of_equal _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rational_radicand_representation_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (QuadraticRationalRadicand.isPositive (var 0) ⟶ le one (var 3) ⟶
      QuadraticRationalClearing.represents (var 1) (var 2) (var 3) ⟶
      QuadraticRationalRadicand.sign (var 0) (var 1) ≐
        sign (QuadraticRationalRadicand.integerRadicand (var 0)) (stretch (denominatorOf (var 0)) (var 2))) :=
  closeUniv 4 (.impI (.impI (.impI (rational_representation_sign _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_radicand_scale_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_scaled_equal_signs_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ le one (var 1) ⟶
      fstT (sndT (sndT (run (var 0) (var 1) (var 2)))) ≐ sndT (sndT (sndT (run (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.impI (.impI (returned_equal_signs _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rational_radicand_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (rationalRun (var 0) (var 1) (var 2) ≐ rationalOutput (var 0) (var 1) (var 2)) :=
  closeUniv 3 (rational_program_at _ _ _)
theorem actual_returned_rational_equal_signs_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (QuadraticRationalRadicand.isPositive (var 0) ⟶ rationalEq (var 0) (var 1) ⟶
      fstT (rationalRun (var 0) (var 1) (var 2)) ≐ sndT (rationalRun (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (returned_rational_signs _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Algebra.QuadraticRadicandScaling
