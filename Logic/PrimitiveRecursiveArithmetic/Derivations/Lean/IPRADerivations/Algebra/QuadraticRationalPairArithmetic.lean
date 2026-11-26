import IPRADerivations.Algebra.QuadraticRationalClearing
import IPRADerivations.Analysis.RationalArithmetic.RationalAlgebra

/-!
# Actual rational pair arithmetic at a positive integer radicand

Operations use the ORIGINAL canonical rational scalar programs. Their
common-denominator representations are derived from the actual input
codes. Sign closure and the zero-product law then follow the proved
integer-stage certificates and positive denominator scaling.
Rational radicands and an internal radical tower remain separate.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Algebra.QuadraticRationalPairArithmetic

open_ipra
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open QuadraticSignCertificates (first second equal)
open QuadraticRationalClearing (clear denominator represents clear_represents denominator_positive)
open QuadraticPositiveScaling (scale scale_first scale_second sign_scale)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def scalar (d : PTm n) : PTm n := LeanProofs.IPRA.Analysis.RationalIntegerNormalization.normalize (ZT.ofNat d) one
def add (x y : PTm n) : PTm n := pairT
  (LeanProofs.IPRA.Analysis.RationalArithmetic.add (fstT x) (fstT y))
  (LeanProofs.IPRA.Analysis.RationalArithmetic.add (sndT x) (sndT y))
def negative (x : PTm n) : PTm n := pairT
  (LeanProofs.IPRA.Analysis.RationalArithmetic.negative (fstT x))
  (LeanProofs.IPRA.Analysis.RationalArithmetic.negative (sndT x))
def multiply (d x y : PTm n) : PTm n := pairT
  (LeanProofs.IPRA.Analysis.RationalArithmetic.add
    (LeanProofs.IPRA.Analysis.RationalArithmetic.multiply (fstT x) (fstT y))
    (LeanProofs.IPRA.Analysis.RationalArithmetic.multiply (scalar d)
      (LeanProofs.IPRA.Analysis.RationalArithmetic.multiply (sndT x) (sndT y))))
  (LeanProofs.IPRA.Analysis.RationalArithmetic.add
    (LeanProofs.IPRA.Analysis.RationalArithmetic.multiply (fstT x) (sndT y))
    (LeanProofs.IPRA.Analysis.RationalArithmetic.multiply (sndT x) (fstT y)))
def positive (d x : PTm n) : Fm PTm n := QuadraticRationalClearing.sign d x ≐ one
def isZero (d x : PTm n) : Fm PTm n := QuadraticRationalClearing.sign d x ≐ zero
ipra_subst scalar [one]
ipra_subst add
ipra_subst negative
ipra_subst multiply
ipra_subst positive
ipra_subst isZero

theorem scalar_code_congr {q r : PTm n} (a : ZT n) (D : PTm n) (h : Γ ⊢[PRAAx] q ≐ r)
    (hr : Γ ⊢[PRAAx] LeanProofs.IPRA.Analysis.RationalArithmetic.represents r a D) : Γ ⊢[PRAAx]
    LeanProofs.IPRA.Analysis.RationalArithmetic.represents q a D := by
  simpa [ZT.subst] using
    Prf.eqSubst (LeanProofs.IPRA.Analysis.RationalArithmetic.represents (var 0) (⟨var 1,var 2⟩ : ZT 4) (var 3))
      ![r,a.pos,a.neg,D] ![q,a.pos,a.neg,D]
      (fun i => by fin_cases i; exact h.eqSymm; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _)
      (by simpa [ZT.subst] using hr)
theorem scalar_value_congr (q D : PTm n) (a b : ZT n) (h : ZT.toZ Γ a = ZT.toZ Γ b)
    (ha : Γ ⊢[PRAAx] LeanProofs.IPRA.Analysis.RationalArithmetic.represents q a D) : Γ ⊢[PRAAx]
    LeanProofs.IPRA.Analysis.RationalArithmetic.represents q b D := by
  apply ZT.derive
  have e := ZT.toZ_eq ha
  simp only [ZT.toZ_mul,ZT.toZ_ofNat] at e ⊢
  rw [← h]; exact e
theorem scalar_add_same (q r D : PTm n) (a b : ZT n) (hD : Γ ⊢[PRAAx] le one D)
    (hq : Γ ⊢[PRAAx] LeanProofs.IPRA.Analysis.RationalArithmetic.represents q a D)
    (hr : Γ ⊢[PRAAx] LeanProofs.IPRA.Analysis.RationalArithmetic.represents r b D) : Γ ⊢[PRAAx]
    LeanProofs.IPRA.Analysis.RationalArithmetic.represents (LeanProofs.IPRA.Analysis.RationalArithmetic.add q r) (a+b) D := by
  apply LeanProofs.IPRA.Analysis.RationalNormalForm.positive_integer_cancel D _ _ hD
  ipra_lc ZT.toZ_eq (LeanProofs.IPRA.Analysis.RationalRepresentations.represents_add q r a b D D hq hr)
theorem scalar_represents (d : PTm n) : Γ ⊢[PRAAx]
    LeanProofs.IPRA.Analysis.RationalArithmetic.represents (scalar d) (ZT.ofNat d) one :=
  LeanProofs.IPRA.Analysis.RationalIntegerNormalization.normalize_preserves_value _ _ (le_refl one)
theorem scalar_multiply (d q D : PTm n) (a : ZT n)
    (h : Γ ⊢[PRAAx] LeanProofs.IPRA.Analysis.RationalArithmetic.represents q a D) : Γ ⊢[PRAAx]
    LeanProofs.IPRA.Analysis.RationalArithmetic.represents
      (LeanProofs.IPRA.Analysis.RationalArithmetic.multiply (scalar d) q) (ZT.ofNat d*a) D := by
  apply ZT.derive
  have e := ZT.toZ_eq (LeanProofs.IPRA.Analysis.RationalRepresentations.represents_multiply (scalar d) q _ _ one D (scalar_represents d) h)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,Q.mk_one,map_mul,map_one] at e ⊢
  simpa only [_root_.one_mul] using e

theorem add_represents (x y A D B E : PTm n) (hx : Γ ⊢[PRAAx] represents x A D)
    (hy : Γ ⊢[PRAAx] represents y B E) : Γ ⊢[PRAAx]
    represents (add x y) (QuadraticSignCertificates.add (scale E A) (scale D B)) (D*E) := by
  refine .andI ?_ ?_
  · apply scalar_code_congr _ _ (fst_pair _ _)
    apply scalar_value_congr _ _ _ _ ?_ (LeanProofs.IPRA.Analysis.RationalRepresentations.represents_add _ _ _ _ D E (.andE₁ hx) (.andE₁ hy))
    simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,QuadraticConeOrder.add_first,scale_first]; ring
  · apply scalar_code_congr _ _ (snd_pair _ _)
    apply scalar_value_congr _ _ _ _ ?_ (LeanProofs.IPRA.Analysis.RationalRepresentations.represents_add _ _ _ _ D E (.andE₂ hx) (.andE₂ hy))
    simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,QuadraticConeOrder.add_second,scale_second]; ring
theorem negative_represents (x A D : PTm n) (hx : Γ ⊢[PRAAx] represents x A D) : Γ ⊢[PRAAx]
    represents (negative x) (QuadraticSignCertificates.negative A) D := by
  refine .andI ?_ ?_
  · apply scalar_code_congr _ _ (fst_pair _ _)
    apply scalar_value_congr _ _ _ _ ?_ (LeanProofs.IPRA.Analysis.RationalRepresentations.represents_negative _ _ _ (.andE₁ hx))
    rw [ZT.toZ_neg,QuadraticSignCertificates.negative_first]
  · apply scalar_code_congr _ _ (snd_pair _ _)
    apply scalar_value_congr _ _ _ _ ?_ (LeanProofs.IPRA.Analysis.RationalRepresentations.represents_negative _ _ _ (.andE₂ hx))
    rw [ZT.toZ_neg,QuadraticSignCertificates.negative_second]
theorem multiply_represents (d x y A D B E : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hE : Γ ⊢[PRAAx] le one E)
    (hx : Γ ⊢[PRAAx] represents x A D) (hy : Γ ⊢[PRAAx] represents y B E) : Γ ⊢[PRAAx]
    represents (multiply d x y) (QuadraticSignCertificates.multiply d A B) (D*E) := by
  refine .andI ?_ ?_
  · apply scalar_code_congr _ _ (fst_pair _ _)
    apply scalar_value_congr _ _ _ _ ?_ (scalar_add_same _ _ (D*E) _ _
      (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product hD hE)
      (LeanProofs.IPRA.Analysis.RationalRepresentations.represents_multiply _ _ _ _ D E (.andE₁ hx) (.andE₁ hy))
      (scalar_multiply d _ (D*E) _ (LeanProofs.IPRA.Analysis.RationalRepresentations.represents_multiply _ _ _ _ D E (.andE₂ hx) (.andE₂ hy))))
    simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,QuadraticSignCertificates.multiply_first]
  · apply scalar_code_congr _ _ (snd_pair _ _)
    apply scalar_value_congr _ _ _ _ ?_ (scalar_add_same _ _ (D*E) _ _
      (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product hD hE)
      (LeanProofs.IPRA.Analysis.RationalRepresentations.represents_multiply _ _ _ _ D E (.andE₁ hx) (.andE₂ hy))
      (LeanProofs.IPRA.Analysis.RationalRepresentations.represents_multiply _ _ _ _ D E (.andE₂ hx) (.andE₁ hy)))
    simp only [ZT.toZ_add,ZT.toZ_mul,QuadraticSignCertificates.multiply_second]

def wellFormed (x : PTm n) : Fm PTm n :=
  LeanProofs.IPRA.Analysis.RationalNormalForm.wellFormed (fstT x) ⋏
    LeanProofs.IPRA.Analysis.RationalNormalForm.wellFormed (sndT x)
ipra_subst wellFormed
theorem add_well_formed (x y : PTm n) : Γ ⊢[PRAAx] wellFormed (add x y) :=
  .andI (LeanProofs.IPRA.Analysis.RationalArithmetic.guard_congr (fst_pair _ _) (LeanProofs.IPRA.Analysis.RationalArithmetic.add_guard _ _))
    (LeanProofs.IPRA.Analysis.RationalArithmetic.guard_congr (snd_pair _ _) (LeanProofs.IPRA.Analysis.RationalArithmetic.add_guard _ _))
theorem negative_well_formed (x : PTm n) : Γ ⊢[PRAAx] wellFormed (negative x) :=
  .andI (LeanProofs.IPRA.Analysis.RationalArithmetic.guard_congr (fst_pair _ _) (LeanProofs.IPRA.Analysis.RationalArithmetic.negative_guard _))
    (LeanProofs.IPRA.Analysis.RationalArithmetic.guard_congr (snd_pair _ _) (LeanProofs.IPRA.Analysis.RationalArithmetic.negative_guard _))
theorem multiply_well_formed (d x y : PTm n) : Γ ⊢[PRAAx] wellFormed (multiply d x y) :=
  .andI (LeanProofs.IPRA.Analysis.RationalArithmetic.guard_congr (fst_pair _ _) (LeanProofs.IPRA.Analysis.RationalArithmetic.add_guard _ _))
    (LeanProofs.IPRA.Analysis.RationalArithmetic.guard_congr (snd_pair _ _) (LeanProofs.IPRA.Analysis.RationalArithmetic.add_guard _ _))

theorem add_sign (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    QuadraticRationalClearing.sign d (add x y) ≐ QuadraticSignCertificates.sign d
      (QuadraticSignCertificates.add (scale (denominator y) (clear x)) (scale (denominator x) (clear y))) :=
  QuadraticRationalClearing.representation_sign _ _ _ _ hd
    (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product (denominator_positive x) (denominator_positive y))
    (add_represents _ _ _ _ _ _ (clear_represents x) (clear_represents y))
theorem negative_sign (d x : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    QuadraticRationalClearing.sign d (negative x) ≐ QuadraticSignCertificates.sign d (QuadraticSignCertificates.negative (clear x)) :=
  QuadraticRationalClearing.representation_sign _ _ _ _ hd (denominator_positive x)
    (negative_represents _ _ _ (clear_represents x))
theorem multiply_sign (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    QuadraticRationalClearing.sign d (multiply d x y) ≐ QuadraticSignCertificates.sign d (QuadraticSignCertificates.multiply d (clear x) (clear y)) :=
  QuadraticRationalClearing.representation_sign _ _ _ _ hd
    (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product (denominator_positive x) (denominator_positive y))
    (multiply_represents _ _ _ _ _ _ _ (denominator_positive x) (denominator_positive y) (clear_represents x) (clear_represents y))
theorem positive_add (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hx : Γ ⊢[PRAAx] positive d x) (hy : Γ ⊢[PRAAx] positive d y) : Γ ⊢[PRAAx] positive d (add x y) :=
  (add_sign _ _ _ hd).eqTrans (QuadraticIntegerOrder.positive_add _ _ _ hd
    ((sign_scale d (denominator y) (clear x) hd (denominator_positive y)).eqTrans hx)
    ((sign_scale d (denominator x) (clear y) hd (denominator_positive x)).eqTrans hy))
theorem positive_multiply (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hx : Γ ⊢[PRAAx] positive d x) (hy : Γ ⊢[PRAAx] positive d y) : Γ ⊢[PRAAx] positive d (multiply d x y) :=
  (multiply_sign _ _ _ hd).eqTrans (QuadraticIntegerOrder.positive_multiply _ _ _ hd hx hy)
theorem zero_negative (d x : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hx : Γ ⊢[PRAAx] isZero d x) : Γ ⊢[PRAAx] isZero d (negative x) :=
  (negative_sign _ _ hd).eqTrans (QuadraticIntegerOrder.zero_negative _ _ hd hx)
theorem zero_multiply (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hx : Γ ⊢[PRAAx] isZero d x) : Γ ⊢[PRAAx] isZero d (multiply d x y) :=
  (multiply_sign _ _ _ hd).eqTrans (QuadraticIntegerOrder.zero_multiply _ _ _ hd hx)
theorem zero_add (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hx : Γ ⊢[PRAAx] isZero d x) (hy : Γ ⊢[PRAAx] isZero d y) : Γ ⊢[PRAAx] isZero d (add x y) :=
  (add_sign _ _ _ hd).eqTrans (QuadraticIntegerOrder.zero_add _ _ _ hd
    ((sign_scale d (denominator y) (clear x) hd (denominator_positive y)).eqTrans hx)
    ((sign_scale d (denominator x) (clear y) hd (denominator_positive x)).eqTrans hy))
theorem positive_add_zero (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hx : Γ ⊢[PRAAx] positive d x) (hy : Γ ⊢[PRAAx] isZero d y) : Γ ⊢[PRAAx] positive d (add x y) :=
  (add_sign _ _ _ hd).eqTrans (QuadraticIntegerOrder.positive_add_zero _ _ _ hd
    ((sign_scale d (denominator y) (clear x) hd (denominator_positive y)).eqTrans hx)
    ((sign_scale d (denominator x) (clear y) hd (denominator_positive x)).eqTrans hy))
theorem zero_product_reflect (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] isZero d (multiply d x y)) : Γ ⊢[PRAAx] isZero d x ⋎ isZero d y :=
  QuadraticIntegerOrder.zero_product_reflect _ _ _ hd ((multiply_sign _ _ _ hd).eqSymm.eqTrans h)

def output (d x y : PTm n) : PTm n := pairT (add x y) (pairT (negative x) (multiply d x y))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (d x y : PTm n) : PTm n := ap3 outputF d x y
ipra_subst output
ipra_subst run
theorem program_at (d x y : PTm n) : Γ ⊢[PRAAx] run d x y ≐ output d x y := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![d,x,y]
theorem returned_add (d x y : PTm n) : Γ ⊢[PRAAx] fstT (run d x y) ≐ add x y :=
  (program_at _ _ _).fstE
theorem returned_negative (d x y : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run d x y)) ≐ negative x :=
  (program_at _ _ _).sndE.fstE
theorem returned_multiply (d x y : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run d x y)) ≐ multiply d x y :=
  (program_at _ _ _).sndE.sndE

theorem actual_rational_pair_normalization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (wellFormed (add (var 1) (var 2)) ⋏ (wellFormed (negative (var 1)) ⋏ wellFormed (multiply (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.andI (add_well_formed _ _) (.andI (negative_well_formed _) (multiply_well_formed _ _ _)))
theorem actual_rational_pair_add_representation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (represents (add (var 0) (var 1))
      (QuadraticSignCertificates.add (scale (denominator (var 1)) (clear (var 0))) (scale (denominator (var 0)) (clear (var 1))))
      (denominator (var 0)*denominator (var 1))) :=
  closeUniv 2 (add_represents _ _ _ _ _ _ (clear_represents _) (clear_represents _))
theorem actual_rational_pair_negative_representation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (represents (negative (var 0)) (QuadraticSignCertificates.negative (clear (var 0))) (denominator (var 0))) :=
  closeUniv 1 (negative_represents _ _ _ (clear_represents _))
theorem actual_rational_pair_product_representation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (represents (multiply (var 0) (var 1) (var 2)) (QuadraticSignCertificates.multiply (var 0) (clear (var 1)) (clear (var 2)))
      (denominator (var 1)*denominator (var 2))) :=
  closeUniv 3 (multiply_represents _ _ _ _ _ _ _ (denominator_positive _) (denominator_positive _) (clear_represents _) (clear_represents _))
theorem actual_rational_pair_positive_closure_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ positive (var 0) (var 1) ⟶ positive (var 0) (var 2) ⟶
      (positive (var 0) (add (var 1) (var 2)) ⋏ positive (var 0) (multiply (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (.impI (.impI (.andI (positive_add _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)
    (positive_multiply _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_rational_pair_zero_ideal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ isZero (var 0) (var 1) ⟶
      (isZero (var 0) (negative (var 1)) ⋏ (isZero (var 0) (multiply (var 0) (var 1) (var 2)) ⋏
        (isZero (var 0) (var 2) ⟶ isZero (var 0) (add (var 1) (var 2)))))) :=
  closeUniv 3 (.impI (.impI (.andI (zero_negative _ _ Prf.hyp1 Prf.hyp0)
    (.andI (zero_multiply _ _ _ Prf.hyp1 Prf.hyp0) (.impI (zero_add _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))
theorem actual_rational_pair_positive_plus_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ positive (var 0) (var 1) ⟶ isZero (var 0) (var 2) ⟶ positive (var 0) (add (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (positive_add_zero _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_rational_pair_domain_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ isZero (var 0) (multiply (var 0) (var 1) (var 2)) ⟶ (isZero (var 0) (var 1) ⋎ isZero (var 0) (var 2))) :=
  closeUniv 3 (.impI (.impI (zero_product_reflect _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rational_pair_arithmetic_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)

end LeanProofs.IPRA.Algebra.QuadraticRationalPairArithmetic
