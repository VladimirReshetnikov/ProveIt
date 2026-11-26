import IPRADerivations.Analysis.Polynomials.Horner.GaussianRationalHorner
import IPRADerivations.Foundations.BoundedSyntax

/-!
# Actual Gaussian-rational norms and original rational comparisons

Gaussian rationals are pairs of independently canonical scalar codes. Actual
negation, subtraction and squared norm normalize every scalar operation.
Their cross-value proofs retain both independently reduced denominators.
The actual rational comparison with (A/B)^2 is reflected to the exact cleared
integer squared-norm bound. No cleared bound is an input to that direction;
all numerator data, denominators and tolerances are internal, including A=0.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalMetric

open_ipra
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (re im normSq normSq_eval)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra
  (equal_re equal_im re_neg im_neg re_sub im_sub equal_of_values)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (represents canonical ofGaussian qadd qadd_represents qadd_canonical canonical_pair
    scalar_congr scalar_add_same positive_product represents_congr)
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (normalize normalize_preserves_value)
open LeanProofs.IPRA.Analysis.RationalRepresentations
open LeanProofs.IPRA.Foundations.BoundedSyntax

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def qnegative (q : PTm n) : PTm n := pairT
  (RationalArithmetic.negative (fstT q)) (RationalArithmetic.negative (sndT q))
def qsub (q r : PTm n) : PTm n := qadd q (qnegative r)
def qnormSq (q : PTm n) : PTm n := RationalArithmetic.add
  (RationalArithmetic.multiply (fstT q) (fstT q))
  (RationalArithmetic.multiply (sndT q) (sndT q))
def squaredTolerance (A B : PTm n) : PTm n := normalize (ZT.ofNat (A*A)) (B*B)
def bounded (q A B : PTm n) : Fm PTm n := RationalArgmin.rationalLE (qnormSq q) (squaredTolerance A B)
def distanceBounded (q r A B : PTm n) : Fm PTm n := bounded (qsub q r) A B

ipra_subst qnegative
ipra_subst qsub
ipra_subst qnormSq
ipra_subst squaredTolerance
ipra_subst bounded
ipra_subst distanceBounded

theorem qnegative_canonical (q : PTm n) : Γ ⊢[PRAAx] canonical (qnegative q) :=
  canonical_pair _ _ (RationalArithmetic.negative_guard _) (RationalArithmetic.negative_guard _)
theorem qsub_canonical (q r : PTm n) : Γ ⊢[PRAAx] canonical (qsub q r) := qadd_canonical _ _
theorem qnormSq_canonical (q : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (qnormSq q) :=
  RationalArithmetic.add_guard _ _

theorem qnegative_represents (q a E : PTm n) (hq : Γ ⊢[PRAAx] represents q a E) :
    Γ ⊢[PRAAx] represents (qnegative q) (ComplexLogarithmRemainder.neg a) E := by
  refine .andI
    (scalar_congr (fst_pair _ _).eqSymm ?_ (.eqRefl _) (represents_negative _ _ _ (Prf.andE₁ hq)))
    (scalar_congr (snd_pair _ _).eqSymm ?_ (.eqRefl _) (represents_negative _ _ _ (Prf.andE₂ hq)))
  all_goals apply ZT.derive; simp only [ZT.toZ_neg,re_neg,im_neg]

theorem qsub_represents (q r a b E : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hq : Γ ⊢[PRAAx] represents q a E) (hr : Γ ⊢[PRAAx] represents r b E) :
    Γ ⊢[PRAAx] represents (qsub q r) (GaussianRootAlgebra.sub a b) E :=
  qadd_represents _ _ _ _ _ hE hq (qnegative_represents r b E hr)

/-- The squared norm is computed by actual scalar arithmetic. Its normalized
output denominator can differ from both normalized component denominators. -/
theorem qnormSq_represents (q a E : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hq : Γ ⊢[PRAAx] represents q a E) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (qnormSq q) (ZT.ofNat (normSq a)) (E*E) := by
  have rr := represents_multiply _ _ _ _ _ _ (Prf.andE₁ hq) (Prf.andE₁ hq)
  have ii := represents_multiply _ _ _ _ _ _ (Prf.andE₂ hq) (Prf.andE₂ hq)
  have h := scalar_add_same _ _ _ _ _ (positive_product E E hE hE) rr ii
  apply scalar_congr (.eqRefl _) (hAB := .eqRefl _) (h := h)
  apply ZT.derive
  simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
  rw [normSq_eval]
  ring

theorem squared_tolerance_represents (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (squaredTolerance A B) (ZT.ofNat (A*A)) (B*B) :=
  normalize_preserves_value _ _ (positive_product B B hB hB)

/-- Reflect a rational comparison between nonnegative raw fraction values.
Only the two actual decoded scalar denominators are canceled in this direction. -/
theorem comparison_to_cleared (c d x y E F : PTm n)
    (hc : Γ ⊢[PRAAx] RationalArithmetic.represents c (ZT.ofNat x) E)
    (hd : Γ ⊢[PRAAx] RationalArithmetic.represents d (ZT.ofNat y) F)
    (h : Γ ⊢[PRAAx] RationalArgmin.rationalLE c d) :
    Γ ⊢[PRAAx] le (F*x) (y*E) := by
  have ec := ZT.toZ_eq hc
  have ed := ZT.toZ_eq hd
  have cmp := natEq (eq_add_of_le h)
  have scaled : Γ ⊢[PRAAx]
      le ((denominatorOf c*denominatorOf d)*(F*x))
        ((denominatorOf c*denominatorOf d)*(y*E)) := by
    refine le_of_eq_add (d := E*F*monus (RationalArgmin.left d c) (RationalArgmin.left c d)) ?_
    apply deriveNat
    simp only [RationalArithmetic.represents,ZT.toZ_mul,ZT.toZ_ofNat] at ec ed
    simp only [ZT.toZ] at ec ed
    unfold RationalArgmin.left at cmp ⊢
    ipra_simps
    linear_combination 𝔞(E)*𝔞(denominatorOf c)*ed-𝔞(F)*𝔞(denominatorOf d)*ec+𝔞(E)*𝔞(F)*cmp
  exact RationalValueBounds.positive_cancel
    (positive_product _ _ (RationalArgmin.denominator_positive c) (RationalArgmin.denominator_positive d)) scaled

theorem comparison_of_cleared (c d x y E F : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hF : Γ ⊢[PRAAx] le one F)
    (hc : Γ ⊢[PRAAx] RationalArithmetic.represents c (ZT.ofNat x) E)
    (hd : Γ ⊢[PRAAx] RationalArithmetic.represents d (ZT.ofNat y) F)
    (h : Γ ⊢[PRAAx] le (F*x) (y*E)) : Γ ⊢[PRAAx] RationalArgmin.rationalLE c d := by
  apply RationalArithmetic.order_of_representations c d (ZT.ofNat x) (ZT.ofNat y) E F hc hd hE hF
  apply zle_of_toZ (monus (y*E) (F*x))
  have e := natEq (eq_add_of_le h)
  ipra_simps
  linear_combination -e

/-- The original rational norm comparison is exactly the cleared inequality,
not a supplied raw bound or an independently chosen integer radius. -/
theorem bounded_iff (q a E A B : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] represents q a E) : Γ ⊢[PRAAx]
    Fm.iff (bounded q A B) (le ((B*B)*normSq a) ((A*A)*(E*E))) := by
  have hn := qnormSq_represents q a E hE hq
  have ht := squared_tolerance_represents A B hB
  exact .iffI
    (.impI (comparison_to_cleared _ _ _ _ _ _ hn.wk ht.wk Prf.hyp0))
    (.impI (comparison_of_cleared _ _ _ _ _ _ (positive_product E E hE hE).wk
      (positive_product B B hB hB).wk hn.wk ht.wk Prf.hyp0))

theorem bounded_difference_iff (q r a b E A B : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] represents q a E) (hr : Γ ⊢[PRAAx] represents r b E) :
    Γ ⊢[PRAAx] Fm.iff (distanceBounded q r A B)
      (le ((B*B)*normSq (GaussianRootAlgebra.sub a b)) ((A*A)*(E*E))) :=
  bounded_iff _ _ _ _ _ hE hB (qsub_represents q r a b E hE hq hr)

/-- The original normalized coefficient comparison supplies the cleared
coefficient error used by the homogeneous perturbation recurrence. -/
theorem normalized_coefficient_bound_iff (S T N D i A B : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    Fm.iff
      (distanceBounded (GaussianRationalRootProduct.rationalCoefficient S N D i)
        (GaussianRationalRootProduct.rationalCoefficient T N D i) A B)
      (le ((B*B)*normSq (GaussianRootAlgebra.sub
          (GaussianRationalRootProduct.scaledCoefficient S N D i)
          (GaussianRationalRootProduct.scaledCoefficient T N D i)))
        ((A*A)*(pw D N*pw D N))) :=
  bounded_difference_iff _ _ _ _ _ _ _
    (GaussianRationalRootProduct.common_denominator_positive D N hD) hB
    (GaussianRationalHorner.ofGaussian_represents _ _ (GaussianRationalRootProduct.common_denominator_positive D N hD))
    (GaussianRationalHorner.ofGaussian_represents _ _ (GaussianRationalRootProduct.common_denominator_positive D N hD))

theorem bounded_to_cleared (q a E A B : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] represents q a E) (h : Γ ⊢[PRAAx] bounded q A B) :
    Γ ⊢[PRAAx] le ((B*B)*normSq a) ((A*A)*(E*E)) :=
  (bounded_iff q a E A B hE hB hq).iffMp h

theorem bounded_of_cleared (q a E A B : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] represents q a E)
    (h : Γ ⊢[PRAAx] le ((B*B)*normSq a) ((A*A)*(E*E))) :
    Γ ⊢[PRAAx] bounded q A B := (bounded_iff q a E A B hE hB hq).iffMpr h

/-- Zero tolerance forces the represented Gaussian value's actual squared
norm to vanish; no positivity of the numerator is needed. -/
theorem bounded_zero_norm (q a E B : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] represents q a E) (h : Γ ⊢[PRAAx] bounded q zero B) :
    Γ ⊢[PRAAx] normSq a ≐ zero := by
  have raw := bounded_to_cleared q a E zero B hE hB hq h
  have scaled : Γ ⊢[PRAAx] le ((B*B)*normSq a) ((B*B)*zero) :=
    le_congr (.eqRefl _) (by ipra_ring) raw
  exact le_antisymm (RationalValueBounds.positive_cancel (positive_product B B hB hB) scaled) (zero_le _)

/-! Fixed actual programs and a Boolean checker of the rational comparison. -/

def metricOutput (q r : PTm n) : PTm n := pairT (qnegative q) (pairT (qsub q r) (qnormSq q))
def metricOutputF : PR 2 := PTm.toPR (metricOutput (var 0) (var 1))
ipra_subst metricOutput

theorem metric_program_at (q r : PTm n) : Γ ⊢[PRAAx] ap2 metricOutputF q r ≐ metricOutput q r := by
  simpa [metricOutputF,ap2] using toPR_eq (Γ := Γ) (metricOutput (var 0) (var 1) : PTm 2) ![q,r]

def boundedSyntax (q A B : PTm n) : BFm n := .le
  (RationalArgmin.left (qnormSq q) (squaredTolerance A B))
  (RationalArgmin.left (squaredTolerance A B) (qnormSq q))
def boundedCheckF : PR 3 := bitF (boundedSyntax (var 0) (var 1) (var 2))
def check (q A B : PTm n) : PTm n := ap3 boundedCheckF q A B

theorem bounded_formula (q A B : PTm n) : formula (boundedSyntax q A B) = bounded q A B := rfl

theorem checker_program (q A B : PTm n) : Γ ⊢[PRAAx] check q A B ≐
    bit (boundedSyntax (var 0) (var 1) (var 2)) ![q,A,B] :=
  program_correct (boundedSyntax (var 0) (var 1) (var 2)) ![q,A,B]

theorem checker_reflection (q A B : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (check q A B ≐ one) (bounded q A B) := by
  have h : Γ ⊢[PRAAx] Fm.iff
      (bit (boundedSyntax (var 0) (var 1) (var 2)) ![q,A,B] ≐ one) (bounded q A B) := by
    have r := bounded_reflection (Γ := Γ) (boundedSyntax (var 0) (var 1) (var 2)) ![q,A,B]
    rw [bounded_formula] at r
    simpa only [subst_bounded,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using r
  have p := checker_program (Γ := Γ) q A B
  exact .iffI (.impI (h.wk.iffMp (p.wk.eqSymm.eqTrans Prf.hyp0)))
    (.impI (p.wk.eqTrans (h.wk.iffMpr Prf.hyp0)))

theorem checker_boolean (q A B : PTm n) : Γ ⊢[PRAAx] (check q A B ≐ zero) ⋎ (check q A B ≐ one) := by
  have p := checker_program (Γ := Γ) q A B
  exact .orE (bit_cases (boundedSyntax (var 0) (var 1) (var 2)) ![q,A,B])
    (.orI₁ (p.wk.eqTrans Prf.hyp0)) (.orI₂ (p.wk.eqTrans Prf.hyp0))

theorem checker_cleared_iff (q a E A B : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] represents q a E) : Γ ⊢[PRAAx]
    Fm.iff (check q A B ≐ one) (le ((B*B)*normSq a) ((A*A)*(E*E))) := by
  have comp := checker_reflection (Γ := Γ) q A B
  have raw := bounded_iff q a E A B hE hB hq
  exact .iffI (.impI (raw.wk.iffMp (comp.wk.iffMp Prf.hyp0)))
    (.impI (comp.wk.iffMpr (raw.wk.iffMpr Prf.hyp0)))

/-! Closed schemes quantify all numerical values and denominator data. -/

theorem gaussian_metric_values_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 4) ⟶ represents (var 0) (var 2) (var 4) ⟶ represents (var 1) (var 3) (var 4) ⟶
      (represents (qsub (var 0) (var 1)) (GaussianRootAlgebra.sub (var 2) (var 3)) (var 4) ⋏
        RationalArithmetic.represents (qnormSq (var 0)) (ZT.ofNat (normSq (var 2))) (var 4*var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (.andI
    (qsub_represents _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)
    (qnormSq_represents _ _ _ Prf.hyp0.wk.wk Prf.hyp1)))))

theorem rational_norm_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ le one (var 4) ⟶ represents (var 0) (var 1) (var 2) ⟶
      Fm.iff (bounded (var 0) (var 3) (var 4))
        (le ((var 4*var 4)*normSq (var 1)) ((var 3*var 3)*(var 2*var 2)))) :=
  closeUniv 5 (.impI (.impI (.impI
    (bounded_iff _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem rational_distance_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 4) ⟶ le one (var 6) ⟶ represents (var 0) (var 2) (var 4) ⟶
      represents (var 1) (var 3) (var 4) ⟶
      Fm.iff (distanceBounded (var 0) (var 1) (var 5) (var 6))
        (le ((var 6*var 6)*normSq (GaussianRootAlgebra.sub (var 2) (var 3)))
          ((var 5*var 5)*(var 4*var 4)))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI
    (bounded_difference_iff _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem actual_coefficient_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 3) ⟶ le one (var 6) ⟶
      Fm.iff
        (distanceBounded (GaussianRationalRootProduct.rationalCoefficient (var 0) (var 2) (var 3) (var 4))
          (GaussianRationalRootProduct.rationalCoefficient (var 1) (var 2) (var 3) (var 4)) (var 5) (var 6))
        (le ((var 6*var 6)*normSq (GaussianRootAlgebra.sub
            (GaussianRationalRootProduct.scaledCoefficient (var 0) (var 2) (var 3) (var 4))
            (GaussianRationalRootProduct.scaledCoefficient (var 1) (var 2) (var 3) (var 4))))
          ((var 5*var 5)*(pw (var 3) (var 2)*pw (var 3) (var 2))))) :=
  closeUniv 7 (.impI (.impI (normalized_coefficient_bound_iff _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem metric_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((ap2 metricOutputF (var 0) (var 1) ≐ metricOutput (var 0) (var 1)) ⋏
      (canonical (qnegative (var 0)) ⋏ (canonical (qsub (var 0) (var 1)) ⋏
        RationalNormalForm.wellFormed (qnormSq (var 0))))) :=
  closeUniv 2 (.andI (metric_program_at _ _)
    (.andI (qnegative_canonical _) (.andI (qsub_canonical _ _) (qnormSq_canonical _))))

theorem metric_checker_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ le one (var 4) ⟶ represents (var 0) (var 1) (var 2) ⟶
      Fm.iff (check (var 0) (var 3) (var 4) ≐ one)
        (le ((var 4*var 4)*normSq (var 1)) ((var 3*var 3)*(var 2*var 2)))) :=
  closeUniv 5 (.impI (.impI (.impI
    (checker_cleared_iff _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem zero_tolerance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le one (var 3) ⟶ represents (var 0) (var 1) (var 2) ⟶
      bounded (var 0) zero (var 3) ⟶ (normSq (var 1) ≐ zero)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI
    (bounded_zero_norm _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianRationalMetric
