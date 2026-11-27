import IPRADerivations.Analysis.Polynomials.Horner.GaussianReciprocalHorner

/-!
# Actual rational algebra for the Horner power-sum decomposition

Five original raw Gaussian codes determine their own positive common
denominator. Genuine arithmetic representations at its cube prove the
single exchange needed by the expansion induction. Associativity and a
contextual unit rule likewise concern actual canonical operation outputs;
no arbitrary original raw input is identified with its normalized code.
All operands and computed denominators are internal numerical inputs.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalSumAlgebra

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (qadd qmul represents positive_product qadd_represents qmul_represents represents_rescale
    represents_congr canonical_unique qadd_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qone qadd_congr rescale_to remainingDen remaining_den_positive)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (oneCode scale)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra
  (equal_refl equal_of_values re_add im_add re_mul im_mul re_scale im_scale re_one im_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Only representations of the five individual operands enter the
cubic arithmetic helper. The unconditional producer derives them below. -/
theorem exchange_from_representations (a delta b p s A Z B P S E : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (ha : Γ ⊢[PRAAx] represents a A E)
    (hz : Γ ⊢[PRAAx] represents delta Z E) (hb : Γ ⊢[PRAAx] represents b B E)
    (hp : Γ ⊢[PRAAx] represents p P E) (hs : Γ ⊢[PRAAx] represents s S E) : Γ ⊢[PRAAx]
    qadd (qmul (qadd (qmul a delta) b) p) s ≐
      qadd (qmul a (qmul p delta)) (qadd s (qmul b p)) := by
  have E2 := positive_product E E hE hE
  have E3 := positive_product (E*E) E E2 hE
  have b2 := represents_rescale b B E E hb
  have s3 := rescale_to s S E (E*E) (E*E*E) hs (by ipra_ring)
  have lhs := qadd_represents _ _ _ _ _ E3
    (qmul_represents _ _ _ _ _ _ E2 hE
      (qadd_represents _ _ _ _ _ E2 (qmul_represents _ _ _ _ _ _ hE hE ha hz) b2) hp) s3
  have first0 := qmul_represents _ _ _ _ _ _ hE E2 ha
    (qmul_represents _ _ _ _ _ _ hE hE hp hz)
  have first := represents_congr (.eqRefl _) (equal_refl _) (mul_assoc E E E).eqSymm first0
  have bp3 := represents_rescale _ _ (E*E) E (qmul_represents _ _ _ _ _ _ hE hE hb hp)
  have rhs := qadd_represents _ _ _ _ _ E3 first (qadd_represents _ _ _ _ _ E3 s3 bp3)
  apply canonical_unique _ _ _ _ (qadd_canonical _ _) (qadd_canonical _ _) E3 (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  apply equal_of_values <;> simp only [re_add,im_add,re_mul,im_mul,re_scale,im_scale] <;> ring

def commonDenominator (a delta b p s : PTm n) : PTm n := rawDen a*remainingDen delta b p s

ipra_subst commonDenominator [remainingDen]

theorem common_denominator_positive (a delta b p s : PTm n) : Γ ⊢[PRAAx]
    le one (commonDenominator a delta b p s) :=
  positive_product _ _ (raw_den_positive a) (remaining_den_positive delta b p s)

/-- Exact exchange for arbitrary original raw codes. Every common
representation is computed from those codes and their decoded denominators. -/
theorem horner_sum_exchange (a delta b p s : PTm n) : Γ ⊢[PRAAx]
    qadd (qmul (qadd (qmul a delta) b) p) s ≐
      qadd (qmul a (qmul p delta)) (qadd s (qmul b p)) := by
  let E := commonDenominator a delta b p s
  have ha := rescale_to a (rawGaussian a) (rawDen a) (remainingDen delta b p s) E
    (raw_represents (Γ := Γ) a) (.eqRefl _)
  have hz := rescale_to delta (rawGaussian delta) (rawDen delta) (remainingDen a b p s) E
    (raw_represents (Γ := Γ) delta) (by unfold E commonDenominator remainingDen; ipra_ring)
  have hb := rescale_to b (rawGaussian b) (rawDen b) (remainingDen a delta p s) E
    (raw_represents (Γ := Γ) b) (by unfold E commonDenominator remainingDen; ipra_ring)
  have hp := rescale_to p (rawGaussian p) (rawDen p) (remainingDen a delta b s) E
    (raw_represents (Γ := Γ) p) (by unfold E commonDenominator remainingDen; ipra_ring)
  have hs := rescale_to s (rawGaussian s) (rawDen s) (remainingDen a delta b p) E
    (raw_represents (Γ := Γ) s) (by unfold E commonDenominator remainingDen; ipra_ring)
  exact exchange_from_representations _ _ _ _ _ _ _ _ _ _ E (common_denominator_positive a delta b p s) ha hz hb hp hs

theorem associative_from_representations (a b c A B C E : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (ha : Γ ⊢[PRAAx] represents a A E)
    (hb : Γ ⊢[PRAAx] represents b B E) (hc : Γ ⊢[PRAAx] represents c C E) : Γ ⊢[PRAAx]
    qadd (qadd a b) c ≐ qadd a (qadd b c) := by
  have lhs := qadd_represents _ _ _ _ _ hE (qadd_represents _ _ _ _ _ hE ha hb) hc
  have rhs := qadd_represents _ _ _ _ _ hE ha (qadd_represents _ _ _ _ _ hE hb hc)
  apply canonical_unique _ _ _ _ (qadd_canonical _ _) (qadd_canonical _ _) hE (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  apply equal_of_values <;> simp only [re_add,im_add] <;> ring

theorem qadd_associative (a b c : PTm n) : Γ ⊢[PRAAx] qadd (qadd a b) c ≐ qadd a (qadd b c) := by
  let E := rawDen a*rawDen b*rawDen c
  have positive : Γ ⊢[PRAAx] le one E :=
    positive_product _ _ (positive_product _ _ (raw_den_positive a) (raw_den_positive b)) (raw_den_positive c)
  have ha := rescale_to a (rawGaussian a) (rawDen a) (rawDen b*rawDen c) E
    (raw_represents (Γ := Γ) a) (by unfold E; ipra_ring)
  have hb := rescale_to b (rawGaussian b) (rawDen b) (rawDen a*rawDen c) E
    (raw_represents (Γ := Γ) b) (by unfold E; ipra_ring)
  have hc := rescale_to c (rawGaussian c) (rawDen c) (rawDen a*rawDen b) E
    (raw_represents (Γ := Γ) c) (by unfold E; ipra_ring)
  exact associative_from_representations _ _ _ _ _ _ E positive ha hb hc

theorem contextual_unit_from_representations (a b A B E : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (ha : Γ ⊢[PRAAx] represents a A E)
    (hb : Γ ⊢[PRAAx] represents b B E) : Γ ⊢[PRAAx]
    qadd (qmul a qone) b ≐ qadd a b := by
  have E2 := positive_product E E hE hE
  have lhs := qadd_represents _ _ _ _ _ E2
    (qmul_represents _ _ _ _ _ _ hE hE ha (GaussianRationalReciprocal.qone_represents_scaled E))
    (represents_rescale b B E E hb)
  have rhs := represents_rescale _ _ E E (qadd_represents _ _ _ _ _ hE ha hb)
  apply canonical_unique _ _ _ _ (qadd_canonical _ _) (qadd_canonical _ _) E2 (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  apply equal_of_values <;> simp only [re_add,im_add,re_mul,im_mul,re_scale,im_scale,re_one,im_one] <;> ring

/-- This contextual law is valid for raw a. The unguarded statement
qmul a qone=a would incorrectly equate a raw code with its normal form. -/
theorem contextual_unit (a b : PTm n) : Γ ⊢[PRAAx] qadd (qmul a qone) b ≐ qadd a b := by
  let E := rawDen a*rawDen b
  have ha := rescale_to a (rawGaussian a) (rawDen a) (rawDen b) E (raw_represents (Γ := Γ) a) (.eqRefl _)
  have hb := rescale_to b (rawGaussian b) (rawDen b) (rawDen a) E (raw_represents (Γ := Γ) b) (mul_comm _ _)
  exact contextual_unit_from_representations _ _ _ _ E
    (positive_product _ _ (raw_den_positive a) (raw_den_positive b)) ha hb

/-- Exchange the last two summands in a left-associated Gaussian rational sum. -/
theorem qadd_swap_tail (a b c : PTm n) : Γ ⊢[PRAAx] qadd (qadd a b) c ≐ qadd (qadd a c) b :=
  (qadd_associative a b c).eqTrans
    ((qadd_congr (.eqRefl _) (GaussianReciprocalHorner.qadd_commutative b c)).eqTrans
      (qadd_associative a c b).eqSymm)

theorem shuffle_four (a b c d : PTm n) : Γ ⊢[PRAAx]
    qadd (qadd (qadd a b) c) d ≐ qadd (qadd a c) (qadd b d) :=
  (qadd_congr (qadd_swap_tail a b c) (.eqRefl _)).eqTrans (qadd_associative (qadd a c) b d)

/-! Actual PR5 output: both normalized exchange expressions and their
computed positive denominator. No arithmetic result is supplied as data. -/
def exchangeLeft (a delta b p s : PTm n) : PTm n := qadd (qmul (qadd (qmul a delta) b) p) s
def exchangeRight (a delta b p s : PTm n) : PTm n := qadd (qmul a (qmul p delta)) (qadd s (qmul b p))
def output (a delta b p s : PTm n) : PTm n :=
  pairT (exchangeLeft a delta b p s) (pairT (exchangeRight a delta b p s) (commonDenominator a delta b p s))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (a delta b p s : PTm n) : PTm n := PTm.app outputF ![a,delta,b,p,s]

ipra_subst exchangeLeft
ipra_subst exchangeRight
ipra_subst output
ipra_subst run

theorem program_at (a delta b p s : PTm n) : Γ ⊢[PRAAx] run a delta b p s ≐ output a delta b p s := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![a,delta,b,p,s]

theorem returned_left (a delta b p s : PTm n) : Γ ⊢[PRAAx]
    fstT (run a delta b p s) ≐ exchangeLeft a delta b p s :=
  (program_at a delta b p s).fstE
theorem returned_right (a delta b p s : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run a delta b p s)) ≐ exchangeRight a delta b p s :=
  (program_at a delta b p s).sndE.fstE
theorem returned_denominator (a delta b p s : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run a delta b p s)) ≐ commonDenominator a delta b p s :=
  (program_at a delta b p s).sndE.sndE
theorem returned_denominator_positive (a delta b p s : PTm n) : Γ ⊢[PRAAx]
    le one (sndT (sndT (run a delta b p s))) :=
  le_congr (.eqRefl _) (returned_denominator a delta b p s).eqSymm (common_denominator_positive a delta b p s)
theorem returned_exchange (a delta b p s : PTm n) : Γ ⊢[PRAAx]
    fstT (run a delta b p s) ≐ fstT (sndT (run a delta b p s)) :=
  (returned_left a delta b p s).eqTrans ((horner_sum_exchange a delta b p s).eqTrans (returned_right a delta b p s).eqSymm)

theorem horner_sum_exchange_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (exchangeLeft (var 0) (var 1) (var 2) (var 3) (var 4) ≐
      exchangeRight (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (horner_sum_exchange _ _ _ _ _)

theorem rational_sum_associativity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (qadd (qadd (var 0) (var 1)) (var 2) ≐ qadd (var 0) (qadd (var 1) (var 2))) :=
  closeUniv 3 (qadd_associative _ _ _)

theorem contextual_unit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (qadd (qmul (var 0) qone) (var 1) ≐ qadd (var 0) (var 1)) :=
  closeUniv 2 (contextual_unit _ _)

theorem rational_sum_shuffle_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (qadd (qadd (qadd (var 0) (var 1)) (var 2)) (var 3) ≐
      qadd (qadd (var 0) (var 2)) (qadd (var 1) (var 3))) :=
  closeUniv 4 (shuffle_four _ _ _ _)

theorem sum_algebra_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
      ((fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐
        exchangeLeft (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
        ((fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) ≐
          exchangeRight (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
          sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) ≐
            commonDenominator (var 0) (var 1) (var 2) (var 3) (var 4)))) :=
  closeUniv 5 (.andI (program_at _ _ _ _ _) (.andI (returned_left _ _ _ _ _)
    (.andI (returned_right _ _ _ _ _) (returned_denominator _ _ _ _ _))))

theorem returned_exchange_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐
       fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) ⋏
      le one (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))) :=
  closeUniv 5 (.andI (returned_exchange _ _ _ _ _) (returned_denominator_positive _ _ _ _ _))

end LeanProofs.IPRA.Analysis.GaussianRationalSumAlgebra
