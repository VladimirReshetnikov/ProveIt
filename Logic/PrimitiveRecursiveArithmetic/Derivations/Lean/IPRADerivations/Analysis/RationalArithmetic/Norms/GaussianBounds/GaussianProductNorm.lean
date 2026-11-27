import IPRADerivations.Analysis.Polynomials.RootFinding.Reconstruction.RootProducts.GaussianRootProduct
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.Estimates.RationalProductWitness

/-!
# A least nearby Gaussian factor from an actual polynomial evaluation

Finite-demand source04 `lem:product-stability`, its squared-distance factor
selection step. The Gaussian numerators `z,R_j` share the positive rational
denominator `C`. The actual factor comparisons are
`B² normSq(z-R_j) ≤ A² C²`, including `A=0`.

The premise bounds the squared norm of the actual Horner evaluation of the
actual runtime root-product coefficient constructor. Its identification
with the product searched below is proved, rather than assumed. Deriving
this evaluation bound from coefficient discrepancies is a separate step.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianProductNorm

open_ipra
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (re im normSq)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra (sub equal equal_of_values re_sub im_sub)
open LeanProofs.IPRA.Analysis.GaussianRootProduct (coefficients evaluate normFactors)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (R z C : PTm n) : PTm n := pairT (pairT R z) C
def numeratorBody : PTm 2 := inst2 GaussianRootProduct.normBody (var 0) (fstT (var 1))
def denominatorBody : PTm 2 := sndT (var 1)*sndT (var 1)

ipra_subst data

theorem numerator_lift (j x : PTm n) : Γ ⊢[PRAAx]
    inst2 numeratorBody j x ≐ inst2 GaussianRootProduct.normBody j (fstT x) := by
  change Γ ⊢[PRAAx] Syn.subst ![j,x] (inst2 GaussianRootProduct.normBody (var 0) (fstT (var 1))) ≐ _
  simp only [subst_inst2,Syn.subst_var,subst_fstT,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact .eqRefl _

theorem numerator_at (R z C j : PTm n) : Γ ⊢[PRAAx]
    inst2 numeratorBody j (data R z C) ≐ normSq (sub z (entry R j)) :=
  (numerator_lift j _).eqTrans ((congrInst2 GaussianRootProduct.normBody (.eqRefl _)
    (fst_pair _ _)).eqTrans (GaussianRootProduct.normBody_at R z j))

theorem denominator_at (R z C j : PTm n) : Γ ⊢[PRAAx]
    inst2 denominatorBody j (data R z C) ≐ C*C := by
  simp only [denominatorBody,inst2,PTm.subst_mul,subst_sndT,Syn.subst_var,Matrix.cons_val_one]
  exact congrMul (snd_pair _ _) (snd_pair _ _)

theorem numerator_product (R z C N : PTm n) : Γ ⊢[PRAAx]
    RationalProductWitness.product numeratorBody N (data R z C) ≐ normFactors R z N := by
  apply prod_congr_bounded
  refine .allI (.impI ?_)
  have e := numerator_lift (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift)
    (var 0) (data (Syn.shift R) (Syn.shift z) (Syn.shift C))
  simpa only [Syn.shift,subst_data,subst_pairT] using e.eqTrans
    (congrInst2 GaussianRootProduct.normBody (.eqRefl _) (fst_pair _ _))

theorem denominator_product (R z C N : PTm n) : Γ ⊢[PRAAx]
    RationalProductWitness.product denominatorBody N (data R z C) ≐ pw (C*C) N := by
  apply prod_const_of
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_data,PTm.subst_mul] using
    denominator_at (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift)
      (Syn.shift R) (Syn.shift z) (Syn.shift C) (var 0)

/-- The searched numerator product is the actual constructed polynomial's
evaluation norm, with no factorization identity among the premises. -/
theorem evaluation_product (R z C N : PTm n) : Γ ⊢[PRAAx]
    normSq (evaluate (coefficients R N) z) ≐
      RationalProductWitness.product numeratorBody N (data R z C) :=
  (GaussianRootProduct.evaluation_norm_product R z N).eqTrans (numerator_product R z C N).eqSymm

def evaluationBound (R z N A B C : PTm n) : Fm PTm n :=
  le (pw (B*B) N*normSq (evaluate (coefficients R N) z))
    (pw (A*A) N*pw (C*C) N)

ipra_subst evaluationBound

theorem product_bound (R z N A B C : PTm n)
    (h : Γ ⊢[PRAAx] evaluationBound R z N A B C) : Γ ⊢[PRAAx]
    le (RationalProductWitness.scaledProduct numeratorBody N (B*B) (data R z C))
      (RationalProductWitness.scaledProduct denominatorBody N (A*A) (data R z C)) :=
  le_congr (congrMul (.eqRefl _) (evaluation_product R z C N))
    (congrMul (.eqRefl _) (denominator_product R z C N).eqSymm) h

def selected (R z N A B C : PTm n) : PTm n :=
  RationalProductWitness.selected numeratorBody denominatorBody N (A*A) (B*B) (data R z C)

ipra_subst selected

theorem selected_range (R z N A B C : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] evaluationBound R z N A B C) : Γ ⊢[PRAAx] lt (selected R z N A B C) N :=
  RationalProductWitness.selected_found _ _ _ _ _ _ hN (product_bound R z N A B C h)

theorem selected_squared_distance (R z N A B C : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] evaluationBound R z N A B C) : Γ ⊢[PRAAx]
    le ((B*B)*normSq (sub z (entry R (selected R z N A B C)))) ((A*A)*(C*C)) :=
  le_congr (congrMul (.eqRefl _) (numerator_at _ _ _ _))
    (congrMul (.eqRefl _) (denominator_at _ _ _ _))
    (RationalProductWitness.selected_comparison _ _ _ _ _ _ hN (product_bound R z N A B C h))

theorem selected_least (R z N A B C j : PTm n) (hj : Γ ⊢[PRAAx] lt j N)
    (hsmall : Γ ⊢[PRAAx] le ((B*B)*normSq (sub z (entry R j))) ((A*A)*(C*C))) :
    Γ ⊢[PRAAx] le (selected R z N A B C) j :=
  RationalProductWitness.selected_least _ _ _ _ _ _ _ hj
    (le_congr (congrMul (.eqRefl _) (numerator_at _ _ _ _).eqSymm)
      (congrMul (.eqRefl _) (denominator_at _ _ _ _).eqSymm) hsmall)

theorem selected_in_list (R z N A B C : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hR : Γ ⊢[PRAAx] le N (length R)) (h : Γ ⊢[PRAAx] evaluationBound R z N A B C) :
    Γ ⊢[PRAAx] lt (selected R z N A B C) (length R) :=
  lt_of_lt_of_le (selected_range R z N A B C hN h) hR

theorem square_positive (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx] le one (D*D) :=
  le_congr (one_mul one) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono hD hD)

theorem denominator_guard (R z C N : PTm n) (hC : Γ ⊢[PRAAx] le one C) :
    Γ ⊢[PRAAx] RationalProductWitness.denominatorGuard denominatorBody N (data R z C) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have positive : Δ ⊢[PRAAx] le one (Syn.shift C*Syn.shift C) :=
    square_positive _ (by simpa only [Δ,Fm.shift,subst_le,Syn.shift,ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ] using hC.shift.wk)
  simpa only [Δ,Syn.shift,subst_data] using le_congr (.eqRefl _) (denominator_at
    (Γ := Δ) (Syn.shift R) (Syn.shift z) (Syn.shift C) (var 0)).eqSymm positive

/-- Positivity is derived for the actual constant-denominator factor list. -/
theorem rational_witness (R z N A B C : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hB : Γ ⊢[PRAAx] le one B) (hC : Γ ⊢[PRAAx] le one C)
    (h : Γ ⊢[PRAAx] evaluationBound R z N A B C) : Γ ⊢[PRAAx]
    RationalProductWitness.correct numeratorBody denominatorBody N (A*A) (B*B) (data R z C) :=
  RationalProductWitness.rational_product_witness _ _ _ _ _ _ hN (square_positive B hB)
    (denominator_guard R z C N hC) (product_bound R z N A B C h)

/-! Zero tolerance gives equality of actual Gaussian values. -/

private theorem value_zero_of_abs (u : ZT n)
    (h : Γ ⊢[PRAAx] Probability.Variance.ad u.pos u.neg ≐ zero) : ZT.toZ Γ u = 0 := by
  have left : Γ ⊢[PRAAx] monus u.pos u.neg ≐ zero := le_antisymm
    (le_congr (.eqRefl _) h (le_add_right _ _)) (zero_le _)
  have right : Γ ⊢[PRAAx] monus u.neg u.pos ≐ zero := le_antisymm
    (le_congr (.eqRefl _) h (le_add_left _ _)) (zero_le _)
  simp only [ZT.toZ]
  rw [natEq (le_antisymm left right)]
  ring

private theorem square_zero {a : PTm n} (h : Γ ⊢[PRAAx] a*a ≐ zero) : Γ ⊢[PRAAx] a ≐ zero :=
  .orE (zero_or_zero_of_mul h) Prf.hyp0 Prf.hyp0

theorem norm_zero_values (c : PTm n) (h : Γ ⊢[PRAAx] normSq c ≐ zero) :
    ZT.toZ Γ (re c) = 0 ∧ ZT.toZ Γ (im c) = 0 := by
  exact ⟨value_zero_of_abs (re c) (square_zero (add_eq_zero_left h)),
    value_zero_of_abs (im c) (square_zero (add_eq_zero_right h))⟩

theorem equal_of_difference_norm_zero (z r : PTm n)
    (h : Γ ⊢[PRAAx] normSq (sub z r) ≐ zero) : Γ ⊢[PRAAx] equal z r := by
  have v := norm_zero_values _ h
  simp only [re_sub,im_sub] at v
  apply equal_of_values
  · linear_combination v.1
  · linear_combination v.2

theorem zero_threshold_norm (R z N B C : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] evaluationBound R z N zero B C) :
    Γ ⊢[PRAAx] normSq (sub z (entry R (selected R z N zero B C))) ≐ zero := by
  have small := selected_squared_distance R z N zero B C hN h
  have zp : Γ ⊢[PRAAx] (B*B)*normSq (sub z (entry R (selected R z N zero B C))) ≐ zero :=
    le_antisymm (le_congr (.eqRefl _) ((congrMul (zero_mul zero) (.eqRefl _)).eqTrans
      (zero_mul _)) small) (zero_le _)
  have positive : Γ ⊢[PRAAx] B*B ≐ succ (monus (B*B) one) :=
    (eq_add_of_le (square_positive B hB)).eqTrans (by ipra_ring)
  exact eq_zero_of_succ_mul ((congrMul positive (.eqRefl _)).eqSymm.eqTrans zp)

theorem zero_threshold_root (R z N B C : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] evaluationBound R z N zero B C) :
    Γ ⊢[PRAAx] equal z (entry R (selected R z N zero B C)) :=
  equal_of_difference_norm_zero _ _ (zero_threshold_norm R z N B C hN hB h)

/-! The actual primitive recursive output stores index, original root, and
the squared rational distance numerator/denominator. -/

def output (R z N A B C : PTm n) : PTm n :=
  pairT (selected R z N A B C)
    (pairT (entry R (selected R z N A B C))
      (pairT (normSq (sub z (entry R (selected R z N A B C)))) (C*C)))
def selectedF : PR 6 := PTm.toPR (selected (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (R z N A B C : PTm n) : PTm n := ConciseIPRA.PTm.app outputF ![R,z,N,A,B,C]

ipra_subst output
ipra_subst run

theorem selected_at (R z N A B C : PTm n) : Γ ⊢[PRAAx]
    ConciseIPRA.PTm.app selectedF ![R,z,N,A,B,C] ≐ selected R z N A B C := by
  simpa [selectedF] using toPR_eq (Γ := Γ)
    (selected (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![R,z,N,A,B,C]

theorem output_at (R z N A B C : PTm n) : Γ ⊢[PRAAx] run R z N A B C ≐ output R z N A B C := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![R,z,N,A,B,C]

theorem output_index (R z N A B C : PTm n) : Γ ⊢[PRAAx]
    fstT (run R z N A B C) ≐ selected R z N A B C :=
  (output_at R z N A B C).fstE
theorem output_point (R z N A B C : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run R z N A B C)) ≐ entry R (selected R z N A B C) :=
  (output_at R z N A B C).sndE.fstE
theorem output_point_index (R z N A B C : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run R z N A B C)) ≐ entry R (fstT (run R z N A B C)) :=
  (output_point R z N A B C).eqTrans (entry_congr (.eqRefl _) (output_index R z N A B C).eqSymm)
theorem output_numerator (R z N A B C : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run R z N A B C))) ≐ normSq (sub z (entry R (selected R z N A B C))) :=
  (congrFst ((congrSnd (output_at R z N A B C).sndE).eqTrans
    (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem output_denominator (R z N A B C : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run R z N A B C))) ≐ C*C :=
  (congrSnd ((congrSnd (output_at R z N A B C).sndE).eqTrans
    (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem output_distance (R z N A B C : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run R z N A B C))) ≐ normSq (sub z (fstT (sndT (run R z N A B C)))) := by
  have e := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (normSq (sub (var 0) (var 1)) : PTm 2)
    (σ := ![z,entry R (selected R z N A B C)]) (σ' := ![z,fstT (sndT (run R z N A B C))])
    (fun i => by fin_cases i; exact .eqRefl _; exact (output_point R z N A B C).eqSymm)
  exact (output_numerator R z N A B C).eqTrans (by simpa using e)

def programCorrect (R z N A B C : PTm n) : Fm PTm n :=
  lt (fstT (run R z N A B C)) N ⋏
    (fstT (sndT (run R z N A B C)) ≐ entry R (fstT (run R z N A B C)) ⋏
      (fstT (sndT (sndT (run R z N A B C))) ≐ normSq (sub z (fstT (sndT (run R z N A B C)))) ⋏
        (le ((B*B)*fstT (sndT (sndT (run R z N A B C))))
          ((A*A)*sndT (sndT (sndT (run R z N A B C)))) ⋏
            le one (sndT (sndT (sndT (run R z N A B C)))))))

theorem program_correct (R z N A B C : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hC : Γ ⊢[PRAAx] le one C) (h : Γ ⊢[PRAAx] evaluationBound R z N A B C) :
    Γ ⊢[PRAAx] programCorrect R z N A B C :=
  .andI (lt_congr (output_index R z N A B C).eqSymm (.eqRefl _) (selected_range R z N A B C hN h))
    (.andI (output_point_index R z N A B C) (.andI (output_distance R z N A B C)
      (.andI (le_congr (congrMul (.eqRefl _) (output_numerator R z N A B C).eqSymm)
        (congrMul (.eqRefl _) (output_denominator R z N A B C).eqSymm)
        (selected_squared_distance R z N A B C hN h))
          (le_congr (.eqRefl _) (output_denominator R z N A B C).eqSymm (square_positive C hC)))))

def selectionCorrect (R z N A B C : PTm n) : Fm PTm n :=
  lt (selected R z N A B C) (length R) ⋏
    (le ((B*B)*normSq (sub z (entry R (selected R z N A B C)))) ((A*A)*(C*C)) ⋏
      (le one (B*B) ⋏ (le one (C*C) ⋏
        RationalProductWitness.leastFormula numeratorBody denominatorBody N (A*A) (B*B) (data R z C))))

theorem selection_correct (R z N A B C : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hR : Γ ⊢[PRAAx] le N (length R)) (hB : Γ ⊢[PRAAx] le one B)
    (hC : Γ ⊢[PRAAx] le one C) (h : Γ ⊢[PRAAx] evaluationBound R z N A B C) :
    Γ ⊢[PRAAx] selectionCorrect R z N A B C :=
  .andI (selected_in_list R z N A B C hN hR h)
    (.andI (selected_squared_distance R z N A B C hN h)
      (.andI (square_positive B hB) (.andI (square_positive C hC)
        (RationalProductWitness.least_formula _ _ _ _ _ _))))

/-! Closed ordinary-iPRA statements: degree, list, point, threshold and
common denominator are all numerical quantified variables. -/

theorem evaluation_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (normSq (evaluate (coefficients (var 0) (var 3)) (var 1)) ≐
      RationalProductWitness.product numeratorBody (var 3) (data (var 0) (var 1) (var 2))) :=
  closeUniv 4 (evaluation_product _ _ _ _)

theorem denominator_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (RationalProductWitness.product denominatorBody (var 3) (data (var 0) (var 1) (var 2)) ≐
      pw (var 2*var 2) (var 3)) :=
  closeUniv 4 (denominator_product _ _ _ _)

theorem factor_selection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 2) ⟶ le (var 2) (length (var 0)) ⟶ le one (var 4) ⟶ le one (var 5) ⟶
      evaluationBound (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
        selectionCorrect (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI
    (selection_correct _ _ _ _ _ _ hyp2.wk.wk hyp2.wk hyp2 Prf.hyp1 Prf.hyp0))))))

/-- Full-list specialization requires just actual nonemptiness. -/
theorem list_factor_selection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (length (var 0)) ⟶ le one (var 3) ⟶ le one (var 4) ⟶
      evaluationBound (var 0) (var 1) (length (var 0)) (var 2) (var 3) (var 4) ⟶
        selectionCorrect (var 0) (var 1) (length (var 0)) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI
    (selection_correct _ _ _ _ _ _ hyp2.wk (le_refl _) hyp2 Prf.hyp1 Prf.hyp0)))))

theorem zero_threshold_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ le one (var 3) ⟶
      evaluationBound (var 0) (var 1) (var 2) zero (var 3) (var 4) ⟶
        equal (var 1) (entry (var 0) (selected (var 0) (var 1) (var 2) zero (var 3) (var 4)))) :=
  closeUniv 5 (.impI (.impI (.impI (zero_threshold_root _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem factor_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 2) ⟶ le one (var 5) ⟶
      evaluationBound (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
        programCorrect (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (program_correct _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem factor_program_metadata_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐
      output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (output_at _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianProductNorm
