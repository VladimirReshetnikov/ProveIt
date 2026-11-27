import IPRADerivations.Analysis.Polynomials.Elimination.Vandermonde.GaussianRationalFiberVandermonde
import IPRADerivations.Analysis.Polynomials.RootFinding.Reconstruction.RootProducts.GaussianReconstructionRoots

/-!
# Actual numerical Lagrange cardinal polynomials

A numerical skip map deletes exactly one original position. Actual
reconstruction supplies the product polynomial. Its denominator is proved
nonzero by a genuine guarded QF induction on the original reverse factor
fold, using the derived nonzero differences of the original field-distinct
list. Actual reciprocal scaling then gives cardinal evaluations and an
ascending coefficient-dot formula. No inverse or determinant law is an
input or a conclusion of this construction.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalLagrangeCardinals

open_ipra
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qmul canonical evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr qsub_congr canonicalCoefficients)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub qsub_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power reciprocal normNumerator reciprocal_identity)
open LeanProofs.IPRA.Analysis.GaussianRationalReconstruction (reconstruct factors factors_succ factors_zero reconstruction_evaluation)
open LeanProofs.IPRA.Analysis.GaussianRationalCoefficientScaling (scaled scaled_length scaled_lookup scaled_entry_canonical evaluation_linearity)
open LeanProofs.IPRA.Analysis.GaussianRationalMonicReduction (evaluate_congr)
export GaussianPolynomialDeterminantTerms (scaled_canonical)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def skip (s i : PTm n) : PTm n := RationalArithmetic.select (Signum.sg (monus s i)) (succ i) i
def slot (s r : PTm n) : PTm n := RationalArithmetic.select (Signum.sg (monus s r)) (pred r) r
def data (R s : PTm n) : PTm n := pairT R s
def deleteBody : PTm 2 := entry (fstT (var 1)) (skip (sndT (var 1)) (var 0))
def deleted (R s : PTm n) : PTm n := sequence deleteBody (pred (length R)) (data R s)

ipra_subst skip
ipra_subst slot
ipra_subst data
ipra_subst deleted

theorem skip_congr {s s' i i' : PTm n} (hs : Γ ⊢[PRAAx] s ≐ s') (hi : Γ ⊢[PRAAx] i ≐ i') : Γ ⊢[PRAAx]
    skip s i ≐ skip s' i' := by
  ipra_congr (skip (var 0) (var 1) : PTm 2) with [hs, hi]
theorem skip_before (s i : PTm n) (hi : Γ ⊢[PRAAx] lt i s) : Γ ⊢[PRAAx] skip s i ≐ i :=
  RationalArithmetic.select_one _ _ _ (AnalyticNumberTheory.Totatives.sg_lt hi)
theorem skip_after (s i : PTm n) (hi : Γ ⊢[PRAAx] le s i) : Γ ⊢[PRAAx] skip s i ≐ succ i :=
  RationalArithmetic.select_zero _ _ _ (AnalyticNumberTheory.Totatives.sg_le hi)
theorem slot_before (s r : PTm n) (hr : Γ ⊢[PRAAx] lt r s) : Γ ⊢[PRAAx] slot s r ≐ r :=
  RationalArithmetic.select_one _ _ _ (AnalyticNumberTheory.Totatives.sg_lt hr)
theorem slot_after (s r : PTm n) (hr : Γ ⊢[PRAAx] le s r) : Γ ⊢[PRAAx] slot s r ≐ pred r :=
  RationalArithmetic.select_zero _ _ _ (AnalyticNumberTheory.Totatives.sg_le hr)

theorem length_positive (t s : PTm n) (hs : Γ ⊢[PRAAx] lt s t) : Γ ⊢[PRAAx] t ≐ succ (pred t) :=
  RationalIntegerNormalization.positive_form (le_trans (le_of_eq_add (d := s) (by ipra_ring)) hs)
theorem index_below_pred (t s : PTm n) (hs : Γ ⊢[PRAAx] lt s t) : Γ ⊢[PRAAx] le s (pred t) :=
  (succ_monus_succ s (pred t)).eqSymm.eqTrans (lt_congr (.eqRefl _) (length_positive t s hs) hs)
theorem pred_le_length (t s : PTm n) (hs : Γ ⊢[PRAAx] lt s t) : Γ ⊢[PRAAx] le (pred t) t :=
  le_congr (.eqRefl _) (length_positive t s hs).eqSymm (le_succ_self _)
theorem natural_neq_of_lt (a b : PTm n) (h : Γ ⊢[PRAAx] lt a b) : Γ ⊢[PRAAx] neg (a ≐ b) :=
  .impI (lt_irrefl a Fm.bot (lt_congr (.eqRefl _) Prf.hyp0.eqSymm h.wk))

theorem skip_bound (R s i : PTm n) (hs : Γ ⊢[PRAAx] lt s (length R))
    (hi : Γ ⊢[PRAAx] lt i (pred (length R))) : Γ ⊢[PRAAx] lt (skip s i) (length R) := by
  refine .orE (lt_or_le i s) ?_ ?_
  · exact lt_congr (skip_before s i Prf.hyp0).eqSymm (.eqRefl _)
      (le_trans hi.wk (pred_le_length _ _ hs.wk))
  · have step : le s i :: Γ ⊢[PRAAx] lt (succ i) (length R) :=
      lt_congr (.eqRefl _) (length_positive _ _ hs.wk).eqSymm
        ((succ_monus_succ (succ i) (pred (length R))).eqTrans hi.wk)
    exact lt_congr (skip_after s i Prf.hyp0).eqSymm (.eqRefl _) step
theorem skip_avoids (s i : PTm n) : Γ ⊢[PRAAx] neg (skip s i ≐ s) := by
  refine .orE (lt_or_le i s) ?_ ?_
  · refine .impI ?_
    have e : (skip s i ≐ s) :: lt i s :: Γ ⊢[PRAAx] i ≐ s := (skip_before s i Prf.hyp1).eqSymm.eqTrans Prf.hyp0
    exact .impE (natural_neq_of_lt i s Prf.hyp1) e
  · refine .impI ?_
    have e : (skip s i ≐ s) :: le s i :: Γ ⊢[PRAAx] succ i ≐ s := (skip_after s i Prf.hyp1).eqSymm.eqTrans Prf.hyp0
    exact not_succ_le_self i Fm.bot (le_congr e.eqSymm (.eqRefl _) Prf.hyp1)

theorem delete_body_at (R s i : PTm n) : Γ ⊢[PRAAx]
    inst2 deleteBody i (data R s) ≐ entry R (skip s i) := by
  simp only [deleteBody,inst2,subst_entry,subst_skip,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact entry_congr (fst_pair _ _) (skip_congr (snd_pair _ _) (.eqRefl _))
theorem deleted_length (R s : PTm n) : Γ ⊢[PRAAx] length (deleted R s) ≐ pred (length R) := sequence_length _ _ _
theorem deleted_lookup (R s i : PTm n) (hi : Γ ⊢[PRAAx] lt i (pred (length R))) : Γ ⊢[PRAAx]
    entry (deleted R s) i ≐ entry R (skip s i) :=
  (sequence_decode deleteBody hi).eqTrans (delete_body_at _ _ _)

theorem slot_coverage (R s r : PTm n) (hs : Γ ⊢[PRAAx] lt s (length R))
    (hr : Γ ⊢[PRAAx] lt r (length R)) (hne : Γ ⊢[PRAAx] neg (r ≐ s)) : Γ ⊢[PRAAx]
    lt (slot s r) (pred (length R)) ⋏ (skip s (slot s r) ≐ r) := by
  refine .orE (lt_or_le r s) ?_ ?_
  · have e := slot_before s r (Prf.hyp0 (Ax := PRAAx) (Γ := Γ))
    exact .andI (lt_congr e.eqSymm (.eqRefl _) (le_trans Prf.hyp0 (index_below_pred _ _ hs.wk)))
      ((skip_congr (.eqRefl _) e).eqTrans (skip_before _ _ Prf.hyp0))
  · refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_
    · have e : lt s r :: le s r :: Γ ⊢[PRAAx] slot s r ≐ pred r := slot_after s r Prf.hyp1
      have rp : lt s r :: le s r :: Γ ⊢[PRAAx] r ≐ succ (pred r) := length_positive r s Prf.hyp0
      have tp : lt s r :: le s r :: Γ ⊢[PRAAx] length R ≐ succ (pred (length R)) := length_positive (length R) s hs.wk.wk
      have rr : lt s r :: le s r :: Γ ⊢[PRAAx] lt (pred r) (pred (length R)) :=
        (succ_monus_succ (succ (pred r)) (pred (length R))).eqSymm.eqTrans (lt_congr rp tp hr.wk.wk)
      exact .andI (lt_congr e.eqSymm (.eqRefl _) rr)
        ((skip_congr (.eqRefl _) e).eqTrans ((skip_after s (pred r) (index_below_pred r s Prf.hyp0)).eqTrans rp.eqSymm))
    · exact .botE _ (.impE hne.wk.wk Prf.hyp0.eqSymm)
theorem deleted_covers (R s r : PTm n) (hs : Γ ⊢[PRAAx] lt s (length R))
    (hr : Γ ⊢[PRAAx] lt r (length R)) (hne : Γ ⊢[PRAAx] neg (r ≐ s)) : Γ ⊢[PRAAx]
    lt (slot s r) (pred (length R)) ⋏ (entry (deleted R s) (slot s r) ≐ entry R r) := by
  have h := slot_coverage R s r hs hr hne
  exact .andI (.andE₁ h) ((deleted_lookup _ _ _ (.andE₁ h)).eqTrans (entry_congr (.eqRefl _) (.andE₂ h)))


def productPolynomial (R s : PTm n) : PTm n := reconstruct (deleted R s) (pred (length R)) (pred (length R))
def denominator (R s : PTm n) : PTm n := evaluate (productPolynomial R s) (entry R s)
def cardinal (R s : PTm n) : PTm n := scaled (productPolynomial R s) (reciprocal (denominator R s))
ipra_subst productPolynomial
ipra_subst denominator
ipra_subst cardinal

theorem difference_nonzero (R s j : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hs : Γ ⊢[PRAAx] lt s (length R)) (hj : Γ ⊢[PRAAx] lt j (length R))
    (hne : Γ ⊢[PRAAx] neg (j ≐ s)) : Γ ⊢[PRAAx] neg (qsub (entry R s) (entry R j) ≐ qzero) := by
  refine .orE (lt_or_le j s) ?_ ?_
  · exact GaussianRationalFiniteRoots.distinct_at R j s h.wk hj.wk hs.wk Prf.hyp0
  · refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_
    · refine .impI ?_
      have eqv := GaussianRationalValueEquality.equal_values_of_difference_zero (entry R s) (entry R j)
        (Prf.hyp0 (Ax := PRAAx) (Γ := lt s j :: le s j :: Γ))
      have reverse := GaussianRationalValueEquality.difference_zero_of_equal_values _ _
        (GaussianRationalValueEquality.value_equal_symm _ _ eqv)
      exact .impE (GaussianRationalFiniteRoots.distinct_at R s j h.wk.wk.wk hs.wk.wk.wk hj.wk.wk.wk Prf.hyp1) reverse
    · exact .botE _ (.impE hne.wk.wk Prf.hyp0.eqSymm)
theorem deleted_factor_nonzero (R s i : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hs : Γ ⊢[PRAAx] lt s (length R)) (hi : Γ ⊢[PRAAx] lt i (pred (length R))) : Γ ⊢[PRAAx]
    neg (qsub (entry R s) (entry (deleted R s) i) ≐ qzero) := by
  have no : Γ ⊢[PRAAx] neg (qsub (entry R s) (entry R (skip s i)) ≐ qzero) :=
    difference_nonzero R s (skip s i) h hs (skip_bound R s i hs hi) (skip_avoids s i)
  exact .impI (.impE no.wk ((qsub_congr (.eqRefl _) (deleted_lookup R s i hi.wk)).eqSymm.eqTrans Prf.hyp0))
alias reverse_position_bound := Common.monus_succ_lt
theorem factors_canonical (S N y k : PTm n) : Γ ⊢[PRAAx] canonical (factors S N y k) :=
  GaussianRationalHorner.canonical_congr (reconstruction_evaluation S N y k).eqSymm (GaussianRationalHorner.horner_canonical _ _ _)
theorem factors_nonzero_step (R s k : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hs : Γ ⊢[PRAAx] lt s (length R)) (hk : Γ ⊢[PRAAx] lt k (pred (length R)))
    (ih : Γ ⊢[PRAAx] neg (factors (deleted R s) (pred (length R)) (entry R s) k ≐ qzero)) : Γ ⊢[PRAAx]
    neg (factors (deleted R s) (pred (length R)) (entry R s) (succ k) ≐ qzero) := by
  refine .impI ?_
  have zero : (factors (deleted R s) (pred (length R)) (entry R s) (succ k) ≐ qzero) :: Γ ⊢[PRAAx]
      qmul (qsub (entry R s) (entry (deleted R s) (monus (pred (length R)) (succ k))))
        (factors (deleted R s) (pred (length R)) (entry R s) k) ≐ qzero :=
    (factors_succ _ _ _ _).eqSymm.eqTrans Prf.hyp0
  exact .impE ih.wk (GaussianRationalFiniteRoots.product_zero_reflect _ _ (qsub_canonical _ _) (factors_canonical _ _ _ _)
    (deleted_factor_nonzero _ _ _ h.wk hs.wk (reverse_position_bound _ _ hk.wk)) zero)

def nonzeroLaw (R s k : PTm n) : Fm PTm n := le k (pred (length R)) ⟶
  neg (factors (deleted R s) (pred (length R)) (entry R s) k ≐ qzero)
ipra_subst nonzeroLaw
theorem factors_nonzero (R s k : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hs : Γ ⊢[PRAAx] lt s (length R)) (hk : Γ ⊢[PRAAx] le k (pred (length R))) : Γ ⊢[PRAAx]
    neg (factors (deleted R s) (pred (length R)) (entry R s) k ≐ qzero) := by
  have hsh : Γ.map Fm.shift ⊢[PRAAx] GaussianRationalFiniteRoots.distinct (Syn.shift R) := by
    simpa only [Fm.shift,GaussianRationalFiniteRoots.subst_distinct,Syn.shift] using h.shift
  have ssh : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift s) (length (Syn.shift R)) := by
    simpa only [Fm.shift,subst_lt,subst_length,Syn.shift] using hs.shift
  have all : Γ ⊢[PRAAx] .all (nonzeroLaw (Syn.shift R) (Syn.shift s) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,⟨trivial,trivial⟩⟩) [subst_nonzeroLaw]
    · exact .impI (.impI (.impE GaussianRationalCurveFibers.gaussian_one_nonzero
        ((factors_zero _ _ _).eqSymm.eqTrans Prf.hyp0)))
    · refine .impI ?_
      exact factors_nonzero_step _ _ _ hsh.wk.wk ssh.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have law : Γ ⊢[PRAAx] nonzeroLaw R s k := by
    simpa only [subst_nonzeroLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE law hk

theorem product_length (R s : PTm n) (hs : Γ ⊢[PRAAx] lt s (length R)) : Γ ⊢[PRAAx]
    length (productPolynomial R s) ≐ length R :=
  (GaussianRationalReconstruction.reconstruct_length _ _ _).eqTrans (length_positive _ _ hs).eqSymm
theorem product_canonical (R s : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (productPolynomial R s) :=
  GaussianRationalReconstruction.reconstruct_canonical _ _ _
theorem product_monic (R s : PTm n) : Γ ⊢[PRAAx] entry (productPolynomial R s) zero ≐ qone :=
  GaussianRationalReconstruction.reconstruct_monic _ _ _
theorem denominator_canonical (R s : PTm n) : Γ ⊢[PRAAx] canonical (denominator R s) := GaussianRationalHorner.horner_canonical _ _ _
theorem denominator_nonzero (R s : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hs : Γ ⊢[PRAAx] lt s (length R)) : Γ ⊢[PRAAx] neg (denominator R s ≐ qzero) :=
  .impI (.impE (factors_nonzero R s (pred (length R)) h.wk hs.wk (le_refl _))
    ((reconstruction_evaluation _ _ _ _).eqSymm.eqTrans Prf.hyp0))
theorem denominator_norm_positive (R s : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hs : Γ ⊢[PRAAx] lt s (length R)) : Γ ⊢[PRAAx] le one (normNumerator (denominator R s)) :=
  GaussianRationalFiniteRoots.norm_positive_of_nonzero _ (denominator_canonical _ _) (denominator_nonzero _ _ h hs)
theorem inverse_valid (R s : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hs : Γ ⊢[PRAAx] lt s (length R)) : Γ ⊢[PRAAx]
    qmul (denominator R s) (reciprocal (denominator R s)) ≐ qone := reciprocal_identity _ (denominator_norm_positive _ _ h hs)


theorem cardinal_length (R s : PTm n) (hs : Γ ⊢[PRAAx] lt s (length R)) : Γ ⊢[PRAAx]
    length (cardinal R s) ≐ length R := (scaled_length _ _).eqTrans (product_length _ _ hs)
theorem cardinal_canonical (R s : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (cardinal R s) := scaled_canonical _ _
theorem cardinal_diagonal (R s : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hs : Γ ⊢[PRAAx] lt s (length R)) : Γ ⊢[PRAAx]
    evaluate (cardinal R s) (entry R s) ≐ qone :=
  (evaluation_linearity _ _ _).eqTrans ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (inverse_valid _ _ h hs))
theorem product_off_diagonal (R s r : PTm n) (hs : Γ ⊢[PRAAx] lt s (length R))
    (hr : Γ ⊢[PRAAx] lt r (length R)) (hne : Γ ⊢[PRAAx] neg (r ≐ s)) : Γ ⊢[PRAAx]
    evaluate (productPolynomial R s) (entry R r) ≐ qzero := by
  have cover := deleted_covers R s r hs hr hne
  exact (evaluate_congr (.eqRefl _) (Prf.andE₂ cover).eqSymm).eqTrans
    (GaussianReconstructionRoots.listed_root_zero (deleted R s) (pred (length R)) (slot s r) (.andE₁ cover))
theorem cardinal_off_diagonal (R s r : PTm n) (hs : Γ ⊢[PRAAx] lt s (length R))
    (hr : Γ ⊢[PRAAx] lt r (length R)) (hne : Γ ⊢[PRAAx] neg (r ≐ s)) : Γ ⊢[PRAAx]
    evaluate (cardinal R s) (entry R r) ≐ qzero :=
  (evaluation_linearity _ _ _).eqTrans ((qmul_congr (.eqRefl _) (product_off_diagonal _ _ _ hs hr hne)).eqTrans
    (GaussianRationalSyntheticDivision.qmul_zero_right _))
theorem delta_equal (r s : PTm n) (h : Γ ⊢[PRAAx] r ≐ s) : Γ ⊢[PRAAx]
    GaussianRationalFiberVandermonde.delta r s ≐ qone := RationalArithmetic.select_one _ _ _ (eqb_of_eq h)
theorem delta_unequal (r s : PTm n) (h : Γ ⊢[PRAAx] neg (r ≐ s)) : Γ ⊢[PRAAx]
    GaussianRationalFiberVandermonde.delta r s ≐ qzero := by
  refine .orE (Foundations.BoundedReflection.eqb_cases r s) ?_ ?_
  · exact RationalArithmetic.select_zero _ _ _ Prf.hyp0
  · exact .botE _ (.impE h.wk (Foundations.BoundedReflection.eq_of_eqb Prf.hyp0))
theorem cardinal_evaluation (R s r : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hs : Γ ⊢[PRAAx] lt s (length R)) (hr : Γ ⊢[PRAAx] lt r (length R)) : Γ ⊢[PRAAx]
    evaluate (cardinal R s) (entry R r) ≐ GaussianRationalFiberVandermonde.delta r s := by
  refine .orE (eq_or_ne r s) ?_ ?_
  · exact (evaluate_congr (.eqRefl _) (entry_congr (.eqRefl _) Prf.hyp0)).eqTrans
      ((cardinal_diagonal _ _ h.wk hs.wk).eqTrans (delta_equal _ _ Prf.hyp0).eqSymm)
  · exact (cardinal_off_diagonal _ _ _ hs.wk hr.wk Prf.hyp0).eqTrans (delta_unequal _ _ Prf.hyp0).eqSymm

/-- Stored polynomial coefficients descend; numerical power columns ascend. -/
def inverseCoefficient (R k s : PTm n) : PTm n := entry (cardinal R s) (monus (length R) (succ k))
def evaluationData (R s z : PTm n) : PTm n := pairT R (pairT s z)
def coefficientTerm (R s z k : PTm n) : PTm n := qmul (power z k) (inverseCoefficient R k s)
def evaluationBody : PTm 2 := coefficientTerm (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def coefficientEvaluation (R s z : PTm n) : PTm n := GaussianRationalFiniteSum.sum evaluationBody (length R) (evaluationData R s z)
def dot (R r s : PTm n) : PTm n := coefficientEvaluation R s (entry R r)
ipra_subst inverseCoefficient
ipra_subst evaluationData
ipra_subst coefficientTerm
ipra_subst coefficientEvaluation
ipra_subst dot
theorem inverse_coefficient_congr {R S k j s t : PTm n} (hR : Γ ⊢[PRAAx] R ≐ S)
    (hk : Γ ⊢[PRAAx] k ≐ j) (hs : Γ ⊢[PRAAx] s ≐ t) : Γ ⊢[PRAAx]
    inverseCoefficient R k s ≐ inverseCoefficient S j t := by
  ipra_congr (inverseCoefficient (var 0) (var 1) (var 2) : PTm 3) with [hR, hk, hs]
theorem evaluation_body_at (R s z k : PTm n) : Γ ⊢[PRAAx]
    inst2 evaluationBody k (evaluationData R s z) ≐ coefficientTerm R s z k := by
  simp only [evaluationBody,inst2,subst_coefficientTerm,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have tail := snd_pair (Γ := Γ) R (pairT s z)
  exact qmul_congr (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl _) tail.sndE)
    (inverse_coefficient_congr (fst_pair _ _) (.eqRefl _) tail.fstE)
theorem coefficient_reversal (R s k : PTm n) (hs : Γ ⊢[PRAAx] lt s (length R)) : Γ ⊢[PRAAx]
    monus (length R) (succ k) ≐ monus (pred (length R)) k :=
  (congrMonus (length_positive _ _ hs) (.eqRefl _)).eqTrans (succ_monus_succ _ _)

theorem coefficient_evaluation (R s z : PTm n) (hs : Γ ⊢[PRAAx] lt s (length R)) : Γ ⊢[PRAAx]
    coefficientEvaluation R s z ≐ evaluate (cardinal R s) z := by
  have ssh : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift s) (length (Syn.shift R)) := by
    simpa only [Fm.shift,subst_lt,subst_length,Syn.shift] using hs.shift
  have eqTerms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual evaluationBody GaussianRationalPowerExpansion.termBody (length R)
      (evaluationData R s z) (GaussianRationalPowerExpansion.data (cardinal R s) (pred (length R)) z) := by
    refine .allI (.impI ?_)
    have e : lt (var 0) (Syn.shift (length R)) :: Γ.map Fm.shift ⊢[PRAAx]
        inst2 evaluationBody (var 0) (evaluationData (Syn.shift R) (Syn.shift s) (Syn.shift z)) ≐
        inst2 GaussianRationalPowerExpansion.termBody (var 0)
          (GaussianRationalPowerExpansion.data (cardinal (Syn.shift R) (Syn.shift s)) (pred (length (Syn.shift R))) (Syn.shift z)) :=
      (evaluation_body_at (Syn.shift R) (Syn.shift s) (Syn.shift z) (var 0)).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
        ((qmul_congr (entry_congr (.eqRefl _) (coefficient_reversal _ _ _ ssh.wk)) (.eqRefl _)).eqTrans
          (GaussianRationalPowerExpansion.term_body_at (cardinal (Syn.shift R) (Syn.shift s)) (pred (length (Syn.shift R))) (Syn.shift z) (var 0)).eqSymm))
    simpa only [Syn.shift,subst_evaluationData,GaussianRationalPowerExpansion.subst_data,subst_cardinal,subst_length,PTm.subst_pred] using e
  have bodySum := GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ eqTerms
  have count := GaussianRationalFiniteSum.sum_index_congr GaussianRationalPowerExpansion.termBody (length_positive _ _ hs) (.eqRefl (GaussianRationalPowerExpansion.data (cardinal R s) (pred (length R)) z))
  have listSum : Γ ⊢[PRAAx] GaussianRationalFiniteSum.sum GaussianRationalPowerExpansion.termBody (succ (pred (length R)))
      (GaussianRationalPowerExpansion.data (cardinal R s) (pred (length R)) z) ≐
      evaluate (GaussianRationalPowerExpansion.terms (cardinal R s) (pred (length R)) z) qone :=
    congrAp3 GaussianRationalHorner.hornerF (GaussianRationalPowerExpansion.terms_length _ _ _).eqSymm (.eqRefl _) (.eqRefl _)
  exact bodySum.eqTrans (count.eqTrans (listSum.eqTrans
    (GaussianRationalPowerExpansion.power_expansion (cardinal R s) (pred (length R)) z
      ((cardinal_length _ _ hs).eqTrans (length_positive _ _ hs))).eqSymm))
theorem cardinal_dot (R r s : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hr : Γ ⊢[PRAAx] lt r (length R)) (hs : Γ ⊢[PRAAx] lt s (length R)) : Γ ⊢[PRAAx]
    dot R r s ≐ GaussianRationalFiberVandermonde.delta r s :=
  (coefficient_evaluation _ _ _ hs).eqTrans (cardinal_evaluation _ _ _ h hs hr)


def cardinalValues (R s : PTm n) : Fm PTm n := .all (lt (var 0) (length (Syn.shift R)) ⟶
  evaluate (cardinal (Syn.shift R) (Syn.shift s)) (entry (Syn.shift R) (var 0)) ≐
    GaussianRationalFiberVandermonde.delta (var 0) (Syn.shift s))
ipra_subst cardinalValues [Syn.subst_shift, Syn.shift_subst]
theorem cardinal_values (R s : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hs : Γ ⊢[PRAAx] lt s (length R)) : Γ ⊢[PRAAx] cardinalValues R s := by
  refine .allI (.impI ?_)
  have hd : Γ.map Fm.shift ⊢[PRAAx] GaussianRationalFiniteRoots.distinct (Syn.shift R) := by
    simpa only [Fm.shift,GaussianRationalFiniteRoots.subst_distinct,Syn.shift] using h.shift
  have ss : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift s) (length (Syn.shift R)) := by
    simpa only [Fm.shift,subst_lt,subst_length,Syn.shift] using hs.shift
  exact cardinal_evaluation _ _ _ hd.wk ss.wk Prf.hyp0

def certificate (R s : PTm n) : Fm PTm n := (length (deleted R s) ≐ pred (length R)) ⋏
  ((length (productPolynomial R s) ≐ length R) ⋏ (canonicalCoefficients (productPolynomial R s) ⋏
  ((entry (productPolynomial R s) zero ≐ qone) ⋏ (neg (denominator R s ≐ qzero) ⋏
  (le one (normNumerator (denominator R s)) ⋏ ((qmul (denominator R s) (reciprocal (denominator R s)) ≐ qone) ⋏
  ((length (cardinal R s) ≐ length R) ⋏ (canonicalCoefficients (cardinal R s) ⋏ cardinalValues R s))))))))
ipra_subst certificate
theorem cardinal_correct (R s : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hs : Γ ⊢[PRAAx] lt s (length R)) : Γ ⊢[PRAAx] certificate R s :=
  .andI (deleted_length _ _) (.andI (product_length _ _ hs) (.andI (product_canonical _ _) (.andI (product_monic _ _)
    (.andI (denominator_nonzero _ _ h hs) (.andI (denominator_norm_positive _ _ h hs) (.andI (inverse_valid _ _ h hs)
      (.andI (cardinal_length _ _ hs) (.andI (cardinal_canonical _ _) (cardinal_values _ _ h hs)))))))))

/-- The five algebraic fields and three original-index fields are actual
PR output. Inverse correctness remains a proved guarded conclusion. -/
def output (R s : PTm n) : PTm n := pairT
  (GaussianRationalFiberVandermonde.productData (deleted R s) (productPolynomial R s) (denominator R s)
    (reciprocal (denominator R s)) (cardinal R s)) (pairT R (pairT (length R) s))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (R s : PTm n) : PTm n := ap2 outputF R s
def cardinalField (q : PTm n) : PTm n := GaussianRationalFiberVandermonde.fields (fstT q) 4
def denominatorField (q : PTm n) : PTm n := GaussianRationalFiberVandermonde.fields (fstT q) 2
def inverseField (q : PTm n) : PTm n := GaussianRationalFiberVandermonde.fields (fstT q) 3
def rootsField (q : PTm n) : PTm n := fstT (sndT q)
ipra_subst output
ipra_subst run
ipra_subst cardinalField
ipra_subst denominatorField
ipra_subst inverseField
ipra_subst rootsField
theorem program_at (R s : PTm n) : Γ ⊢[PRAAx] run R s ≐ output R s := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![R,s]
theorem fields_congr {q q' : PTm n} (h : Γ ⊢[PRAAx] q ≐ q') (i : Fin 5) : Γ ⊢[PRAAx]
    GaussianRationalFiberVandermonde.fields q i ≐ GaussianRationalFiberVandermonde.fields q' i := by
  ipra_congr (GaussianRationalFiberVandermonde.fields (var 0) i : PTm 1) with [h]
theorem returned_field (R s : PTm n) (i : Fin 5) : Γ ⊢[PRAAx]
    GaussianRationalFiberVandermonde.fields (fstT (run R s)) i ≐
      ![deleted R s,productPolynomial R s,denominator R s,reciprocal (denominator R s),cardinal R s] i :=
  (fields_congr (program_at _ _).fstE i).eqTrans
    (GaussianRationalFiberVandermonde.field_at _ _ _ _ _ i)
theorem returned_deleted (R s : PTm n) : Γ ⊢[PRAAx] fstT (fstT (run R s)) ≐ deleted R s := returned_field _ _ 0
theorem returned_product (R s : PTm n) : Γ ⊢[PRAAx] fstT (sndT (fstT (run R s))) ≐ productPolynomial R s := returned_field _ _ 1
theorem returned_denominator (R s : PTm n) : Γ ⊢[PRAAx] denominatorField (run R s) ≐ denominator R s := returned_field _ _ 2
theorem returned_inverse (R s : PTm n) : Γ ⊢[PRAAx] inverseField (run R s) ≐ reciprocal (denominator R s) := returned_field _ _ 3
theorem returned_cardinal (R s : PTm n) : Γ ⊢[PRAAx] cardinalField (run R s) ≐ cardinal R s := returned_field _ _ 4
theorem returned_data (R s : PTm n) : Γ ⊢[PRAAx] sndT (run R s) ≐ pairT R (pairT (length R) s) :=
  (program_at _ _).sndE
theorem returned_roots (R s : PTm n) : Γ ⊢[PRAAx] rootsField (run R s) ≐ R :=
  (returned_data _ _).fstE
theorem returned_length (R s : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run R s))) ≐ length R :=
  (returned_data _ _).sndE.fstE
theorem returned_index (R s : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run R s))) ≐ s :=
  (returned_data _ _).sndE.sndE
theorem returned_denominator_nonzero (R s : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hs : Γ ⊢[PRAAx] lt s (length R)) : Γ ⊢[PRAAx] neg (denominatorField (run R s) ≐ qzero) :=
  .impI (.impE (denominator_nonzero _ _ h.wk hs.wk) ((returned_denominator _ _).eqSymm.eqTrans Prf.hyp0))
theorem returned_inverse_valid (R s : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hs : Γ ⊢[PRAAx] lt s (length R)) : Γ ⊢[PRAAx] qmul (denominatorField (run R s)) (inverseField (run R s)) ≐ qone :=
  (qmul_congr (returned_denominator _ _) (returned_inverse _ _)).eqTrans (inverse_valid _ _ h hs)
theorem returned_evaluation (R s r : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hs : Γ ⊢[PRAAx] lt s (length R)) (hr : Γ ⊢[PRAAx] lt r (length R)) : Γ ⊢[PRAAx]
    evaluate (cardinalField (run R s)) (entry (rootsField (run R s)) r) ≐ GaussianRationalFiberVandermonde.delta r s :=
  (evaluate_congr (returned_cardinal _ _) (entry_congr (returned_roots _ _) (.eqRefl _))).eqTrans (cardinal_evaluation _ _ _ h hs hr)

/-- The source wrapper uses exactly the original generated ordinate list;
its only nontrivial hypotheses are original point distinction and indices. -/
def sourceOutput (L p g s : PTm n) : PTm n := pairT (run (GaussianRationalCurveFibers.yList L p g) s)
  (pairT (GaussianRationalCurveFibers.selectedX L p g) (GaussianRationalFiberGrouping.partitionTotal L p))
def sourceF : PR 4 := PTm.toPR (sourceOutput (var 0) (var 1) (var 2) (var 3))
def sourceRun (L p g s : PTm n) : PTm n := app sourceF ![L,p,g,s]
def sourceCardinal (L p g s : PTm n) : PTm n := cardinalField (fstT (sourceRun L p g s))
ipra_subst sourceOutput
ipra_subst sourceRun
ipra_subst sourceCardinal
theorem source_program_at (L p g s : PTm n) : Γ ⊢[PRAAx] sourceRun L p g s ≐ sourceOutput L p g s := by
  simpa [sourceRun,sourceF] using toPR_eq (Γ := Γ) (sourceOutput (var 0) (var 1) (var 2) (var 3) : PTm 4) ![L,p,g,s]
theorem source_returned_generic (L p g s : PTm n) : Γ ⊢[PRAAx]
    fstT (sourceRun L p g s) ≐ run (GaussianRationalCurveFibers.yList L p g) s :=
  (source_program_at _ _ _ _).fstE
theorem source_returned_roots (L p g s : PTm n) : Γ ⊢[PRAAx]
    rootsField (fstT (sourceRun L p g s)) ≐ GaussianRationalCurveFibers.yList L p g :=
  (congrFst (congrSnd (source_returned_generic _ _ _ _))).eqTrans (returned_roots _ _)
theorem source_returned_cardinal (L p g s : PTm n) : Γ ⊢[PRAAx]
    sourceCardinal L p g s ≐ cardinal (GaussianRationalCurveFibers.yList L p g) s :=
  (fields_congr (congrFst (source_returned_generic _ _ _ _)) 4).eqTrans (returned_cardinal _ _)
theorem source_returned_x (L p g s : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sourceRun L p g s)) ≐ GaussianRationalCurveFibers.selectedX L p g :=
  (source_program_at _ _ _ _).sndE.fstE
theorem source_returned_partition (L p g s : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sourceRun L p g s)) ≐ length L :=
  (source_program_at _ _ _ _).sndE.sndE.eqTrans
    (GaussianRationalFiberGrouping.cardinal_partition _ _)
theorem source_correct (L p g s : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalCurveFibers.pointDistinct L)
    (hs : Γ ⊢[PRAAx] lt s (GaussianRationalFiberGrouping.fiberCount L p g)) : Γ ⊢[PRAAx]
    certificate (GaussianRationalCurveFibers.yList L p g) s :=
  cardinal_correct _ _ (GaussianRationalCurveFibers.fiber_ordinates_distinct _ _ _ h)
    (lt_congr (.eqRefl _) (GaussianRationalCurveFibers.y_length _ _ _).eqSymm hs)
theorem source_cardinal_evaluation (L p g s r : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalCurveFibers.pointDistinct L)
    (hs : Γ ⊢[PRAAx] lt s (GaussianRationalFiberGrouping.fiberCount L p g))
    (hr : Γ ⊢[PRAAx] lt r (GaussianRationalFiberGrouping.fiberCount L p g)) : Γ ⊢[PRAAx]
    evaluate (sourceCardinal L p g s) (entry (rootsField (fstT (sourceRun L p g s))) r) ≐ GaussianRationalFiberVandermonde.delta r s :=
  (evaluate_congr (source_returned_cardinal _ _ _ _) (entry_congr (source_returned_roots _ _ _ _) (.eqRefl _))).eqTrans
    (cardinal_evaluation _ _ _ (GaussianRationalCurveFibers.fiber_ordinates_distinct _ _ _ h)
      (lt_congr (.eqRefl _) (GaussianRationalCurveFibers.y_length _ _ _).eqSymm hs)
      (lt_congr (.eqRefl _) (GaussianRationalCurveFibers.y_length _ _ _).eqSymm hr))


/-! Ordinary closed endpoints retain every original numerical list,
position, source payload and query. No host dimension is substituted. -/
theorem deletion_coverage_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (length (var 0)) ⟶ lt (var 2) (length (var 0)) ⟶ neg (var 2 ≐ var 1) ⟶
      (lt (slot (var 1) (var 2)) (pred (length (var 0))) ⋏
        (entry (deleted (var 0) (var 1)) (slot (var 1) (var 2)) ≐ entry (var 0) (var 2)))) :=
  closeUniv 3 (.impI (.impI (.impI (deleted_covers _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem denominator_nonzero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianRationalFiniteRoots.distinct (var 0) ⟶ lt (var 1) (length (var 0)) ⟶
      neg (denominator (var 0) (var 1) ≐ qzero)) :=
  closeUniv 2 (.impI (.impI (denominator_nonzero _ _ Prf.hyp1 Prf.hyp0)))
theorem cardinal_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianRationalFiniteRoots.distinct (var 0) ⟶ lt (var 1) (length (var 0)) ⟶
      qmul (denominator (var 0) (var 1)) (reciprocal (denominator (var 0) (var 1))) ≐ qone) :=
  closeUniv 2 (.impI (.impI (inverse_valid _ _ Prf.hyp1 Prf.hyp0)))
theorem cardinal_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianRationalFiniteRoots.distinct (var 0) ⟶ lt (var 1) (length (var 0)) ⟶ lt (var 2) (length (var 0)) ⟶
      evaluate (cardinal (var 0) (var 1)) (entry (var 0) (var 2)) ≐ GaussianRationalFiberVandermonde.delta (var 2) (var 1)) :=
  closeUniv 3 (.impI (.impI (.impI (cardinal_evaluation _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem ascending_coefficient_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (length (var 0)) ⟶ coefficientEvaluation (var 0) (var 1) (var 2) ≐ evaluate (cardinal (var 0) (var 1)) (var 2)) :=
  closeUniv 3 (.impI (coefficient_evaluation _ _ _ Prf.hyp0))
theorem cardinal_dot_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianRationalFiniteRoots.distinct (var 0) ⟶ lt (var 1) (length (var 0)) ⟶ lt (var 2) (length (var 0)) ⟶
      dot (var 0) (var 1) (var 2) ≐ GaussianRationalFiberVandermonde.delta (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (cardinal_dot _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem cardinal_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianRationalFiniteRoots.distinct (var 0) ⟶ lt (var 1) (length (var 0)) ⟶ certificate (var 0) (var 1)) :=
  closeUniv 2 (.impI (.impI (cardinal_correct _ _ Prf.hyp1 Prf.hyp0)))
theorem cardinal_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((run (var 0) (var 1) ≐ output (var 0) (var 1)) ⋏ (rootsField (run (var 0) (var 1)) ≐ var 0)) :=
  closeUniv 2 (.andI (program_at _ _) (returned_roots _ _))
theorem original_fiber_cardinals_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianRationalCurveFibers.pointDistinct (var 0) ⟶
      lt (var 3) (GaussianRationalFiberGrouping.fiberCount (var 0) (var 1) (var 2)) ⟶
      certificate (GaussianRationalCurveFibers.yList (var 0) (var 1) (var 2)) (var 3)) :=
  closeUniv 4 (.impI (.impI (source_correct _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem source_program_fields_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((rootsField (fstT (sourceRun (var 0) (var 1) (var 2) (var 3))) ≐ GaussianRationalCurveFibers.yList (var 0) (var 1) (var 2)) ⋏
      (sndT (sndT (sourceRun (var 0) (var 1) (var 2) (var 3))) ≐ length (var 0))) :=
  closeUniv 4 (.andI (source_returned_roots _ _ _ _) (source_returned_partition _ _ _ _))
theorem returned_source_cardinal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianRationalCurveFibers.pointDistinct (var 0) ⟶
      lt (var 3) (GaussianRationalFiberGrouping.fiberCount (var 0) (var 1) (var 2)) ⟶
      lt (var 4) (GaussianRationalFiberGrouping.fiberCount (var 0) (var 1) (var 2)) ⟶
      evaluate (sourceCardinal (var 0) (var 1) (var 2) (var 3))
        (entry (rootsField (fstT (sourceRun (var 0) (var 1) (var 2) (var 3)))) (var 4)) ≐ GaussianRationalFiberVandermonde.delta (var 4) (var 3)) :=
  closeUniv 5 (.impI (.impI (.impI (source_cardinal_evaluation _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianRationalLagrangeCardinals
