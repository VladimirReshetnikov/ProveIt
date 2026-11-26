import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalLinearProduct

/-!
# Actual one-step rational synthetic-division error transport

The coefficient error compares the supplied polynomial with a genuine
linear-factor reconstruction. Its quotient error is the actual synthetic
quotient minus the supplied comparison coefficients. The residual is the
actual polynomial evaluation, stored only at the last coefficient.
All counts and operand denominators are internal. Input coefficients need
not be canonical: equality is proved between normalized arithmetic outputs.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192

namespace LeanProofs.IPRA.Analysis.GaussianRationalDeflationError

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (qzero qadd qmul represents canonical qadd_canonical qmul_canonical qadd_represents qmul_represents
    represents_rescale represents_congr canonical_unique zero_represents positive_product horner evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub qsub_represents qsub_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (quotient quotient_length quotient_lookup quotient_recurrence qadd_congr qmul_congr qsub_congr
    rescale_to remainingDen remaining_den_positive qzero_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (qL1 rawDen rawGaussian raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.GaussianCoefficientL1
  (subCoefficients sub_lookup prefixNorm coefficientNorm norm_guard qL1_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalLinearProduct
  (linear padded delayed coefficient padded_inside padded_outside delayed_zero delayed_succ)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra
  (equal equal_of_values re_add im_add re_mul im_mul re_scale im_scale re_sub im_sub)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (re im scale)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open LeanProofs.IPRA.Analysis.RationalArithmetic (add multiply)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

/-- The normalized error identity derived from one true Horner step.
No literal canonicality of the input coefficient p is used. -/
theorem affine_error_from_representations (a p f d z A P F D Z E : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (ha : Γ ⊢[PRAAx] represents a A E)
    (hp : Γ ⊢[PRAAx] represents p P E) (hf : Γ ⊢[PRAAx] represents f F E)
    (hd : Γ ⊢[PRAAx] represents d D E) (hz : Γ ⊢[PRAAx] represents z Z E) : Γ ⊢[PRAAx]
    qsub p (qsub f (qmul d z)) ≐
      qsub (qsub (qadd (qmul a z) p) f) (qmul (qsub a d) z) := by
  have E2 := positive_product E E hE hE
  have p2 := represents_rescale p P E E hp
  have f2 := represents_rescale f F E E hf
  have dz := qmul_represents _ _ _ _ _ _ hE hE hd hz
  have left := qsub_represents _ _ _ _ _ E2 p2 (qsub_represents _ _ _ _ _ E2 f2 dz)
  have az := qmul_represents _ _ _ _ _ _ hE hE ha hz
  have top := qadd_represents _ _ _ _ _ E2 az p2
  have diff := qsub_represents _ _ _ _ _ E2 top f2
  have bottom := qmul_represents _ _ _ _ _ _ hE hE (qsub_represents _ _ _ _ _ hE ha hd) hz
  have right := qsub_represents _ _ _ _ _ E2 diff bottom
  apply canonical_unique _ _ _ _ (qsub_canonical _ _) (qsub_canonical _ _) E2 (hrv := right)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := left)
  apply equal_of_values <;> simp only [re_sub,im_sub,re_add,im_add,re_mul,im_mul,re_scale,im_scale] <;> ring

theorem affine_error (a p f d z : PTm n) : Γ ⊢[PRAAx]
    qsub p (qsub f (qmul d z)) ≐
      qsub (qsub (qadd (qmul a z) p) f) (qmul (qsub a d) z) := by
  let E := rawDen a*remainingDen p f d z
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ (raw_den_positive a) (remaining_den_positive p f d z)
  have ha := rescale_to a (rawGaussian a) (rawDen a) (remainingDen p f d z) E (raw_represents (Γ := Γ) a) (.eqRefl _)
  have hp := rescale_to p (rawGaussian p) (rawDen p) (remainingDen a f d z) E (raw_represents (Γ := Γ) p)
    (by unfold E remainingDen; ipra_ring)
  have hf := rescale_to f (rawGaussian f) (rawDen f) (remainingDen a p d z) E (raw_represents (Γ := Γ) f)
    (by unfold E remainingDen; ipra_ring)
  have hd := rescale_to d (rawGaussian d) (rawDen d) (remainingDen a p f z) E (raw_represents (Γ := Γ) d)
    (by unfold E remainingDen; ipra_ring)
  have hz := rescale_to z (rawGaussian z) (rawDen z) (remainingDen a p f d) E (raw_represents (Γ := Γ) z)
    (by unfold E remainingDen; ipra_ring)
  exact affine_error_from_representations _ _ _ _ _ _ _ _ _ _ E hE ha hp hf hd hz

/-- Moving the actual residual past two differences is finite Gaussian
arithmetic, independent of the polynomial representation. -/
theorem split_residual_from_representations (q r f v Q R F V E : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hq : Γ ⊢[PRAAx] represents q Q E)
    (hr : Γ ⊢[PRAAx] represents r R E) (hf : Γ ⊢[PRAAx] represents f F E)
    (hv : Γ ⊢[PRAAx] represents v V E) : Γ ⊢[PRAAx]
    qsub (qsub (qadd q r) f) v ≐ qadd (qsub (qsub q f) v) r := by
  have left := qsub_represents _ _ _ _ _ hE (qsub_represents _ _ _ _ _ hE (qadd_represents _ _ _ _ _ hE hq hr) hf) hv
  have right := qadd_represents _ _ _ _ _ hE (qsub_represents _ _ _ _ _ hE (qsub_represents _ _ _ _ _ hE hq hf) hv) hr
  apply canonical_unique _ _ _ _ (qsub_canonical _ _) (qadd_canonical _ _) hE (hrv := right)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := left)
  apply equal_of_values <;> simp only [re_sub,im_sub,re_add,im_add] <;> ring

theorem split_residual (q r f v : PTm n) : Γ ⊢[PRAAx]
    qsub (qsub (qadd q r) f) v ≐ qadd (qsub (qsub q f) v) r := by
  let E := remainingDen q r f v
  have hE : Γ ⊢[PRAAx] le one E := remaining_den_positive _ _ _ _
  have hq := rescale_to q (rawGaussian q) (rawDen q) (rawDen r*rawDen f*rawDen v) E (raw_represents (Γ := Γ) q)
    (by unfold E remainingDen; ipra_ring)
  have hr := rescale_to r (rawGaussian r) (rawDen r) (rawDen q*rawDen f*rawDen v) E (raw_represents (Γ := Γ) r)
    (by unfold E remainingDen; ipra_ring)
  have hf := rescale_to f (rawGaussian f) (rawDen f) (rawDen q*rawDen r*rawDen v) E (raw_represents (Γ := Γ) f)
    (by unfold E remainingDen; ipra_ring)
  have hv := rescale_to v (rawGaussian v) (rawDen v) (rawDen q*rawDen r*rawDen f) E (raw_represents (Γ := Γ) v)
    (by unfold E remainingDen; ipra_ring)
  exact split_residual_from_representations _ _ _ _ _ _ _ _ E hE hq hr hf hv

theorem error_with_residual (a p f d z q r : PTm n)
    (h : Γ ⊢[PRAAx] qadd q r ≐ qadd (qmul a z) p) : Γ ⊢[PRAAx]
    qsub p (qsub f (qmul d z)) ≐ qadd (qsub (qsub q f) (qmul (qsub a d) z)) r :=
  (affine_error a p f d z).eqTrans ((qsub_congr (qsub_congr h.eqSymm (.eqRefl _)) (.eqRefl _)).eqTrans
    (split_residual q r f (qmul (qsub a d) z)))

theorem qsub_zero_zero : Γ ⊢[PRAAx] qsub (qzero : PTm n) qzero ≐ qzero :=
  (qsub_congr (GaussianRationalSyntheticDivision.qzero_add qzero qzero_canonical).eqSymm (.eqRefl _)).eqTrans
    (GaussianRationalSyntheticDivision.qadd_sub_cancel qzero qzero qzero_canonical)

/-- Zero padding commutes with the actual finite coefficient difference,
even outside the stored list and for noncanonical operands. -/
theorem padded_sub (C F N i : PTm n) : Γ ⊢[PRAAx]
    padded (subCoefficients C F N) N i ≐ qsub (padded C N i) (padded F N i) := by
  refine .orE (lt_or_le i N) ?_ ?_
  · exact (padded_inside _ _ _ Prf.hyp0).eqTrans
      ((sub_lookup C F N i Prf.hyp0).eqTrans (qsub_congr (padded_inside C N i Prf.hyp0).eqSymm
        (padded_inside F N i Prf.hyp0).eqSymm))
  · exact (padded_outside _ _ _ Prf.hyp0).eqTrans (qsub_zero_zero.eqSymm.eqTrans
      (qsub_congr (padded_outside C N i Prf.hyp0).eqSymm (padded_outside F N i Prf.hyp0).eqSymm))

theorem delayed_congr {C C' N N' i i' : PTm n} (hC : Γ ⊢[PRAAx] C ≐ C')
    (hN : Γ ⊢[PRAAx] N ≐ N') (hi : Γ ⊢[PRAAx] i ≐ i') : Γ ⊢[PRAAx] delayed C N i ≐ delayed C' N' i' :=
  (GaussianRationalLinearProduct.delayed_at C N i).eqSymm.eqTrans
    ((congrAp3 GaussianRationalLinearProduct.delayedF hC hN hi).eqTrans
      (GaussianRationalLinearProduct.delayed_at C' N' i'))

theorem delayed_sub (C F N i : PTm n) : Γ ⊢[PRAAx]
    delayed (subCoefficients C F N) N i ≐ qsub (delayed C N i) (delayed F N i) := by
  refine .orE (zero_or_succ i) ?_ ?_
  · have ec : ((i ≐ zero) :: Γ) ⊢[PRAAx] delayed C N i ≐ qzero :=
      (delayed_congr (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (delayed_zero C N)
    have ef : ((i ≐ zero) :: Γ) ⊢[PRAAx] delayed F N i ≐ qzero :=
      (delayed_congr (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (delayed_zero F N)
    exact ((delayed_congr (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (delayed_zero _ _)).eqTrans
      (qsub_zero_zero.eqSymm.eqTrans (qsub_congr ec.eqSymm ef.eqSymm))
  · have ec : ((i ≐ succ (PTm.pred i)) :: Γ) ⊢[PRAAx] delayed C N i ≐ padded C N (PTm.pred i) :=
      (delayed_congr (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (delayed_succ C N _)
    have ef : ((i ≐ succ (PTm.pred i)) :: Γ) ⊢[PRAAx] delayed F N i ≐ padded F N (PTm.pred i) :=
      (delayed_congr (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (delayed_succ F N _)
    exact ((delayed_congr (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (delayed_succ _ _ _)).eqTrans
      ((padded_sub C F N _).eqTrans (qsub_congr ec.eqSymm ef.eqSymm))

/-- The delayed quotient at every relevant coefficient is precisely the
actual previous Horner accumulator, including the zero-th position. -/
theorem delayed_quotient (P z N i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    delayed (quotient P z N) N i ≐ horner P z i := by
  refine .orE (zero_or_succ i) ?_ ?_
  · have h : ((i ≐ zero) :: Γ) ⊢[PRAAx] delayed (quotient P z N) N i ≐ qzero :=
      (delayed_congr (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (delayed_zero _ _)
    have e : ((i ≐ zero) :: Γ) ⊢[PRAAx] horner P z i ≐ qzero :=
      (congrAp3 GaussianRationalHorner.hornerF Prf.hyp0 (.eqRefl _) (.eqRefl _)).eqTrans
        (GaussianRationalHorner.horner_zero _ _)
    exact h.eqTrans e.eqSymm
  · have range : ((i ≐ succ (PTm.pred i)) :: Γ) ⊢[PRAAx] lt (PTm.pred i) N :=
      le_congr Prf.hyp0 (.eqRefl _) hi.wk
    exact ((delayed_congr (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (delayed_succ _ _ _)).eqTrans
      ((padded_inside _ _ _ range).eqTrans ((quotient_lookup P z N _ range).eqTrans
        (congrAp3 GaussianRationalHorner.hornerF Prf.hyp0.eqSymm (.eqRefl _) (.eqRefl _))))


open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticBounds (natCode)
open LeanProofs.IPRA.Analysis.GaussianRationalLinearProduct (qzero_norm scalar_zero_code scalar_add_zero scalar_zero_add norm_length rational_eq_of_code)
open LeanProofs.IPRA.Foundations.MasterCertificate (subst_sequence)
open LeanProofs.IPRA.Signum (sg)

def residualAt (R N i : PTm n) : PTm n := RationalArithmetic.select (sg (PTm.monus N i)) R qzero
ipra_subst residualAt
theorem residualAt_inside (R N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] residualAt R N i ≐ qzero :=
  RationalArithmetic.select_one _ _ _ (AnalyticNumberTheory.Totatives.sg_lt hi)
theorem residualAt_end (R N : PTm n) : Γ ⊢[PRAAx] residualAt R N N ≐ R :=
  RationalArithmetic.select_zero _ _ _ (AnalyticNumberTheory.Totatives.sg_le (le_refl _))

def residualAtF : PR 3 := PTm.toPR (residualAt (var 0) (var 1) (var 2))
theorem residualAt_at (R N i : PTm n) : Γ ⊢[PRAAx] ap3 residualAtF R N i ≐ residualAt R N i := by
  simpa only [residualAtF,ap3,subst_residualAt,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (residualAt (var 0) (var 1) (var 2) : PTm 3) ![R,N,i]
def residualBody : PTm 2 := ap3 residualAtF (fstT (var 1)) (sndT (var 1)) (var 0)
def residualVector (R N : PTm n) : PTm n := sequence residualBody (succ N) (pairT R N)
ipra_subst residualVector
theorem residual_length (R N : PTm n) : Γ ⊢[PRAAx] length (residualVector R N) ≐ succ N := sequence_length _ _ _
theorem residual_lookup (R N i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    entry (residualVector R N) i ≐ residualAt R N i := by
  have e : Γ ⊢[PRAAx] entry (residualVector R N) i ≐ inst2 residualBody i (pairT R N) :=
    sequence_decode residualBody ((succ_monus_succ _ _).eqTrans hi)
  simp only [residualBody,inst2,subst_ap3,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] at e
  exact e.eqTrans ((congrAp3 residualAtF (fst_pair _ _) (snd_pair _ _) (.eqRefl _)).eqTrans (residualAt_at R N i))

def zeroBody : PTm 2 := natCode zero
@[simp] theorem zero_term (i x : PTm n) : RationalFiniteSum.term zeroBody i x = natCode zero := by
  simp only [RationalFiniteSum.term,zeroBody,inst2,GaussianRationalSyntheticBounds.subst_natCode,ConciseIPRA.PTm.subst_zero]
theorem zero_sum (k x : PTm n) : Γ ⊢[PRAAx] RationalFiniteSum.sum zeroBody k x ≐ natCode zero := by
  have all : Γ ⊢[PRAAx] .all (RationalFiniteSum.sum zeroBody (var 0) (Syn.shift x) ≐ natCode zero) := by
    ipra_qfind [RationalFiniteSum.subst_sum, GaussianRationalSyntheticBounds.subst_natCode]
    · exact (RationalFiniteSum.sum_zero _ _).eqTrans scalar_zero_code.eqSymm
    · have step : ((RationalFiniteSum.sum zeroBody (var 0) (Syn.shift x) ≐ natCode zero) :: Γ.map Fm.shift) ⊢[PRAAx]
          RationalFiniteSum.sum zeroBody (succ (var 0)) (Syn.shift x) ≐
            add (RationalFiniteSum.sum zeroBody (var 0) (Syn.shift x)) (natCode zero) := by
        simpa only [zero_term] using RationalFiniteSum.sum_succ (Γ := (RationalFiniteSum.sum zeroBody (var 0) (Syn.shift x) ≐ natCode zero) :: Γ.map Fm.shift) zeroBody (var 0) (Syn.shift x)
      exact step.eqTrans ((RationalAlgebra.add_congr Prf.hyp0 (.eqRefl (natCode zero))).eqTrans
        (scalar_add_zero _ (RationalNormalForm.normalize_well_formed _ _ (le_refl one))))
  simpa only [Fm.subst_eq,RationalFiniteSum.subst_sum,GaussianRationalSyntheticBounds.subst_natCode,ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

theorem residual_prefix (R N : PTm n) : Γ ⊢[PRAAx] prefixNorm (residualVector R N) N ≐ natCode zero := by
  have e : Γ ⊢[PRAAx] prefixNorm (residualVector R N) N ≐ RationalFiniteSum.sum zeroBody N R := by
    apply RationalFiniteSum.sum_ext
    refine .allI (.impI ?_)
    have h : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx] qL1 (entry (residualVector (Syn.shift R) (Syn.shift N)) (var 0)) ≐ natCode zero := (qL1_congr ((residual_lookup (Syn.shift R) (Syn.shift N) (var 0) (le_of_lt Prf.hyp0)).eqTrans
      (residualAt_inside _ _ _ Prf.hyp0))).eqTrans qzero_norm
    simpa only [GaussianCoefficientL1.norm_body_at,zero_term,Syn.shift,subst_residualVector] using rational_eq_of_code h
  exact e.eqTrans (zero_sum N R)

theorem residual_norm (R N : PTm n) : Γ ⊢[PRAAx] coefficientNorm (residualVector R N) ≐ qL1 R :=
  (norm_length _ _ (residual_length R N)).eqTrans ((GaussianCoefficientL1.prefix_succ _ _).eqTrans
    ((RationalAlgebra.add_congr (residual_prefix R N)
      (qL1_congr ((residual_lookup R N N (le_refl _)).eqTrans (residualAt_end R N)))).eqTrans
        (scalar_zero_add _ (GaussianRationalL1.qL1_guard _))))

theorem residualAt_congr {R R' N N' i i' : PTm n} (hR : Γ ⊢[PRAAx] R ≐ R')
    (hN : Γ ⊢[PRAAx] N ≐ N') (hi : Γ ⊢[PRAAx] i ≐ i') : Γ ⊢[PRAAx]
    residualAt R N i ≐ residualAt R' N' i' :=
  (residualAt_at R N i).eqSymm.eqTrans ((congrAp3 residualAtF hR hN hi).eqTrans (residualAt_at R' N' i'))

/-- A single uniform local equation, including the final residual position,
derived from the actual quotient's Horner recurrence. -/
theorem padded_recurrence (P z N i : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    qadd (padded (quotient P z N) N i) (residualAt (evaluate P z) N i) ≐
      qadd (qmul (delayed (quotient P z N) N i) z) (entry P i) := by
  refine .orE (lt_or_eq_of_le hi) ?_ ?_
  · have top : (lt i N :: Γ) ⊢[PRAAx] qadd (padded (quotient P z N) N i) (residualAt (evaluate P z) N i) ≐
        entry (quotient P z N) i :=
      (qadd_congr (padded_inside _ _ _ Prf.hyp0) (residualAt_inside _ _ _ Prf.hyp0)).eqTrans
        (GaussianRationalLinearProduct.qadd_zero_right _
          (GaussianRationalSyntheticDivision.quotient_coefficient_canonical P z N i Prf.hyp0))
    exact top.eqTrans ((quotient_recurrence P z N i Prf.hyp0).eqTrans
      (qadd_congr (qmul_congr (delayed_quotient P z N i hi.wk).eqSymm (.eqRefl _)) (.eqRefl _)))
  · have range : ((i ≐ N) :: Γ) ⊢[PRAAx] le N i := le_congr (.eqRefl _) Prf.hyp0.eqSymm (le_refl _)
    have top : ((i ≐ N) :: Γ) ⊢[PRAAx] qadd (padded (quotient P z N) N i) (residualAt (evaluate P z) N i) ≐ evaluate P z :=
      (qadd_congr (padded_outside _ _ _ range)
        ((residualAt_congr (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (residualAt_end _ _))).eqTrans
          (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalHorner.horner_canonical _ _ _))
    have eval : ((i ≐ N) :: Γ) ⊢[PRAAx] evaluate P z ≐ qadd (qmul (horner P z i) z) (entry P i) :=
      (congrAp3 GaussianRationalHorner.hornerF hP.wk (.eqRefl _) (.eqRefl _)).eqTrans
        ((GaussianRationalHorner.horner_succ P z N).eqTrans
          (qadd_congr (qmul_congr (congrAp3 GaussianRationalHorner.hornerF Prf.hyp0.eqSymm (.eqRefl _) (.eqRefl _))
            (.eqRefl _)) (entry_congr (.eqRefl _) Prf.hyp0.eqSymm)))
    exact top.eqTrans (eval.eqTrans
      (qadd_congr (qmul_congr (delayed_quotient P z N i hi.wk).eqSymm (.eqRefl _)) (.eqRefl _)))

def quotientError (P F z N : PTm n) : PTm n := subCoefficients (quotient P z N) F N
def inputError (P F z N : PTm n) : PTm n := subCoefficients P (linear F z N) (succ N)

ipra_subst quotientError
ipra_subst inputError

theorem quotient_error_length (P F z N : PTm n) : Γ ⊢[PRAAx] length (quotientError P F z N) ≐ N :=
  GaussianCoefficientL1.zip_length _ _ _ _
theorem input_error_length (P F z N : PTm n) : Γ ⊢[PRAAx] length (inputError P F z N) ≐ succ N :=
  GaussianCoefficientL1.zip_length _ _ _ _

/-- The exact coefficient identity for the actual normalized error vector.
It is derived at an arbitrary internal index, not supplied as a trace. -/
theorem error_coefficient (P F z N i : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    entry (inputError P F z N) i ≐
      qadd (entry (linear (quotientError P F z N) z N) i) (entry (residualVector (evaluate P z) N) i) := by
  have range : Γ ⊢[PRAAx] lt i (succ N) := (succ_monus_succ _ _).eqTrans hi
  have input : Γ ⊢[PRAAx] entry (inputError P F z N) i ≐ qsub (entry P i) (coefficient F z N i) :=
    (sub_lookup P (linear F z N) (succ N) i range).eqTrans
      (qsub_congr (.eqRefl _) (GaussianRationalLinearProduct.linear_lookup F z N i hi))
  have err : Γ ⊢[PRAAx] entry (linear (quotientError P F z N) z N) i ≐
      qsub (qsub (padded (quotient P z N) N i) (padded F N i))
        (qmul (qsub (delayed (quotient P z N) N i) (delayed F N i)) z) :=
    (GaussianRationalLinearProduct.linear_lookup _ _ _ _ hi).eqTrans
      (qsub_congr (padded_sub (quotient P z N) F N i)
        (qmul_congr (delayed_sub (quotient P z N) F N i) (.eqRefl _)))
  exact input.eqTrans ((error_with_residual _ _ _ _ _ _ _ (padded_recurrence P z N i hP hi)).eqTrans
    (qadd_congr err.eqSymm (residual_lookup _ _ _ hi).eqSymm))

/-- The finite norm triangle is applied to the derived coefficient identity,
with both complete output lengths supplied by their actual constructors. -/
theorem error_norm_triangle (P F z N : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (inputError P F z N))
      (add (coefficientNorm (linear (quotientError P F z N) z N)) (qL1 (evaluate P z))) := by
  let A := linear (quotientError P F z N) z N
  let R := residualVector (evaluate P z) N
  have terms : Γ ⊢[PRAAx] RationalFiniteSum.termwiseLE GaussianCoefficientL1.normBody
      (RationalSumAdditivity.addedBody GaussianCoefficientL1.normBody GaussianCoefficientL1.normBody)
      (succ N) (inputError P F z N) (pairT A R) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift
    have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) :=
      (succ_monus_succ _ _).eqSymm.eqTrans (by simpa only [Δ,lt,le,Syn.shift,ConciseIPRA.PTm.subst_succ] using Prf.hyp0)
    have shape : Δ ⊢[PRAAx] length (Syn.shift P) ≐ succ (Syn.shift N) := by
      simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hP.shift.wk
    have e := qL1_congr (error_coefficient (Syn.shift P) (Syn.shift F) (Syn.shift z) (Syn.shift N) (var 0) shape hi)
    have r := RationalSumAdditivity.added_term (Γ := Δ) GaussianCoefficientL1.normBody GaussianCoefficientL1.normBody
      (var 0) (linear (quotientError (Syn.shift P) (Syn.shift F) (Syn.shift z) (Syn.shift N)) (Syn.shift z) (Syn.shift N))
      (residualVector (evaluate (Syn.shift P) (Syn.shift z)) (Syn.shift N))
    simp only [GaussianCoefficientL1.norm_body_at] at r
    have point := RationalArgmin.rationalLE_congr e.eqSymm r.eqSymm (GaussianRationalL1Algebra.qL1_add _ _)
    simpa only [Δ,A,R,GaussianCoefficientL1.norm_body_at,Syn.shift,subst_inputError,subst_quotientError,
      GaussianRationalLinearProduct.subst_linear,subst_residualVector,GaussianRationalHorner.subst_evaluate,subst_pairT] using point
  have summed := RationalFiniteSum.sum_monotone _ _ _ _ _ terms
  have right : Γ ⊢[PRAAx] RationalFiniteSum.sum
      (RationalSumAdditivity.addedBody GaussianCoefficientL1.normBody GaussianCoefficientL1.normBody)
      (succ N) (pairT A R) ≐ add (coefficientNorm A) (qL1 (evaluate P z)) :=
    (RationalSumAdditivity.sum_additive _ _ _ A R).eqTrans
      (RationalAlgebra.add_congr (norm_length A _ (GaussianRationalLinearProduct.linear_length _ _ _)).eqSymm
        ((norm_length R _ (residual_length _ _)).eqSymm.eqTrans (residual_norm _ _)))
  exact RationalArgmin.rationalLE_congr (norm_length _ _ (input_error_length P F z N)).eqSymm right summed

/-- Actual one-step deflation error transport. The comparison uses exactly
its first N coefficients, as specified by the linear-product producer.
Thus neither canonical input storage nor even a stored length of F is
needed; in particular the usual len(F)=N, N>=1 source instance follows. -/
theorem deflation_error_bound (P F z N : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (inputError P F z N))
      (add (qL1 (evaluate P z))
        (multiply (add (natCode one) (qL1 z)) (coefficientNorm (quotientError P F z N)))) := by
  have linearBound := GaussianRationalLinearProduct.linear_norm_bound (Γ := Γ) (quotientError P F z N) z N (quotient_error_length P F z N)
  have grow := GaussianRationalSyntheticBounds.add_monotone _ _ _ _ linearBound (RationalArgmin.reflexive (qL1 (evaluate P z)))
  have total := RationalArgmin.transitive (error_norm_triangle P F z N hP) grow
  exact RationalArgmin.rationalLE_congr (.eqRefl _) (RationalAlgebra.add_commutative _ _) total

/-! Actual fixed programs and universally closed source endpoints. -/
def output (P F z N : PTm n) : PTm n := pairT (inputError P F z N)
  (pairT (quotientError P F z N) (residualVector (evaluate P z) N))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
ipra_subst output
theorem output_at (P F z N : PTm n) : Γ ⊢[PRAAx] PTm.app outputF ![P,F,z,N] ≐ output P F z N := by
  simpa only [outputF,subst_output,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using toPR_eq (Γ := Γ)
      (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![P,F,z,N]

theorem error_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 3) ⟶ le (var 4) (var 3) ⟶
      entry (inputError (var 0) (var 1) (var 2) (var 3)) (var 4) ≐
        qadd (entry (linear (quotientError (var 0) (var 1) (var 2) (var 3)) (var 2) (var 3)) (var 4))
          (entry (residualVector (evaluate (var 0) (var 2)) (var 3)) (var 4))) :=
  closeUniv 5 (.impI (.impI (error_coefficient _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem residual_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((length (residualVector (var 0) (var 1)) ≐ succ (var 1)) ⋏
      (coefficientNorm (residualVector (var 0) (var 1)) ≐ qL1 (var 0))) :=
  closeUniv 2 (.andI (residual_length _ _) (residual_norm _ _))

theorem deflation_error_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 3) ⟶
      rationalLE (coefficientNorm (inputError (var 0) (var 1) (var 2) (var 3)))
        (add (qL1 (evaluate (var 0) (var 2)))
          (multiply (add (natCode one) (qL1 (var 2)))
            (coefficientNorm (quotientError (var 0) (var 1) (var 2) (var 3)))))) :=
  closeUniv 4 (.impI (deflation_error_bound _ _ _ _ Prf.hyp0))

theorem deflation_error_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((PTm.app outputF ![var 0,var 1,var 2,var 3] ≐ output (var 0) (var 1) (var 2) (var 3)) ⋏
      ((length (inputError (var 0) (var 1) (var 2) (var 3)) ≐ succ (var 3)) ⋏
        (length (quotientError (var 0) (var 1) (var 2) (var 3)) ≐ var 3))) :=
  closeUniv 4 (.andI (output_at _ _ _ _) (.andI (input_error_length _ _ _ _) (quotient_error_length _ _ _ _)))

end LeanProofs.IPRA.Analysis.GaussianRationalDeflationError
