import IPRADerivations.Analysis.Polynomials.Coefficients.Norms.GaussianCoefficientL1
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.GaussianRationalSyntheticBounds
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalIdentities.RationalSumLinearity

/-!
# Actual rational multiplication by a linear polynomial

The runtime coefficient producer stores c_i-c_(i-1)z, with explicit qzero
padding and a zero delayed coefficient at index zero. All arithmetic uses
actual independently normalizing Gaussian-rational operations. Source
coefficient length and canonical storage are explicit where literal input
coefficients are recovered. The coefficient L1 estimate concerns the actual
finite rational norm sums; no factorization or output bound is an input.
This is a linear-factor dependency of finite-demand (TE), not a full
convolution or deflation theorem.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192

namespace LeanProofs.IPRA.Analysis.GaussianRationalLinearProduct

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd qmul canonical represents horner evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (qL1 rawDen rawGaussian raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.GaussianCoefficientL1 (qL1_congr prefixNorm coefficientNorm norm_guard)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticBounds (natCode natCode_represents add_monotone)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr canonicalCoefficients)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE rationalEq)
open LeanProofs.IPRA.Analysis.RationalArithmetic (add multiply)
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry subst_sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.Signum (sg)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def padded (C N i : PTm n) : PTm n := RationalArithmetic.select (sg (PTm.monus N i)) qzero (entry C i)
def delayed (C N i : PTm n) : PTm n := RationalArithmetic.select (sg i) qzero (padded C N (PTm.pred i))
def coefficient (C z N i : PTm n) : PTm n := qsub (padded C N i) (qmul (delayed C N i) z)

ipra_subst padded
ipra_subst delayed
ipra_subst coefficient

theorem padded_inside (C N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] padded C N i ≐ entry C i :=
  RationalArithmetic.select_one _ _ _ (AnalyticNumberTheory.Totatives.sg_lt hi)
theorem padded_outside (C N i : PTm n) (hi : Γ ⊢[PRAAx] le N i) : Γ ⊢[PRAAx] padded C N i ≐ qzero :=
  RationalArithmetic.select_zero _ _ _ (AnalyticNumberTheory.Totatives.sg_le hi)
theorem delayed_zero (C N : PTm n) : Γ ⊢[PRAAx] delayed C N zero ≐ qzero :=
  RationalArithmetic.select_zero _ _ _ Signum.sg_zero

theorem padded_congr {C C' N N' i i' : PTm n} (hC : Γ ⊢[PRAAx] C ≐ C')
    (hN : Γ ⊢[PRAAx] N ≐ N') (hi : Γ ⊢[PRAAx] i ≐ i') : Γ ⊢[PRAAx] padded C N i ≐ padded C' N' i' := by
  ipra_congr (padded (var 0) (var 1) (var 2) : PTm 3) with [hC, hN, hi]

theorem delayed_succ (C N i : PTm n) : Γ ⊢[PRAAx] delayed C N (succ i) ≐ padded C N i :=
  (RationalArithmetic.select_one _ _ _ (Signum.sg_succ i)).eqTrans
    (padded_congr (.eqRefl _) (.eqRefl _) (pred_succ i))

def paddedF : PR 3 := PTm.toPR (padded (var 0) (var 1) (var 2))
def delayedF : PR 3 := PTm.toPR (delayed (var 0) (var 1) (var 2))

theorem padded_at (C N i : PTm n) : Γ ⊢[PRAAx] ap3 paddedF C N i ≐ padded C N i := by
  simpa only [paddedF,ap3,subst_padded,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (padded (var 0) (var 1) (var 2) : PTm 3) ![C,N,i]
theorem delayed_at (C N i : PTm n) : Γ ⊢[PRAAx] ap3 delayedF C N i ≐ delayed C N i := by
  simpa only [delayedF,ap3,subst_delayed,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (delayed (var 0) (var 1) (var 2) : PTm 3) ![C,N,i]

def data (C z N : PTm n) : PTm n := pairT C (pairT z N)
def coefficientBody : PTm 2 := qsub
  (ap3 paddedF (fstT (var 1)) (sndT (sndT (var 1))) (var 0))
  (qmul (ap3 delayedF (fstT (var 1)) (sndT (sndT (var 1))) (var 0)) (fstT (sndT (var 1))))
def linear (C z N : PTm n) : PTm n := sequence coefficientBody (succ N) (data C z N)

ipra_subst data
ipra_subst linear

theorem coefficientBody_at (C z N i : PTm n) : Γ ⊢[PRAAx] inst2 coefficientBody i (data C z N) ≐ coefficient C z N i := by
  simp only [coefficientBody,inst2,GaussianRationalMetric.subst_qsub,GaussianRationalHorner.subst_qmul,
    subst_ap3,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have Cfield : Γ ⊢[PRAAx] fstT (data C z N) ≐ C := fst_pair _ _
  have Nfield : Γ ⊢[PRAAx] sndT (sndT (data C z N)) ≐ N := (snd_pair _ _).sndE
  have zfield : Γ ⊢[PRAAx] fstT (sndT (data C z N)) ≐ z := (snd_pair _ _).fstE
  exact qsub_congr ((congrAp3 paddedF Cfield Nfield (.eqRefl _)).eqTrans (padded_at C N i))
    (qmul_congr ((congrAp3 delayedF Cfield Nfield (.eqRefl _)).eqTrans (delayed_at C N i)) zfield)

theorem linear_length (C z N : PTm n) : Γ ⊢[PRAAx] length (linear C z N) ≐ succ N := sequence_length _ _ _
theorem linear_lookup (C z N i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    entry (linear C z N) i ≐ coefficient C z N i :=
  (sequence_decode coefficientBody ((succ_monus_succ _ _).eqTrans hi)).eqTrans (coefficientBody_at C z N i)

theorem padded_canonical (C N i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ N)
    (hcanon : Γ ⊢[PRAAx] canonicalCoefficients C) : Γ ⊢[PRAAx] canonical (padded C N i) := by
  refine .orE (lt_or_le i N) ?_ ?_
  · exact GaussianRationalHorner.canonical_congr (padded_inside C N i Prf.hyp0)
      (GaussianRationalSyntheticDivision.canonical_coefficient_at C i hcanon.wk
        (lt_congr (.eqRefl _) hC.wk.eqSymm Prf.hyp0))
  · exact GaussianRationalHorner.canonical_congr (padded_outside C N i Prf.hyp0)
      GaussianRationalSyntheticDivision.qzero_canonical

theorem linear_canonical (C z N : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (linear C z N) := by
  refine .allI (.impI ?_)
  have len := linear_length (Γ := Γ.map Fm.shift) (Syn.shift C) (Syn.shift z) (Syn.shift N)
  have hi : (lt (var 0) (length (Syn.shift (linear C z N))) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) := by
    have h : (lt (var 0) (length (Syn.shift (linear C z N))) :: Γ.map Fm.shift) ⊢[PRAAx]
        lt (var 0) (length (linear (Syn.shift C) (Syn.shift z) (Syn.shift N))) := by
      simpa only [Syn.shift,subst_linear] using Prf.hyp0
    exact (succ_monus_succ _ _).eqSymm.eqTrans (lt_congr (.eqRefl _) len.wk h)
  have guard := GaussianRationalHorner.canonical_congr
    (linear_lookup (Syn.shift C) (Syn.shift z) (Syn.shift N) (var 0) hi)
    (GaussianRationalMetric.qsub_canonical (padded (Syn.shift C) (Syn.shift N) (var 0))
      (qmul (delayed (Syn.shift C) (Syn.shift N) (var 0)) (Syn.shift z)))
  simpa only [Syn.shift,subst_linear] using guard

/-- A field-group cancellation law for the actual canonical operations.
The common denominator is computed from the two actual inputs. -/
theorem add_sub_right (a c : PTm n) (hc : Γ ⊢[PRAAx] canonical c) : Γ ⊢[PRAAx] qadd a (qsub c a) ≐ c := by
  let E := rawDen a*rawDen c
  have hE : Γ ⊢[PRAAx] le one E := GaussianRationalHorner.positive_product _ _ (raw_den_positive a) (raw_den_positive c)
  have ha := GaussianRationalHorner.represents_rescale (Γ := Γ) a (rawGaussian a) (rawDen a) (rawDen c) (raw_represents a)
  have hcv := GaussianRationalSyntheticDivision.rescale_to c (rawGaussian c) (rawDen c) (rawDen a) E
    (raw_represents (Γ := Γ) c) (mul_comm _ _)
  have sub := GaussianRationalMetric.qsub_represents _ _ _ _ E hE hcv ha
  have result := GaussianRationalHorner.qadd_represents _ _ _ _ E hE ha sub
  apply GaussianRationalHorner.canonical_unique _ c _ E (GaussianRationalHorner.qadd_canonical _ _) hc hE (hrv := hcv)
  apply GaussianRationalHorner.represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := result)
  apply GaussianRootAlgebra.equal_of_values
  · simp only [GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_sub]
    ring
  · simp only [GaussianRootAlgebra.im_add,GaussianRootAlgebra.im_sub]
    ring

/-- At the new factor root, the actual Horner prefixes telescope to the
original coefficients. The proof handles N=0 without a special trace. -/
theorem root_prefix_zero (C z N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ N)
    (hcanon : Γ ⊢[PRAAx] canonicalCoefficients C) : Γ ⊢[PRAAx]
    horner (linear C z N) z (succ zero) ≐ padded C N zero := by
  have e := (GaussianRationalHorner.horner_succ (Γ := Γ) (linear C z N) z zero).eqTrans
    (qadd_congr (qmul_congr (GaussianRationalHorner.horner_zero _ _) (.eqRefl _))
      (linear_lookup C z N zero (zero_le _)))
  have coeff : Γ ⊢[PRAAx] coefficient C z N zero ≐ qsub (padded C N zero) (qmul qzero z) :=
    qsub_congr (.eqRefl _) (qmul_congr (delayed_zero C N) (.eqRefl _))
  exact e.eqTrans ((qadd_congr (.eqRefl _) coeff).eqTrans
    (add_sub_right _ _ (padded_canonical C N zero hC hcanon)))

theorem root_prefix_step (C z N k : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ N)
    (hcanon : Γ ⊢[PRAAx] canonicalCoefficients C) (hk : Γ ⊢[PRAAx] le (succ k) N)
    (ih : Γ ⊢[PRAAx] horner (linear C z N) z (succ k) ≐ padded C N k) : Γ ⊢[PRAAx]
    horner (linear C z N) z (succ (succ k)) ≐ padded C N (succ k) := by
  have coeff : Γ ⊢[PRAAx] coefficient C z N (succ k) ≐
      qsub (padded C N (succ k)) (qmul (padded C N k) z) :=
    qsub_congr (.eqRefl _) (qmul_congr (delayed_succ C N k) (.eqRefl _))
  exact (GaussianRationalHorner.horner_succ (linear C z N) z (succ k)).eqTrans
    ((qadd_congr (qmul_congr ih (.eqRefl _)) ((linear_lookup C z N (succ k) hk).eqTrans coeff)).eqTrans
      (add_sub_right _ _ (padded_canonical C N (succ k) hC hcanon)))

theorem root_prefix (C z N k : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ N)
    (hcanon : Γ ⊢[PRAAx] canonicalCoefficients C) (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    horner (linear C z N) z (succ k) ≐ padded C N k := by
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift N) ⟶
      (horner (linear (Syn.shift C) (Syn.shift z) (Syn.shift N)) (Syn.shift z) (succ (var 0)) ≐
        padded (Syn.shift C) (Syn.shift N) (var 0))) := by
    ipra_qfind (⟨le_QF _ _,trivial⟩) [subst_le, GaussianRationalHorner.subst_horner, subst_linear, subst_padded]
    · exact .impI (root_prefix_zero C z N hC hcanon).wk
    · refine .impI ?_
      let IH := le (var 0) (Syn.shift N) ⟶
        (horner (linear (Syn.shift C) (Syn.shift z) (Syn.shift N)) (Syn.shift z) (succ (var 0)) ≐
          padded (Syn.shift C) (Syn.shift N) (var 0))
      let Δ := le (succ (var 0)) (Syn.shift N) :: IH :: Γ.map Fm.shift
      have shape : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ Syn.shift N := by
        simpa only [Fm.shift,Fm.subst_eq,subst_length,Syn.shift] using hC.shift
      have canon : Γ.map Fm.shift ⊢[PRAAx] canonicalCoefficients (Syn.shift C) := by
        simpa only [Fm.shift,GaussianRationalSyntheticDivision.subst_canonicalCoefficients,Syn.shift] using hcanon.shift
      have ih : Δ ⊢[PRAAx] horner (linear (Syn.shift C) (Syn.shift z) (Syn.shift N)) (Syn.shift z) (succ (var 0)) ≐
          padded (Syn.shift C) (Syn.shift N) (var 0) := .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      exact root_prefix_step _ _ _ _ shape.wk.wk canon.wk.wk Prf.hyp0 ih
  have inst : Γ ⊢[PRAAx] le k N ⟶ (horner (linear C z N) z (succ k) ≐ padded C N k) := by
    simpa only [Fm.subst_imp,Fm.subst_eq,subst_le,GaussianRationalHorner.subst_horner,
      subst_linear,subst_padded,ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE inst hk

/-- Extensionality of actual Horner programs from in-range literal entries;
no extensionality of arbitrary outer sequence encodings is assumed. -/
theorem horner_ext (C D y N k : PTm n)
    (h : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift N) ⟶ entry (Syn.shift C) (var 0) ≐ entry (Syn.shift D) (var 0)))
    (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx] horner C y k ≐ horner D y k := by
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift N) ⟶
      (horner (Syn.shift C) (Syn.shift y) (var 0) ≐ horner (Syn.shift D) (Syn.shift y) (var 0))) := by
    ipra_qfind (⟨le_QF _ _,trivial⟩) [subst_le, GaussianRationalHorner.subst_horner]
    · exact .impI ((GaussianRationalHorner.horner_zero C y).eqTrans (GaussianRationalHorner.horner_zero D y).eqSymm)
    · refine .impI ?_
      let IH := le (var 0) (Syn.shift N) ⟶
        (horner (Syn.shift C) (Syn.shift y) (var 0) ≐ horner (Syn.shift D) (Syn.shift y) (var 0))
      let Δ := le (succ (var 0)) (Syn.shift N) :: IH :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] horner (Syn.shift C) (Syn.shift y) (var 0) ≐ horner (Syn.shift D) (Syn.shift y) (var 0) :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      have coefficient : Δ ⊢[PRAAx] entry (Syn.shift C) (var 0) ≐ entry (Syn.shift D) (var 0) :=
        .impE h.allOpen.wk.wk Prf.hyp0
      exact (GaussianRationalHorner.horner_succ _ _ _).eqTrans
        ((qadd_congr (qmul_congr ih (.eqRefl _)) coefficient).eqTrans
          (GaussianRationalHorner.horner_succ _ _ _).eqSymm)
  have inst : Γ ⊢[PRAAx] le k N ⟶ (horner C y k ≐ horner D y k) := by
    simpa only [Fm.subst_imp,Fm.subst_eq,subst_le,GaussianRationalHorner.subst_horner,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE inst hk

theorem inverse_entries (C z N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ N)
    (hcanon : Γ ⊢[PRAAx] canonicalCoefficients C) : Γ ⊢[PRAAx]
    .all (lt (var 0) (Syn.shift N) ⟶
      entry (GaussianRationalSyntheticDivision.quotient (linear (Syn.shift C) (Syn.shift z) (Syn.shift N)) (Syn.shift z) (Syn.shift N)) (var 0) ≐
        entry (Syn.shift C) (var 0)) := by
  refine .allI (.impI ?_)
  have shape : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ Syn.shift N := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,Syn.shift] using hC.shift
  have canon : Γ.map Fm.shift ⊢[PRAAx] canonicalCoefficients (Syn.shift C) := by
    simpa only [Fm.shift,GaussianRationalSyntheticDivision.subst_canonicalCoefficients,Syn.shift] using hcanon.shift
  exact (GaussianRationalSyntheticDivision.quotient_lookup _ _ _ _ Prf.hyp0).eqTrans
    ((root_prefix _ _ _ _ shape.wk canon.wk (le_trans (le_succ_self _) Prf.hyp0)).eqTrans
      (padded_inside _ _ _ Prf.hyp0))

theorem inverse_evaluation (C z y N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ N)
    (hcanon : Γ ⊢[PRAAx] canonicalCoefficients C) : Γ ⊢[PRAAx]
    evaluate (GaussianRationalSyntheticDivision.quotient (linear C z N) z N) y ≐ evaluate C y := by
  have entries : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift N) ⟶
      entry (Syn.shift (GaussianRationalSyntheticDivision.quotient (linear C z N) z N)) (var 0) ≐ entry (Syn.shift C) (var 0)) := by
    simpa only [Syn.shift,GaussianRationalSyntheticDivision.subst_quotient,subst_linear] using inverse_entries C z N hC hcanon
  exact (congrAp3 GaussianRationalHorner.hornerF (GaussianRationalSyntheticDivision.quotient_length _ _ _) (.eqRefl _) (.eqRefl _)).eqTrans
    ((horner_ext _ _ _ _ _ entries (le_refl N)).eqTrans
      (congrAp3 GaussianRationalHorner.hornerF hC.eqSymm (.eqRefl _) (.eqRefl _)))

theorem zero_remainder (C z N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ N)
    (hcanon : Γ ⊢[PRAAx] canonicalCoefficients C) : Γ ⊢[PRAAx] evaluate (linear C z N) z ≐ qzero :=
  (congrAp3 GaussianRationalHorner.hornerF (linear_length C z N) (.eqRefl _) (.eqRefl _)).eqTrans
    ((root_prefix C z N N hC hcanon (le_refl _)).eqTrans (padded_outside C N N (le_refl _)))

theorem qadd_commutative (a b : PTm n) : Γ ⊢[PRAAx] qadd a b ≐ qadd b a :=
  congrPairT (RationalAlgebra.add_commutative _ _) (RationalAlgebra.add_commutative _ _)

theorem qadd_zero_right (a : PTm n) (ha : Γ ⊢[PRAAx] canonical a) : Γ ⊢[PRAAx] qadd a qzero ≐ a :=
  (qadd_commutative a qzero).eqTrans (GaussianRationalSyntheticDivision.qzero_add a ha)

/-- The actual constructed coefficient list evaluates to (y-z)C(y), at
arbitrary internal degree and with the zero-length polynomial included. -/
theorem linear_evaluation (C z y N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ N)
    (hcanon : Γ ⊢[PRAAx] canonicalCoefficients C) : Γ ⊢[PRAAx]
    evaluate (linear C z N) y ≐ qmul (qsub y z) (evaluate C y) :=
  (GaussianRationalSyntheticDivision.division_evaluation (linear C z N) z y N (linear_length C z N)).eqTrans
    ((qadd_congr (qmul_congr (.eqRefl _) (inverse_evaluation C z y N hC hcanon)) (zero_remainder C z N hC hcanon)).eqTrans
      (qadd_zero_right _ (GaussianRationalHorner.qmul_canonical _ _)))

/-! ## Exact actual finite norms of the padded and delayed coefficients -/

theorem scalar_zero_code : Γ ⊢[PRAAx] natCode zero ≐ RationalIntegerNormalization.integerCode (ZT.natLit 0) := by
  apply RationalIntegerNormalization.normalize_integer _ _ _ (le_refl one)
  ipra_lc

theorem scalar_add_zero (a : PTm n) (ha : Γ ⊢[PRAAx] RationalNormalForm.wellFormed a) : Γ ⊢[PRAAx]
    add a (natCode zero) ≐ a := by
  have rep := RationalRepresentations.represents_add (Γ := Γ) a (natCode zero) _ _ _ _
    (RationalRepresentations.represents_self a) (natCode_represents zero)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _) ha rep
    (RationalRepresentations.represents_self a)
    (RationalAlgebra.positive_product (RationalArgmin.denominator_positive a) (le_refl one))
    (RationalArgmin.denominator_positive a)
  ipra_lc

theorem scalar_zero_add (a : PTm n) (ha : Γ ⊢[PRAAx] RationalNormalForm.wellFormed a) : Γ ⊢[PRAAx]
    add (natCode zero) a ≐ a := (RationalAlgebra.add_commutative _ _).eqTrans (scalar_add_zero a ha)

theorem scalar_multiply_one (a : PTm n) (ha : Γ ⊢[PRAAx] RationalNormalForm.wellFormed a) : Γ ⊢[PRAAx]
    multiply a (natCode one) ≐ a := by
  have rep := RationalRepresentations.represents_multiply (Γ := Γ) a (natCode one) _ _ _ _
    (RationalRepresentations.represents_self a) (natCode_represents one)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.multiply_guard _ _) ha rep
    (RationalRepresentations.represents_self a)
    (RationalAlgebra.positive_product (RationalArgmin.denominator_positive a) (le_refl one))
    (RationalArgmin.denominator_positive a)
  ipra_lc

theorem qzero_norm : Γ ⊢[PRAAx] qL1 (qzero : PTm n) ≐ natCode zero := by
  have rep := GaussianRationalL1.qL1_represents (Γ := Γ) qzero ComplexLogarithmRemainder.zeroCode one (le_refl _)
    (GaussianRationalHorner.zero_represents _)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (GaussianRationalL1.qL1_guard _)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one)) rep (natCode_represents zero) (le_refl _) (le_refl _)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  rw [natEq (GaussianL1.norm1_zero (Γ := Γ) (n := n))]

def padNormBody : PTm 2 := qL1 (ap3 paddedF (fstT (var 1)) (sndT (var 1)) (var 0))
def delayNormBody : PTm 2 := qL1 (ap3 delayedF (fstT (var 1)) (sndT (var 1)) (var 0))
def padSum (C N k : PTm n) : PTm n := RationalFiniteSum.sum padNormBody k (pairT C N)
def delaySum (C N k : PTm n) : PTm n := RationalFiniteSum.sum delayNormBody k (pairT C N)

ipra_subst padSum
ipra_subst delaySum

theorem pad_norm_at (C N i : PTm n) : Γ ⊢[PRAAx]
    RationalFiniteSum.term padNormBody i (pairT C N) ≐ qL1 (padded C N i) := by
  simp only [RationalFiniteSum.term,padNormBody,inst2,GaussianRationalL1.subst_qL1,
    subst_ap3,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact qL1_congr ((congrAp3 paddedF (fst_pair _ _) (snd_pair _ _) (.eqRefl _)).eqTrans (padded_at C N i))

theorem delay_norm_at (C N i : PTm n) : Γ ⊢[PRAAx]
    RationalFiniteSum.term delayNormBody i (pairT C N) ≐ qL1 (delayed C N i) := by
  simp only [RationalFiniteSum.term,delayNormBody,inst2,GaussianRationalL1.subst_qL1,
    subst_ap3,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact qL1_congr ((congrAp3 delayedF (fst_pair _ _) (snd_pair _ _) (.eqRefl _)).eqTrans (delayed_at C N i))

theorem pad_sum_zero (C N : PTm n) : Γ ⊢[PRAAx] padSum C N zero ≐ natCode zero :=
  (RationalFiniteSum.sum_zero _ _).eqTrans scalar_zero_code.eqSymm
theorem delay_sum_zero (C N : PTm n) : Γ ⊢[PRAAx] delaySum C N zero ≐ natCode zero :=
  (RationalFiniteSum.sum_zero _ _).eqTrans scalar_zero_code.eqSymm

theorem pad_sum_succ (C N k : PTm n) : Γ ⊢[PRAAx] padSum C N (succ k) ≐ add (padSum C N k) (qL1 (padded C N k)) :=
  (RationalFiniteSum.sum_succ _ _ _).eqTrans (RationalAlgebra.add_congr (.eqRefl _) (pad_norm_at C N k))
theorem delay_sum_succ (C N k : PTm n) : Γ ⊢[PRAAx] delaySum C N (succ k) ≐ add (delaySum C N k) (qL1 (delayed C N k)) :=
  (RationalFiniteSum.sum_succ _ _ _).eqTrans (RationalAlgebra.add_congr (.eqRefl _) (delay_norm_at C N k))

theorem rational_eq_of_code {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] rationalEq a b :=
  RationalArgmin.rationalEq_congr (.eqRefl _) h (.eqRefl _)

/-- In-range padded sums are literal canonical copies of the original
prefix norm; every summand equality is derived from the selector program. -/
theorem pad_sum_prefix (C N k : PTm n) (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    padSum C N k ≐ prefixNorm C k := by
  apply RationalFiniteSum.sum_ext
  refine .allI (.impI ?_)
  have bound : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift k) (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hk.shift
  have e := (pad_norm_at (Γ := lt (var 0) (Syn.shift k) :: Γ.map Fm.shift)
    (Syn.shift C) (Syn.shift N) (var 0)).eqTrans
      (qL1_congr (padded_inside _ _ _ (lt_of_lt_of_le Prf.hyp0 bound.wk)))
  simpa only [GaussianCoefficientL1.norm_body_at,Syn.shift,subst_pairT] using rational_eq_of_code e

theorem norm_length (C N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ N) : Γ ⊢[PRAAx] coefficientNorm C ≐ prefixNorm C N := by
  have e := congrAp2 (RationalFiniteSum.sumCodeF GaussianCoefficientL1.normBody) hC (.eqRefl C)
  exact (RationalFiniteSum.sum_at _ _ _).eqSymm.eqTrans (e.eqTrans (RationalFiniteSum.sum_at _ _ _))

theorem pad_total (C N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ N) : Γ ⊢[PRAAx]
    padSum C N (succ N) ≐ coefficientNorm C :=
  (pad_sum_succ C N N).eqTrans
    ((RationalAlgebra.add_congr (pad_sum_prefix C N N (le_refl _))
      ((qL1_congr (padded_outside C N N (le_refl _))).eqTrans qzero_norm)).eqTrans
        ((scalar_add_zero _ (RationalFiniteSum.sum_well_formed _ _ _)).eqTrans (norm_length C N hC).eqSymm))

/-- The actual delayed sum has a zero first summand and the exact shifted
prefix afterward. QF induction derives the equality at every runtime index. -/
theorem delayed_sum_shift (C N k : PTm n) : Γ ⊢[PRAAx] delaySum C N (succ k) ≐ padSum C N k := by
  have all : Γ ⊢[PRAAx] .all (delaySum (Syn.shift C) (Syn.shift N) (succ (var 0)) ≐
      padSum (Syn.shift C) (Syn.shift N) (var 0)) := by
    ipra_qfind [subst_delaySum, subst_padSum]
    · exact (delay_sum_succ C N zero).eqTrans
        ((RationalAlgebra.add_congr (delay_sum_zero C N)
          ((qL1_congr (delayed_zero C N)).eqTrans qzero_norm)).eqTrans
            ((scalar_add_zero _ (RationalNormalForm.normalize_well_formed _ _ (le_refl one))).eqTrans (pad_sum_zero C N).eqSymm))
    · exact (delay_sum_succ _ _ _).eqTrans
        ((RationalAlgebra.add_congr Prf.hyp0 (qL1_congr (delayed_succ _ _ _))).eqTrans
          (pad_sum_succ _ _ _).eqSymm)
  simpa only [Fm.subst_eq,subst_delaySum,subst_padSum,ConciseIPRA.PTm.subst_succ,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

theorem delay_total (C N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ N) : Γ ⊢[PRAAx]
    delaySum C N (succ N) ≐ coefficientNorm C :=
  (delayed_sum_shift C N N).eqTrans ((pad_sum_prefix C N N (le_refl _)).eqTrans (norm_length C N hC).eqSymm)

/-- Each actual new coefficient obeys the finite L1 triangle/product bound. -/
theorem coefficient_norm_bound (C z N i : PTm n) : Γ ⊢[PRAAx]
    rationalLE (qL1 (coefficient C z N i))
      (add (qL1 (padded C N i)) (multiply (qL1 z) (qL1 (delayed C N i)))) := by
  have product := GaussianRationalL1Algebra.qL1_multiply (Γ := Γ) (delayed C N i) z
  have product' := RationalArgmin.rationalLE_congr (.eqRefl _) (RationalAlgebra.multiply_commutative _ _) product
  exact RationalArgmin.transitive (GaussianRationalL1Algebra.qL1_sub _ _)
    (add_monotone _ _ _ _ (RationalArgmin.reflexive _) product')

def rightBody : PTm 2 := RationalSumAdditivity.addedBody padNormBody (RationalSumLinearity.scaledBody delayNormBody)
def rightData (C z N : PTm n) : PTm n := pairT (pairT C N) (pairT (qL1 z) (pairT C N))

ipra_subst rightData

theorem right_term_at (C z N i : PTm n) : Γ ⊢[PRAAx] RationalFiniteSum.term rightBody i (rightData C z N) ≐
    add (qL1 (padded C N i)) (multiply (qL1 z) (qL1 (delayed C N i))) :=
  (RationalSumAdditivity.added_term padNormBody (RationalSumLinearity.scaledBody delayNormBody)
    i (pairT C N) (pairT (qL1 z) (pairT C N))).eqTrans
      (RationalAlgebra.add_congr (pad_norm_at C N i)
        ((RationalSumLinearity.scaled_term delayNormBody i (qL1 z) (pairT C N)).eqTrans
          (RationalAlgebra.multiply_congr (.eqRefl _) (delay_norm_at C N i))))

theorem right_sum (C z N : PTm n) : Γ ⊢[PRAAx]
    RationalFiniteSum.sum rightBody (succ N) (rightData C z N) ≐
      add (padSum C N (succ N)) (multiply (qL1 z) (delaySum C N (succ N))) :=
  (RationalSumAdditivity.sum_additive padNormBody (RationalSumLinearity.scaledBody delayNormBody)
    (succ N) (pairT C N) (pairT (qL1 z) (pairT C N))).eqTrans
      (RationalAlgebra.add_congr (.eqRefl _)
        (RationalSumLinearity.sum_homogeneous delayNormBody (succ N) (qL1 z) (pairT C N)))

theorem scalar_factor (a S : PTm n) (hS : Γ ⊢[PRAAx] RationalNormalForm.wellFormed S) : Γ ⊢[PRAAx]
    add S (multiply a S) ≐ multiply (add (natCode one) a) S := by
  have e : Γ ⊢[PRAAx] multiply (add (natCode one) a) S ≐ add S (multiply a S) :=
    (RationalAlgebra.multiply_commutative _ _).eqTrans ((RationalAlgebra.multiply_add S (natCode one) a).eqTrans
      (RationalAlgebra.add_congr (scalar_multiply_one S hS) (RationalAlgebra.multiply_commutative _ _)))
  exact e.eqSymm

/-- The actual complete coefficient norm of the linear product is bounded
by (1+||z||1)||C||coef. The input only supplies its true stored length;
canonical input fractions, a common denominator or an output bound are not
hypotheses of this estimate. -/
theorem linear_norm_bound (C z N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ N) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (linear C z N))
      (multiply (add (natCode one) (qL1 z)) (coefficientNorm C)) := by
  have terms : Γ ⊢[PRAAx] RationalFiniteSum.termwiseLE GaussianCoefficientL1.normBody rightBody
      (succ N) (linear C z N) (rightData C z N) := by
    refine .allI (.impI ?_)
    have hi : (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
      (succ_monus_succ _ _).eqSymm.eqTrans (by simpa only [lt,le,Syn.shift,ConciseIPRA.PTm.subst_succ] using Prf.hyp0)
    have left := qL1_congr (linear_lookup (Syn.shift C) (Syn.shift z) (Syn.shift N) (var 0) hi)
    have right := right_term_at (Γ := lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift)
      (Syn.shift C) (Syn.shift z) (Syn.shift N) (var 0)
    have point := RationalArgmin.rationalLE_congr left.eqSymm right.eqSymm
      (coefficient_norm_bound (Syn.shift C) (Syn.shift z) (Syn.shift N) (var 0))
    simpa only [GaussianCoefficientL1.norm_body_at,Syn.shift,subst_linear,subst_rightData] using point
  have bound := RationalFiniteSum.sum_monotone _ _ _ _ _ terms
  have value : Γ ⊢[PRAAx] RationalFiniteSum.sum rightBody (succ N) (rightData C z N) ≐
      multiply (add (natCode one) (qL1 z)) (coefficientNorm C) :=
    (right_sum C z N).eqTrans ((RationalAlgebra.add_congr (pad_total C N hC)
      (RationalAlgebra.multiply_congr (.eqRefl _) (delay_total C N hC))).eqTrans
        (scalar_factor _ _ (norm_guard C)))
  exact RationalArgmin.rationalLE_congr (norm_length _ _ (linear_length C z N)).eqSymm value bound

/-! ## Actual program metadata and uniformly closed endpoints -/

def program (C z N : PTm n) : PTm n := pairT (linear C z N)
  (pairT (coefficientNorm (linear C z N)) (multiply (add (natCode one) (qL1 z)) (coefficientNorm C)))
def programF : PR 3 := PTm.toPR (program (var 0) (var 1) (var 2))

ipra_subst program

theorem program_at (C z N : PTm n) : Γ ⊢[PRAAx] ap3 programF C z N ≐ program C z N := by
  simpa only [programF,ap3,subst_program,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (program (var 0) (var 1) (var 2) : PTm 3) ![C,z,N]

theorem linear_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((length (linear (var 0) (var 1) (var 2)) ≐ succ (var 2)) ⋏
      (canonicalCoefficients (linear (var 0) (var 1) (var 2)) ⋏
        (le (var 3) (var 2) ⟶ entry (linear (var 0) (var 1) (var 2)) (var 3) ≐
          coefficient (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (.andI (linear_length _ _ _) (.andI (linear_canonical _ _ _)
    (.impI (linear_lookup _ _ _ _ Prf.hyp0))))

theorem linear_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ var 3 ⟶ canonicalCoefficients (var 0) ⟶
      evaluate (linear (var 0) (var 1) (var 3)) (var 2) ≐ qmul (qsub (var 2) (var 1)) (evaluate (var 0) (var 2))) :=
  closeUniv 4 (.impI (.impI (linear_evaluation _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem linear_norm_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ var 2 ⟶ rationalLE (coefficientNorm (linear (var 0) (var 1) (var 2)))
      (multiply (add (natCode one) (qL1 (var 1))) (coefficientNorm (var 0)))) :=
  closeUniv 3 (.impI (linear_norm_bound _ _ _ Prf.hyp0))

theorem padded_delayed_norms_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (length (var 0) ≐ var 1 ⟶
      ((padSum (var 0) (var 1) (succ (var 1)) ≐ coefficientNorm (var 0)) ⋏
        (delaySum (var 0) (var 1) (succ (var 1)) ≐ coefficientNorm (var 0)))) :=
  closeUniv 2 (.impI (.andI (pad_total _ _ Prf.hyp0) (delay_total _ _ Prf.hyp0)))

theorem linear_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 programF (var 0) (var 1) (var 2) ≐ program (var 0) (var 1) (var 2)) :=
  closeUniv 3 (program_at _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalLinearProduct
