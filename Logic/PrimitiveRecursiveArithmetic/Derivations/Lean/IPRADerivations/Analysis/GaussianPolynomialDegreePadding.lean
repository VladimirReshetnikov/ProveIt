import IPRADerivations.Analysis.GaussianGeneralPolynomialSamples
import IPRADerivations.Analysis.GaussianRationalPowerDifference
import IPRADerivations.Analysis.RationalArithmetic
import IPRADerivations.AnalyticNumberTheory.Totatives

/-!
# Actual leading-zero degree padding of general coefficient names

A fixed PR3 program retains the original numerical degree and data in a
pair. It returns the original raw coefficient through that degree and
literal Gaussian zero above it. Genuine coefficient-name coherence is
preserved at every internal upper degree, including zero.

When N<=P the actual descending P-sample has P-N leading zero entries,
then the actual original N-sample entries. Two guarded QF Horner-prefix
inductions prove exact evaluation equality. No equality of the outer list
codes, monicity, nonzero coefficient, or evaluation law is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialDegreePadding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.PTm (monus)
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero horner hornerF evaluate positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open LeanProofs.IPRA.Analysis.GaussianGeneralCoefficientNames (generalCN)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit unit_positive subst_unit)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qadd_congr qmul_congr qzero_canonical)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (N x : PTm n) : PTm n := pairT N x
def extension (a : PR 3) (i s N x : PTm n) : PTm n :=
  RationalArithmetic.select (sg (monus (succ N) i)) qzero (ap3 a i s x)
def extensionBody (a : PR 3) : PTm 3 :=
  extension a (var 0) (var 1) (fstT (var 2)) (sndT (var 2))
def extensionF (a : PR 3) : PR 3 := PTm.toPR (extensionBody a)
def padding (N P : PTm n) : PTm n := monus P N
def paddedSample (a : PR 3) (N P s x : PTm n) : PTm n :=
  GaussianGeneralPolynomialSamples.sample (extensionF a) P s (data N x)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (N x : PTm n) :
    Syn.subst σ (data N x) = data (Syn.subst σ N) (Syn.subst σ x) := by simp [data]
@[simp] theorem subst_extension {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (i s N x : PTm n) :
    Syn.subst σ (extension a i s N x) = extension a (Syn.subst σ i) (Syn.subst σ s)
      (Syn.subst σ N) (Syn.subst σ x) := by simp [extension,sg]
@[simp] theorem subst_padding {m : ℕ} (σ : Fin n → PTm m) (N P : PTm n) :
    Syn.subst σ (padding N P) = padding (Syn.subst σ N) (Syn.subst σ P) := by simp [padding]
@[simp] theorem subst_paddedSample {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N P s x : PTm n) :
    Syn.subst σ (paddedSample a N P s x) = paddedSample a (Syn.subst σ N)
      (Syn.subst σ P) (Syn.subst σ s) (Syn.subst σ x) := by simp [paddedSample]

theorem extension_at (a : PR 3) (i s N x : PTm n) : Γ ⊢[PRAAx]
    ap3 (extensionF a) i s (data N x) ≐ extension a i s N x := by
  have bit := congrMonus (Γ := Γ) (.eqRefl one)
    (congrMonus (.eqRefl one) (congrMonus (congrSucc (fst_pair N x)) (.eqRefl i)))
  have value := congrAp3 (Γ := Γ) a (.eqRefl i) (.eqRefl s) (snd_pair N x)
  have fields : Γ ⊢[PRAAx] extension a i s (fstT (data N x)) (sndT (data N x)) ≐ extension a i s N x := by
    exact congrAdd (congrMul bit value) (congrMul (congrMonus (.eqRefl one) bit) (.eqRefl qzero))
  have compiled := toPR_eq (Γ := Γ) (extensionBody a) ![i,s,data N x]
  have body : Syn.subst ![i,s,data N x] (extensionBody a) =
      extension a i s (fstT (data N x)) (sndT (data N x)) := by simp [extensionBody]
  rw [body] at compiled
  exact compiled.eqTrans fields

theorem extension_inside (a : PR 3) (i s N x : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    extension a i s N x ≐ ap3 a i s x :=
  RationalArithmetic.select_one _ _ _
    (AnalyticNumberTheory.Totatives.sg_lt ((succ_monus_succ _ _).eqTrans hi))

theorem extension_outside (a : PR 3) (i s N x : PTm n) (hi : Γ ⊢[PRAAx] le (succ N) i) : Γ ⊢[PRAAx]
    extension a i s N x ≐ qzero := RationalArithmetic.select_zero _ _ _ (AnalyticNumberTheory.Totatives.sg_le hi)

theorem extension_inside_at (a : PR 3) (i s N x : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    ap3 (extensionF a) i s (data N x) ≐ ap3 a i s x :=
  (extension_at a i s N x).eqTrans (extension_inside a i s N x hi)
theorem extension_outside_at (a : PR 3) (i s N x : PTm n) (hi : Γ ⊢[PRAAx] le (succ N) i) : Γ ⊢[PRAAx]
    ap3 (extensionF a) i s (data N x) ≐ qzero :=
  (extension_at a i s N x).eqTrans (extension_outside a i s N x hi)

theorem extension_coherence (a : PR 3) (N x i s t : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) : Γ ⊢[PRAAx]
    distanceBounded (ap3 (extensionF a) i s (data N x)) (ap3 (extensionF a) i t (data N x))
      (unit s+unit t) (unit s*unit t) := by
  refine .orE (lt_or_le i (succ N)) ?_ ?_
  · have hi : (lt i (succ N) :: Γ) ⊢[PRAAx] le i N := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
    exact distance_congr (extension_inside_at a i s N x hi).eqSymm
      (extension_inside_at a i t N x hi).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianGeneralCoefficientNames.coherence a N i s t x hCN.wk hi)
  · have pos := positive_product (Γ := le (succ N) i :: Γ) _ _ (unit_positive s) (unit_positive t)
    have zero := distance_radius_mono _ _ zero (unit s*unit t) (unit s+unit t) (unit s*unit t) pos pos
      (le_of_eq_add (d := (unit s+unit t)*(unit s*unit t)) (by ipra_ring))
      (GaussianRationalPowerDifference.distance_refl_zero qzero _ pos)
    exact distance_congr (extension_outside_at a i s N x Prf.hyp0).eqSymm
      (extension_outside_at a i t N x Prf.hyp0).eqSymm (.eqRefl _) (.eqRefl _) zero

/-- Every runtime target degree is allowed; coherence itself requires no N<=P. -/
theorem extended_generalCN (a : PR 3) (N P x : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) : Γ ⊢[PRAAx] generalCN (extensionF a) P (data N x) := by
  have hs : ((Γ.map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      generalCN a (Syn.shift (Syn.shift (Syn.shift N))) (Syn.shift (Syn.shift (Syn.shift x))) := by
    simpa only [Fm.shift,GaussianGeneralCoefficientNames.subst_generalCN,Syn.shift] using hCN.shift.shift.shift
  refine .allI (.impI (.allI (.allI ?_)))
  simpa [generalCN,GaussianCoefficientNameBounds.CN,GaussianCoefficientNameBounds.regularCoefficient,Syn.shift] using
    (extension_coherence a (Syn.shift (Syn.shift (Syn.shift N))) (Syn.shift (Syn.shift (Syn.shift x)))
      (var 2) (var 1) (var 0) hs).wk

theorem padding_sum (N P : PTm n) (hNP : Γ ⊢[PRAAx] le N P) : Γ ⊢[PRAAx] P ≐ N+padding N P := eq_add_of_le hNP

theorem leading_degree (N P i : PTm n) (hNP : Γ ⊢[PRAAx] le N P)
    (hi : Γ ⊢[PRAAx] lt i (padding N P)) : Γ ⊢[PRAAx] le (succ N) (monus P i) := by
  have ip := le_trans (le_of_lt hi) (GaussianMonicResidualRadius.monus_le_left P N)
  have hp := natEq (padding_sum N P hNP)
  have hd := natEq (eq_add_of_le hi)
  have ei := natEq (eq_add_of_le ip)
  apply le_of_eq_add (d := monus (padding N P) (succ i))
  apply deriveNat
  ipra_simps
  linear_combination hp+hd-ei

theorem tail_degree (N P j : PTm n) (hNP : Γ ⊢[PRAAx] le N P) : Γ ⊢[PRAAx]
    monus P (padding N P+j) ≐ monus N j :=
  (congrMonus (padding_sum N P hNP) (add_comm (padding N P) j)).eqTrans (monus_add_add N j (padding N P))

theorem tail_index (N P j : PTm n) (hNP : Γ ⊢[PRAAx] le N P) (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    le (padding N P+j) P :=
  le_congr (.eqRefl _) ((add_comm (padding N P) N).eqTrans (padding_sum N P hNP).eqSymm)
    (add_le_add₂ (le_refl (padding N P)) hj)

theorem padded_length (a : PR 3) (N P s x : PTm n) : Γ ⊢[PRAAx] length (paddedSample a N P s x) ≐ succ P :=
  GaussianGeneralPolynomialSamples.sample_length _ _ _ _

theorem padded_leading_entry (a : PR 3) (N P s x i : PTm n) (hNP : Γ ⊢[PRAAx] le N P)
    (hi : Γ ⊢[PRAAx] lt i (padding N P)) : Γ ⊢[PRAAx] entry (paddedSample a N P s x) i ≐ qzero :=
  (GaussianGeneralPolynomialSamples.sample_lookup (extensionF a) P s (data N x) i
    (le_trans (le_of_lt hi) (GaussianMonicResidualRadius.monus_le_left P N))).eqTrans
      (extension_outside_at a _ s N x (leading_degree N P i hNP hi))

theorem padded_tail_entry (a : PR 3) (N P s x j : PTm n) (hNP : Γ ⊢[PRAAx] le N P)
    (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    entry (paddedSample a N P s x) (padding N P+j) ≐ entry (GaussianGeneralPolynomialSamples.sample a N s x) j := by
  have hd := tail_degree (Γ := Γ) N P j hNP
  have bound := le_congr hd.eqSymm (.eqRefl _) (GaussianMonicResidualRadius.monus_le_left N j)
  exact (GaussianGeneralPolynomialSamples.sample_lookup (extensionF a) P s (data N x) _ (tail_index N P j hNP hj)).eqTrans
    ((extension_inside_at a _ s N x bound).eqTrans
      ((congrAp3 a hd (.eqRefl _) (.eqRefl _)).eqTrans
        (GaussianGeneralPolynomialSamples.sample_lookup a N s x j hj).eqSymm))

def leadingLaw (a : PR 3) (N P s x z r : PTm n) : Fm PTm n :=
  le r (padding N P) ⟶ horner (paddedSample a N P s x) z r ≐ qzero
def tailLaw (a : PR 3) (N P s x z r : PTm n) : Fm PTm n :=
  le r (succ N) ⟶ horner (paddedSample a N P s x) z (padding N P+r) ≐
    horner (GaussianGeneralPolynomialSamples.sample a N s x) z r

@[simp] theorem subst_leadingLaw {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N P s x z r : PTm n) :
    (leadingLaw a N P s x z r).subst σ = leadingLaw a (Syn.subst σ N) (Syn.subst σ P)
      (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ z) (Syn.subst σ r) := by simp [leadingLaw]
@[simp] theorem subst_tailLaw {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N P s x z r : PTm n) :
    (tailLaw a N P s x z r).subst σ = tailLaw a (Syn.subst σ N) (Syn.subst σ P)
      (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ z) (Syn.subst σ r) := by simp [tailLaw]

theorem leading_prefix_step (a : PR 3) (N P s x z r : PTm n) (hNP : Γ ⊢[PRAAx] le N P)
    (hr : Γ ⊢[PRAAx] lt r (padding N P))
    (ih : Γ ⊢[PRAAx] horner (paddedSample a N P s x) z r ≐ qzero) : Γ ⊢[PRAAx]
    horner (paddedSample a N P s x) z (succ r) ≐ qzero :=
  (GaussianRationalHorner.horner_succ _ _ _).eqTrans
    ((qadd_congr ((qmul_congr ih (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left _))
      (padded_leading_entry a N P s x r hNP hr)).eqTrans
        (GaussianRationalSyntheticDivision.qzero_add qzero qzero_canonical))

theorem leading_prefix (a : PR 3) (N P s x z r : PTm n) (hNP : Γ ⊢[PRAAx] le N P)
    (hr : Γ ⊢[PRAAx] le r (padding N P)) : Γ ⊢[PRAAx]
    horner (paddedSample a N P s x) z r ≐ qzero := by
  have hn : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift N) (Syn.shift P) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hNP.shift
  have all : Γ ⊢[PRAAx] .all (leadingLaw a (Syn.shift N) (Syn.shift P) (Syn.shift s)
      (Syn.shift x) (Syn.shift z) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_leadingLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (GaussianRationalHorner.horner_zero _ _)
    · simp only [subst_leadingLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      exact leading_prefix_step a _ _ _ _ _ _ hn.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] leadingLaw a N P s x z r := by
    simpa only [subst_leadingLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r
  exact .impE rule hr

theorem tail_prefix_step (a : PR 3) (N P s x z r : PTm n) (hNP : Γ ⊢[PRAAx] le N P)
    (hr : Γ ⊢[PRAAx] le r N)
    (ih : Γ ⊢[PRAAx] horner (paddedSample a N P s x) z (padding N P+r) ≐
      horner (GaussianGeneralPolynomialSamples.sample a N s x) z r) : Γ ⊢[PRAAx]
    horner (paddedSample a N P s x) z (padding N P+succ r) ≐
      horner (GaussianGeneralPolynomialSamples.sample a N s x) z (succ r) :=
  (congrAp3 hornerF (by ipra_ring : Γ ⊢[PRAAx] padding N P+succ r ≐ succ (padding N P+r))
    (.eqRefl _) (.eqRefl _)).eqTrans
    ((GaussianRationalHorner.horner_succ _ _ _).eqTrans
      ((qadd_congr (qmul_congr ih (.eqRefl _)) (padded_tail_entry a N P s x r hNP hr)).eqTrans
        (GaussianRationalHorner.horner_succ _ _ _).eqSymm))

theorem padded_prefix (a : PR 3) (N P s x z r : PTm n) (hNP : Γ ⊢[PRAAx] le N P)
    (hr : Γ ⊢[PRAAx] le r (succ N)) : Γ ⊢[PRAAx]
    horner (paddedSample a N P s x) z (padding N P+r) ≐
      horner (GaussianGeneralPolynomialSamples.sample a N s x) z r := by
  have hn : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift N) (Syn.shift P) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hNP.shift
  have all : Γ ⊢[PRAAx] .all (tailLaw a (Syn.shift N) (Syn.shift P) (Syn.shift s)
      (Syn.shift x) (Syn.shift z) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_tailLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI ((congrAp3 hornerF (add_zero _) (.eqRefl _) (.eqRefl _)).eqTrans
        ((leading_prefix a N P s x z (padding N P) hNP (le_refl _)).eqTrans
          (GaussianRationalHorner.horner_zero _ _).eqSymm)).wk
    · simp only [subst_tailLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      exact tail_prefix_step a _ _ _ _ _ _ hn.wk.wk
        ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] tailLaw a N P s x z r := by
    simpa only [subst_tailLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r
  exact .impE rule hr

theorem padded_evaluation (a : PR 3) (N P s x z : PTm n) (hNP : Γ ⊢[PRAAx] le N P) : Γ ⊢[PRAAx]
    evaluate (paddedSample a N P s x) z ≐ evaluate (GaussianGeneralPolynomialSamples.sample a N s x) z := by
  have count : Γ ⊢[PRAAx] succ P ≐ padding N P+succ N := by
    have e := natEq (padding_sum N P hNP)
    apply deriveNat
    ipra_simps
    linear_combination e
  exact (congrAp3 hornerF (padded_length a N P s x) (.eqRefl _) (.eqRefl _)).eqTrans
    ((congrAp3 hornerF count (.eqRefl _) (.eqRefl _)).eqTrans
      ((padded_prefix a N P s x z (succ N) hNP (le_refl _)).eqTrans
        (congrAp3 hornerF (GaussianGeneralPolynomialSamples.sample_length a N s x).eqSymm (.eqRefl _) (.eqRefl _))))

theorem degree_extension_program_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (ap3 (extensionF a) (var 2) (var 3) (data (var 0) (var 1)) ≐ extension a (var 2) (var 3) (var 0) (var 1)) :=
  closeUniv 4 (extension_at _ _ _ _ _)

theorem degree_extension_branches_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le (var 2) (var 0) ⟶ ap3 (extensionF a) (var 2) (var 3) (data (var 0) (var 1)) ≐ ap3 a (var 2) (var 3) (var 1)) ⋏
    (le (succ (var 0)) (var 2) ⟶ ap3 (extensionF a) (var 2) (var 3) (data (var 0) (var 1)) ≐ qzero)) :=
  closeUniv 4 (.andI (.impI (extension_inside_at _ _ _ _ _ Prf.hyp0))
    (.impI (extension_outside_at _ _ _ _ _ Prf.hyp0)))

theorem extended_coefficient_names_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (generalCN a (var 0) (var 2) ⟶ generalCN (extensionF a) (var 1) (data (var 0) (var 2))) :=
  closeUniv 3 (.impI (extended_generalCN _ _ _ _ Prf.hyp0))

theorem leading_zero_horner_prefix_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 0) (var 1) ⟶ le (var 5) (padding (var 0) (var 1)) ⟶
      horner (paddedSample a (var 0) (var 1) (var 2) (var 3)) (var 4) (var 5) ≐ qzero) :=
  closeUniv 6 (.impI (.impI (leading_prefix _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_padded_horner_prefix_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 0) (var 1) ⟶ le (var 5) (succ (var 0)) ⟶
      horner (paddedSample a (var 0) (var 1) (var 2) (var 3)) (var 4) (padding (var 0) (var 1)+var 5) ≐
        horner (GaussianGeneralPolynomialSamples.sample a (var 0) (var 2) (var 3)) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (padded_prefix _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_degree_padding_evaluation_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 0) (var 1) ⟶ evaluate (paddedSample a (var 0) (var 1) (var 2) (var 3)) (var 4) ≐
      evaluate (GaussianGeneralPolynomialSamples.sample a (var 0) (var 2) (var 3)) (var 4)) :=
  closeUniv 5 (.impI (padded_evaluation _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianPolynomialDegreePadding
