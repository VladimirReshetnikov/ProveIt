import IPRADerivations.Analysis.GaussianRationalPolynomialBuffers
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.LinearCombination

/-!
# Runtime coefficient convolution for exact rational polynomials

The actual output is generated from bounded finite convolutions. Its Horner
value is proved from an actual stage recurrence, not supplied as a contract.
Both degrees, lists, query point and all convolution indices are numerical.
Leading zeros and raw original coefficient codes are allowed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPolynomialProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (qzero qadd qmul canonical horner hornerF evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qadd_congr qmul_congr qzero_canonical qmul_zero_left qmul_zero_right qzero_add canonicalCoefficients)
open LeanProofs.IPRA.Analysis.GaussianRationalLinearProduct
  (padded padded_inside padded_outside)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialBuffers
  (zeros zeros_lookup zeros_evaluation appendZero append_length append_lookup append_evaluation
    leftPad pad_length pad_lookup padCoefficient pad_coefficient_before pad_coefficient_after pad_evaluation
    added added_length added_lookup added_evaluation)
open LeanProofs.IPRA.Foundations.MasterCertificate
  (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The guard prevents truncated subtraction from introducing extra terms. -/
def contribution (P Q M k i : PTm n) : PTm n :=
  RationalArithmetic.select (Signum.sg (monus (succ k) i)) qzero
    (qmul (entry P i) (padded Q (succ M) (monus k i)))
def data (P Q M k : PTm n) : PTm n := pairT P (pairT Q (pairT M k))
def contributionBody : PTm 2 := contribution (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) (var 0)
def coefficient (P Q M t k : PTm n) : PTm n :=
  GaussianRationalFiniteSum.sum contributionBody t (data P Q M k)
def stageData (P Q M t : PTm n) : PTm n := pairT P (pairT Q (pairT M t))
def coefficientF : PR 5 := PTm.toPR (coefficient (var 0) (var 1) (var 2) (var 3) (var 4))
def stageBody : PTm 2 := PTm.app coefficientF ![fstT (var 1),fstT (sndT (var 1)),
  fstT (sndT (sndT (var 1))),sndT (sndT (sndT (var 1))),var 0]
def stage (P Q M t : PTm n) : PTm n := sequence stageBody (M+t) (stageData P Q M t)
def product (P Q N M : PTm n) : PTm n := stage P Q M (succ N)

@[simp] theorem subst_contribution {l : ℕ} (σ : Fin n → PTm l) (P Q M k i : PTm n) :
    Syn.subst σ (contribution P Q M k i) = contribution (Syn.subst σ P) (Syn.subst σ Q)
      (Syn.subst σ M) (Syn.subst σ k) (Syn.subst σ i) := by simp [contribution,Signum.sg]
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (P Q M k : PTm n) :
    Syn.subst σ (data P Q M k) = data (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ M) (Syn.subst σ k) := by simp [data]
@[simp] theorem subst_coefficient {l : ℕ} (σ : Fin n → PTm l) (P Q M t k : PTm n) :
    Syn.subst σ (coefficient P Q M t k) = coefficient (Syn.subst σ P) (Syn.subst σ Q)
      (Syn.subst σ M) (Syn.subst σ t) (Syn.subst σ k) := by simp [coefficient]
@[simp] theorem subst_stageData {l : ℕ} (σ : Fin n → PTm l) (P Q M t : PTm n) :
    Syn.subst σ (stageData P Q M t) = stageData (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ M) (Syn.subst σ t) := by simp [stageData]
@[simp] theorem subst_stage {l : ℕ} (σ : Fin n → PTm l) (P Q M t : PTm n) :
    Syn.subst σ (stage P Q M t) = stage (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ M) (Syn.subst σ t) := by simp [stage]
@[simp] theorem subst_product {l : ℕ} (σ : Fin n → PTm l) (P Q N M : PTm n) :
    Syn.subst σ (product P Q N M) = product (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ N) (Syn.subst σ M) := by simp [product]

theorem contribution_congr {P P' Q Q' M M' k k' i i' : PTm n}
    (hP : Γ ⊢[PRAAx] P ≐ P') (hQ : Γ ⊢[PRAAx] Q ≐ Q') (hM : Γ ⊢[PRAAx] M ≐ M')
    (hk : Γ ⊢[PRAAx] k ≐ k') (hi : Γ ⊢[PRAAx] i ≐ i') : Γ ⊢[PRAAx]
    contribution P Q M k i ≐ contribution P' Q' M' k' i' := by
  ipra_congr (contribution (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with [hP, hQ, hM, hk, hi]

theorem contribution_body_at (P Q M k i : PTm n) : Γ ⊢[PRAAx]
    inst2 contributionBody i (data P Q M k) ≐ contribution P Q M k i := by
  simp only [contributionBody,inst2,subst_contribution,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  have e := snd_pair (Γ := Γ) P (pairT Q (pairT M k))
  have f := (congrSnd e).eqTrans (snd_pair Q (pairT M k))
  exact contribution_congr (fst_pair _ _) ((congrFst e).eqTrans (fst_pair _ _))
    ((congrFst f).eqTrans (fst_pair _ _)) ((congrSnd f).eqTrans (snd_pair _ _)) (.eqRefl _)

theorem contribution_inside (P Q M k i : PTm n) (hi : Γ ⊢[PRAAx] le i k) : Γ ⊢[PRAAx]
    contribution P Q M k i ≐ qmul (entry P i) (padded Q (succ M) (monus k i)) :=
  RationalArithmetic.select_one _ _ _
    (AnalyticNumberTheory.Totatives.sg_lt ((succ_monus_succ _ _).eqTrans hi))

theorem contribution_outside (P Q M k i : PTm n) (hi : Γ ⊢[PRAAx] lt k i) : Γ ⊢[PRAAx]
    contribution P Q M k i ≐ qzero :=
  RationalArithmetic.select_zero _ _ _ (AnalyticNumberTheory.Totatives.sg_le hi)

theorem coefficient_canonical (P Q M t k : PTm n) : Γ ⊢[PRAAx] canonical (coefficient P Q M t k) :=
  GaussianRationalFiniteSum.sum_canonical _ _ _
theorem coefficient_zero (P Q M k : PTm n) : Γ ⊢[PRAAx] coefficient P Q M zero k ≐ qzero :=
  GaussianRationalFiniteSum.sum_zero _ _
theorem coefficient_succ (P Q M t k : PTm n) : Γ ⊢[PRAAx]
    coefficient P Q M (succ t) k ≐ qadd (coefficient P Q M t k) (contribution P Q M k t) :=
  (GaussianRationalFiniteSum.sum_succ _ _ _).eqTrans
    (qadd_congr (.eqRefl _) (contribution_body_at P Q M k t))

theorem coefficient_program (P Q M t k : PTm n) : Γ ⊢[PRAAx]
    PTm.app coefficientF ![P,Q,M,t,k] ≐ coefficient P Q M t k := by
  simpa [coefficientF] using toPR_eq (Γ := Γ)
    (coefficient (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![P,Q,M,t,k]

theorem stage_body_at (P Q M t k : PTm n) : Γ ⊢[PRAAx]
    inst2 stageBody k (stageData P Q M t) ≐ coefficient P Q M t k := by
  simp only [stageBody,inst2,ConciseIPRA.PTm.subst_app,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  have vector : (fun i => Syn.subst ![k,stageData P Q M t]
      ((![fstT (var 1),fstT (sndT (var 1)),fstT (sndT (sndT (var 1))),
        sndT (sndT (sndT (var 1))),var 0] : Fin 5 → PTm 2) i)) =
      ![fstT (stageData P Q M t),fstT (sndT (stageData P Q M t)),
        fstT (sndT (sndT (stageData P Q M t))),sndT (sndT (sndT (stageData P Q M t))),k] := by
    funext i
    fin_cases i <;> simp
  rw [vector]
  have e := snd_pair (Γ := Γ) P (pairT Q (pairT M t))
  have f := (congrSnd e).eqTrans (snd_pair Q (pairT M t))
  have h := congrApp (Γ := Γ) coefficientF (ts := ![fstT (stageData P Q M t),fstT (sndT (stageData P Q M t)),
      fstT (sndT (sndT (stageData P Q M t))),sndT (sndT (sndT (stageData P Q M t))),k])
    (us := ![P,Q,M,t,k]) (fun i => by
      fin_cases i
      · exact fst_pair _ _
      · exact (congrFst e).eqTrans (fst_pair _ _)
      · exact (congrFst f).eqTrans (fst_pair _ _)
      · exact (congrSnd f).eqTrans (snd_pair _ _)
      · exact .eqRefl _)
  exact h.eqTrans (coefficient_program P Q M t k)

theorem stage_length (P Q M t : PTm n) : Γ ⊢[PRAAx] length (stage P Q M t) ≐ M+t := sequence_length _ _ _
theorem stage_lookup (P Q M t k : PTm n) (hk : Γ ⊢[PRAAx] lt k (M+t)) : Γ ⊢[PRAAx]
    entry (stage P Q M t) k ≐ coefficient P Q M t k :=
  (sequence_decode stageBody hk).eqTrans (stage_body_at P Q M t k)

theorem product_length (P Q N M : PTm n) : Γ ⊢[PRAAx]
    length (product P Q N M) ≐ succ (N+M) := (stage_length P Q M (succ N)).eqTrans (by ipra_ring)

/-- The actual bounded convolution, with the original first-list length as
the finite summation bound and guarded subtraction in the second index. -/
theorem product_lookup (P Q N M k : PTm n) (hk : Γ ⊢[PRAAx] le k (N+M)) : Γ ⊢[PRAAx]
    entry (product P Q N M) k ≐ coefficient P Q M (succ N) k :=
  stage_lookup P Q M (succ N) k (le_congr (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] succ (N+M) ≐ M+succ N) ((succ_monus_succ _ _).eqTrans hk))

theorem stage_canonical (P Q M t : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (stage P Q M t) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift (stage P Q M t))) :: Γ.map Fm.shift
  have inputRange : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift (stage P Q M t))) := Prf.hyp0
  have bound : Δ ⊢[PRAAx] lt (var 0) (Syn.shift M+Syn.shift t) :=
    lt_congr (.eqRefl _) (stage_length (Syn.shift P) (Syn.shift Q) (Syn.shift M) (Syn.shift t))
      (by simpa only [Syn.shift,subst_stage] using inputRange)
  simpa only [Δ,Syn.shift,subst_stage] using GaussianRationalHorner.canonical_congr
    (stage_lookup (Syn.shift P) (Syn.shift Q) (Syn.shift M) (Syn.shift t) (var 0) bound)
    (coefficient_canonical _ _ _ _ _)

theorem product_canonical (P Q N M : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (product P Q N M) :=
  stage_canonical P Q M (succ N)

/-- Every old summand vanishes beyond its genuine degree-bound buffer. -/
theorem tail_index (M t k i : PTm n) (hk : Γ ⊢[PRAAx] le (M+t) k)
    (hi : Γ ⊢[PRAAx] lt i t) : Γ ⊢[PRAAx] le (succ M) (monus k i) := by
  have ik := le_trans (le_of_lt hi) (le_trans (le_add_left t M) hk)
  apply le_of_eq_add (d := monus t (succ i)+monus k (M+t))
  ipra_lc natEq (eq_add_of_le hk)+natEq (eq_add_of_le hi)-natEq (eq_add_of_le ik)

theorem contribution_after (P Q M t k i : PTm n) (hk : Γ ⊢[PRAAx] le (M+t) k)
    (hi : Γ ⊢[PRAAx] lt i t) : Γ ⊢[PRAAx] contribution P Q M k i ≐ qzero :=
  (contribution_inside P Q M k i (le_trans (le_of_lt hi) (le_trans (le_add_left t M) hk))).eqTrans
    ((qmul_congr (.eqRefl _) (padded_outside Q _ _ (tail_index M t k i hk hi))).eqTrans
      (qmul_zero_right _))

theorem constant_zero_sum (t x : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum (qzero : PTm 2) t x ≐ qzero := by
  have eqs : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual (qzero : PTm 2) qzero t x zero := by
    refine .allI (.impI ?_)
    simp only [inst2,GaussianRationalHorner.subst_qzero]
    exact .eqRefl _
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ eqs).eqTrans
    (GaussianRationalPolynomialBuffers.zeros_prefix t GaussianRationalSyntheticDivision.qone t (le_refl _))

theorem coefficient_after (P Q M t k : PTm n) (hk : Γ ⊢[PRAAx] le (M+t) k) : Γ ⊢[PRAAx]
    coefficient P Q M t k ≐ qzero := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift M+Syn.shift t) (Syn.shift k) := by
    simpa only [Fm.shift,subst_le,PTm.subst_add,Syn.shift] using hk.shift
  have eqs : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual contributionBody (qzero : PTm 2)
      t (data P Q M k) zero := by
    refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_data,inst2,GaussianRationalHorner.subst_qzero] using
      (contribution_body_at (Syn.shift P) (Syn.shift Q) (Syn.shift M) (Syn.shift k) (var 0)).eqTrans
        (contribution_after _ _ _ _ _ _ hs.wk Prf.hyp0)
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ eqs).eqTrans (constant_zero_sum _ _)

theorem stage_zero_evaluation (P Q M z : PTm n) : Γ ⊢[PRAAx]
    evaluate (stage P Q M zero) z ≐ qzero := by
  have entries : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift M) ⟶
      entry (Syn.shift (stage P Q M zero)) (var 0) ≐ entry (Syn.shift (zeros M)) (var 0)) := by
    refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_stage,GaussianRationalPolynomialBuffers.subst_zeros,ConciseIPRA.PTm.subst_zero,lt] using
      (stage_lookup (Syn.shift P) (Syn.shift Q) (Syn.shift M) zero (var 0)
        (le_congr (.eqRefl _) (add_zero _).eqSymm Prf.hyp0)).eqTrans
          ((coefficient_zero _ _ _ _).eqTrans (zeros_lookup _ _ Prf.hyp0).eqSymm)
  exact (congrAp3 hornerF ((stage_length P Q M zero).eqTrans (add_zero M)) (.eqRefl _) (.eqRefl _)).eqTrans
    ((GaussianRationalLinearProduct.horner_ext _ _ _ _ _ entries (le_refl M)).eqTrans
      ((congrAp3 hornerF (GaussianRationalPolynomialBuffers.zeros_length M).eqSymm (.eqRefl _) (.eqRefl _)).eqTrans
        (zeros_evaluation M z)))

theorem append_stage_lookup (P Q M t k : PTm n) (hk : Γ ⊢[PRAAx] le k (M+t)) : Γ ⊢[PRAAx]
    entry (appendZero (stage P Q M t)) k ≐ coefficient P Q M t k := by
  have start : Γ ⊢[PRAAx] entry (appendZero (stage P Q M t)) k ≐ padded (stage P Q M t) (M+t) k :=
    (append_lookup _ k (le_congr (.eqRefl _) (stage_length P Q M t).eqSymm hk)).eqTrans
      (GaussianRationalLinearProduct.padded_congr (.eqRefl _) (stage_length P Q M t) (.eqRefl _))
  refine .orE (lt_or_le k (M+t)) ?_ ?_
  · exact start.wk.eqTrans ((padded_inside _ _ _ Prf.hyp0).eqTrans (stage_lookup _ _ _ _ _ Prf.hyp0))
  · exact start.wk.eqTrans ((padded_outside _ _ _ Prf.hyp0).eqTrans (coefficient_after _ _ _ _ _ Prf.hyp0).eqSymm)

theorem subtract_index_bound (M t k : PTm n) (hk : Γ ⊢[PRAAx] lt k (M+succ t))
    (ht : Γ ⊢[PRAAx] le t k) : Γ ⊢[PRAAx] le (monus k t) M := by
  have upper : Γ ⊢[PRAAx] le k (M+t) := (succ_monus_succ k (M+t)).eqSymm.eqTrans
    (le_congr (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] M+succ t ≐ succ (M+t)) hk)
  have cross : Γ ⊢[PRAAx] le (monus k t+t) (M+t) :=
    le_congr ((eq_add_of_le ht).eqTrans (add_comm _ _)) (.eqRefl _) upper
  exact (monus_add_add _ _ t).eqSymm.eqTrans cross

theorem padded_scaled_lookup (P Q M t k : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ M)
    (hk : Γ ⊢[PRAAx] lt k (M+succ t)) : Γ ⊢[PRAAx]
    entry (leftPad (GaussianRationalCoefficientScaling.scaled Q (entry P t)) t) k ≐ contribution P Q M k t := by
  let S := GaussianRationalCoefficientScaling.scaled Q (entry P t)
  have slen : Γ ⊢[PRAAx] length S ≐ succ M := (GaussianRationalCoefficientScaling.scaled_length Q (entry P t)).eqTrans hQ
  have bound : Γ ⊢[PRAAx] lt k (t+length S) :=
    le_congr (.eqRefl _) ((by ipra_ring : Γ ⊢[PRAAx] M+succ t ≐ t+succ M).eqTrans
      (congrAdd (.eqRefl _) slen.eqSymm)) hk
  have start := pad_lookup S t k bound
  refine .orE (lt_or_le k t) ?_ ?_
  · exact start.wk.eqTrans ((pad_coefficient_before _ _ _ Prf.hyp0).eqTrans
      (contribution_outside P Q M k t Prf.hyp0).eqSymm)
  · have ik : (le t k :: Γ) ⊢[PRAAx] le (monus k t) M := subtract_index_bound M t k hk.wk Prf.hyp0
    have iq : (le t k :: Γ) ⊢[PRAAx] lt (monus k t) (length Q) :=
      le_congr (.eqRefl _) hQ.wk.eqSymm ((succ_monus_succ _ _).eqTrans ik)
    exact start.wk.eqTrans ((pad_coefficient_after _ _ _ Prf.hyp0).eqTrans
      ((GaussianRationalCoefficientScaling.scaled_lookup Q (entry P t) _ iq).eqTrans
        ((qmul_congr (.eqRefl _) (padded_inside Q (succ M) _ ((succ_monus_succ _ _).eqTrans ik)).eqSymm).eqTrans
          (contribution_inside P Q M k t Prf.hyp0).eqSymm)))

/-- A true generated-column recurrence for the finite convolutions. -/
theorem stage_step_evaluation (P Q M t z : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) : Γ ⊢[PRAAx]
    evaluate (stage P Q M (succ t)) z ≐
      qadd (qmul (evaluate (stage P Q M t) z) z) (qmul (entry P t) (evaluate Q z)) := by
  let A := appendZero (stage P Q M t)
  let B := leftPad (GaussianRationalCoefficientScaling.scaled Q (entry P t)) t
  let L := M+succ t
  have hA : Γ ⊢[PRAAx] length A ≐ L := (append_length _).eqTrans
    ((congrSucc (stage_length P Q M t)).eqTrans (by unfold L; ipra_ring))
  have hB : Γ ⊢[PRAAx] length B ≐ L := (pad_length _ _).eqTrans
    ((congrAdd (.eqRefl _) ((GaussianRationalCoefficientScaling.scaled_length _ _).eqTrans hQ)).eqTrans (by unfold L; ipra_ring))
  have hs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift Q) ≐ succ (Syn.shift M) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hQ.shift
  have entries : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift L) ⟶
      entry (Syn.shift (stage P Q M (succ t))) (var 0) ≐ entry (Syn.shift (added A B L)) (var 0)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift L) :: Γ.map Fm.shift
    have domain : Δ ⊢[PRAAx] lt (var 0) (Syn.shift M+succ (Syn.shift t)) := by
      simpa only [Δ,L,Syn.shift,PTm.subst_add,ConciseIPRA.PTm.subst_succ] using (Prf.hyp0 (Ax := PRAAx) (Γ := Γ.map Fm.shift) (φ := lt (var 0) (Syn.shift L)))
    have bound : Δ ⊢[PRAAx] le (var 0) (Syn.shift M+Syn.shift t) :=
      (succ_monus_succ _ _).eqSymm.eqTrans
        (le_congr (.eqRefl _) (by ipra_ring : Δ ⊢[PRAAx] Syn.shift M+succ (Syn.shift t) ≐ succ (Syn.shift M+Syn.shift t)) domain)
    simpa only [Δ,A,B,L,Syn.shift,subst_stage,GaussianRationalPolynomialBuffers.subst_appendZero,
      GaussianRationalPolynomialBuffers.subst_leftPad,GaussianRationalCoefficientScaling.subst_scaled,
      GaussianRationalPolynomialBuffers.subst_added,ConciseIPRA.PTm.subst_succ,PTm.subst_add,subst_entry] using
      (stage_lookup (Syn.shift P) (Syn.shift Q) (Syn.shift M) (succ (Syn.shift t)) (var 0) domain).eqTrans
        ((coefficient_succ _ _ _ _ _).eqTrans
          ((qadd_congr (append_stage_lookup _ _ _ _ _ bound).eqSymm
            (padded_scaled_lookup _ _ _ _ _ hs.wk domain).eqSymm).eqTrans
              (added_lookup _ _ _ _ Prf.hyp0).eqSymm))
  have compare : Γ ⊢[PRAAx] evaluate (stage P Q M (succ t)) z ≐ evaluate (added A B L) z := (congrAp3 hornerF (stage_length P Q M (succ t)) (.eqRefl _) (.eqRefl _)).eqTrans
    ((GaussianRationalLinearProduct.horner_ext _ _ _ _ _ entries (le_refl L)).eqTrans
      (congrAp3 hornerF (added_length A B L).eqSymm (.eqRefl _) (.eqRefl _)))
  exact compare.eqTrans ((added_evaluation A B L z hA hB).eqTrans
    (qadd_congr (append_evaluation _ z)
      ((pad_evaluation _ t z).eqTrans (GaussianRationalCoefficientScaling.evaluation_linearity Q (entry P t) z))))

def evaluationLaw (P Q M z t : PTm n) : Fm PTm n :=
  evaluate (stage P Q M t) z ≐ qmul (horner P z t) (evaluate Q z)
@[simp] theorem subst_evaluationLaw {l : ℕ} (σ : Fin n → PTm l) (P Q M z t : PTm n) :
    (evaluationLaw P Q M z t).subst σ = evaluationLaw (Syn.subst σ P) (Syn.subst σ Q)
      (Syn.subst σ M) (Syn.subst σ z) (Syn.subst σ t) := by simp [evaluationLaw]

theorem evaluation_step (P Q M z t : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ M)
    (ih : Γ ⊢[PRAAx] evaluationLaw P Q M z t) : Γ ⊢[PRAAx] evaluationLaw P Q M z (succ t) := by
  have shuffle : Γ ⊢[PRAAx] qmul (qmul (horner P z t) (evaluate Q z)) z ≐
      qmul (qmul (horner P z t) z) (evaluate Q z) :=
    (GaussianReciprocalHorner.qmul_associative _ _ _).eqTrans
      ((qmul_congr (.eqRefl _) (GaussianRationalPowerAlgebra.qmul_commutative _ _)).eqTrans
        (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm)
  exact (stage_step_evaluation P Q M t z hQ).eqTrans
    ((qadd_congr ((qmul_congr ih (.eqRefl _)).eqTrans shuffle) (.eqRefl _)).eqTrans
      ((GaussianRationalPolynomialBuffers.distribute_right _ _ _).eqSymm.eqTrans
        (qmul_congr (GaussianRationalHorner.horner_succ _ _ _).eqSymm (.eqRefl _))))

theorem stage_evaluation (P Q M z t : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) : Γ ⊢[PRAAx]
    evaluationLaw P Q M z t := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift Q) ≐ succ (Syn.shift M) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hQ.shift
  have all : Γ ⊢[PRAAx] .all (evaluationLaw (Syn.shift P) (Syn.shift Q) (Syn.shift M) (Syn.shift z) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_evaluationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (stage_zero_evaluation P Q M z).eqTrans
        ((qmul_congr (GaussianRationalHorner.horner_zero P z) (.eqRefl _)).eqTrans (qmul_zero_left _)).eqSymm
    · simp only [subst_evaluationLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact evaluation_step _ _ _ _ _ hs.wk Prf.hyp0
  simpa only [subst_evaluationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t

/-- Exact evaluator multiplication, with no supplied convolution,
factorization or arithmetic representation law. Zero degrees are included. -/
theorem product_evaluation (P Q N M z : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N)
    (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) : Γ ⊢[PRAAx]
    evaluate (product P Q N M) z ≐ qmul (evaluate P z) (evaluate Q z) :=
  (stage_evaluation P Q M z (succ N) hQ).eqTrans
    (qmul_congr (congrAp3 hornerF hP.eqSymm (.eqRefl _) (.eqRefl _)) (.eqRefl _))

/-! The same actual PR4 returns precisely these computed coefficients. -/
def productF : PR 4 := PTm.toPR (product (var 0) (var 1) (var 2) (var 3))
def run (P Q N M : PTm n) : PTm n := PTm.app productF ![P,Q,N,M]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (P Q N M : PTm n) :
    Syn.subst σ (run P Q N M) = run (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ N) (Syn.subst σ M) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (P Q N M : PTm n) : Γ ⊢[PRAAx] run P Q N M ≐ product P Q N M := by
  simpa [run,productF] using toPR_eq (Γ := Γ)
    (product (var 0) (var 1) (var 2) (var 3) : PTm 4) ![P,Q,N,M]
theorem returned_length (P Q N M : PTm n) : Γ ⊢[PRAAx]
    length (run P Q N M) ≐ succ (N+M) := (congrFst (program_at P Q N M)).eqTrans (product_length _ _ _ _)
theorem returned_canonical (P Q N M : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (run P Q N M) := by
  have p := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (canonicalCoefficients (var 0) : Fm PTm 1)
    ![product P Q N M] ![run P Q N M] (fun i => by fin_cases i; exact (program_at P Q N M).eqSymm)
    (by simpa using product_canonical (Γ := Γ) P Q N M)
  simpa using p
theorem returned_lookup (P Q N M k : PTm n) (hk : Γ ⊢[PRAAx] le k (N+M)) : Γ ⊢[PRAAx]
    entry (run P Q N M) k ≐ coefficient P Q M (succ N) k :=
  (entry_congr (program_at P Q N M) (.eqRefl _)).eqTrans (product_lookup P Q N M k hk)
theorem returned_evaluation (P Q N M z : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N)
    (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) : Γ ⊢[PRAAx]
    evaluate (run P Q N M) z ≐ qmul (evaluate P z) (evaluate Q z) :=
  (GaussianRationalHorner.evaluate_program_at (run P Q N M) z).eqSymm.eqTrans
    ((congrAp2 GaussianRationalHorner.evaluateF (program_at P Q N M) (.eqRefl _)).eqTrans
      ((GaussianRationalHorner.evaluate_program_at (product P Q N M) z).eqTrans
        (product_evaluation P Q N M z hP hQ)))

theorem actual_polynomial_product_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (product (var 0) (var 1) (var 2) (var 3)) ≐ succ (var 2+var 3)) :=
  closeUniv 4 (product_length _ _ _ _)
theorem actual_polynomial_product_canonical_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (canonicalCoefficients (product (var 0) (var 1) (var 2) (var 3))) := closeUniv 4 (product_canonical _ _ _ _)
theorem actual_polynomial_convolution_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 2+var 3) ⟶
      entry (product (var 0) (var 1) (var 2) (var 3)) (var 4) ≐
        coefficient (var 0) (var 1) (var 3) (succ (var 2)) (var 4)) :=
  closeUniv 5 (.impI (product_lookup _ _ _ _ _ Prf.hyp0))
theorem actual_polynomial_product_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 2) ⟶ length (var 1) ≐ succ (var 3) ⟶
      evaluate (product (var 0) (var 1) (var 2) (var 3)) (var 4) ≐
        qmul (evaluate (var 0) (var 4)) (evaluate (var 1) (var 4))) :=
  closeUniv 5 (.impI (.impI (product_evaluation _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_polynomial_product_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((run (var 0) (var 1) (var 2) (var 3) ≐ product (var 0) (var 1) (var 2) (var 3)) ⋏
      ((length (run (var 0) (var 1) (var 2) (var 3)) ≐ succ (var 2+var 3)) ⋏
        canonicalCoefficients (run (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (.andI (program_at _ _ _ _) (.andI (returned_length _ _ _ _) (returned_canonical _ _ _ _)))
theorem returned_polynomial_convolution_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 2+var 3) ⟶
      entry (run (var 0) (var 1) (var 2) (var 3)) (var 4) ≐
        coefficient (var 0) (var 1) (var 3) (succ (var 2)) (var 4)) :=
  closeUniv 5 (.impI (returned_lookup _ _ _ _ _ Prf.hyp0))
theorem returned_polynomial_product_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 2) ⟶ length (var 1) ≐ succ (var 3) ⟶
      evaluate (run (var 0) (var 1) (var 2) (var 3)) (var 4) ≐
        qmul (evaluate (var 0) (var 4)) (evaluate (var 1) (var 4))) :=
  closeUniv 5 (.impI (.impI (returned_evaluation _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalPolynomialProduct
