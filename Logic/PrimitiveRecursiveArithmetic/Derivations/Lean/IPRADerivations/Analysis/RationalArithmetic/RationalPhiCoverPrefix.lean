import IPRADerivations.Analysis.RationalArithmetic.RationalPhiCoverBound
import IPRADerivations.Foundations.BoundedSyntax

/-!
# The exact m*M+1 cutoff for the original finite Phi_s cover theorem

An actual sequence copies the first K original raw point codes. The original
curve equations, field distinctness and any fixed bounded point condition are
inherited from literal lookups. A cover assertion only for valid tuples of
length m*M+1 therefore bounds every original valid tuple by m*M. No uniform
cover of an unbounded set or quantitative cover-existence theorem is asserted.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPhiCoverPrefix

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalPhiSectionNonzero (curveInput)
open RationalPhiCoverAssignment (sourceCoverBit)
open RationalCurvePointsGaussianEmbedding (distinct distinctFrom distinct_at)
open RationalSuperellipticNormDegree (pointPowers point_power_at)
open RationalArgmin (rationalEq rationalEq_congr)
open GaussianRationalFiberGrouping (abscissa ordinate)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def entryBody : PTm 2 := entry (var 1) (var 0)
def pointPrefix (P K : PTm n) : PTm n := sequence entryBody K P
def cutoff (m M : PTm n) : PTm n := succ (m*M)
def extra (A : BFm 2) (P x : PTm n) : Fm PTm n := .all (lt (var 0) (length (Syn.shift P)) ⟶
  (formula A).subst ![entry (Syn.shift P) (var 0),Syn.shift x])
def cutoffCover (A : BFm 2) (f s r m M x : PTm n) : Fm PTm n := .all
  (length (var 0) ≐ cutoff (Syn.shift m) (Syn.shift M) ⟶ distinct (var 0) ⟶
    pointPowers (Syn.shift f) (Syn.shift r) (var 0) ⟶ extra A (var 0) (Syn.shift x) ⟶
      sourceCoverBit (Syn.shift s) (var 0) (Syn.shift M) ≐ one)

@[simp] theorem subst_prefix {q : ℕ} (σ : Fin n → PTm q) (P K : PTm n) :
    Syn.subst σ (pointPrefix P K) = pointPrefix (Syn.subst σ P) (Syn.subst σ K) := by simp [pointPrefix]
@[simp] theorem subst_cutoff {q : ℕ} (σ : Fin n → PTm q) (m M : PTm n) :
    Syn.subst σ (cutoff m M) = cutoff (Syn.subst σ m) (Syn.subst σ M) := by simp [cutoff]
@[simp] theorem subst_extra {q : ℕ} (σ : Fin n → PTm q) (A : BFm 2) (P x : PTm n) :
    (extra A P x).subst σ = extra A (Syn.subst σ P) (Syn.subst σ x) := by
  simp only [extra,Fm.subst_all,Fm.subst_imp,subst_lt,Foundations.SequenceComposition.subst_length,
    Fm.subst_subst,Syn.subst_var,Syn.up_zero,Syn.subst_shift,Syn.shift_subst]
  congr 2
  congr 1
  funext i
  fin_cases i <;> simp [Syn.subst_shift]
@[simp] theorem subst_cutoffCover {q : ℕ} (σ : Fin n → PTm q) (A : BFm 2) (f s r m M x : PTm n) :
    (cutoffCover A f s r m M x).subst σ = cutoffCover A (Syn.subst σ f) (Syn.subst σ s) (Syn.subst σ r)
      (Syn.subst σ m) (Syn.subst σ M) (Syn.subst σ x) := by simp [cutoffCover,Syn.subst_shift,Syn.shift_subst]

theorem entry_body_at (P i : PTm n) : inst2 entryBody i P = entry P i := by simp [entryBody,inst2]
theorem prefix_length (P K : PTm n) : Γ ⊢[PRAAx] length (pointPrefix P K) ≐ K := sequence_length _ _ _
theorem prefix_lookup (P K i : PTm n) (hi : Γ ⊢[PRAAx] lt i K) : Γ ⊢[PRAAx]
    entry (pointPrefix P K) i ≐ entry P i := by simpa only [pointPrefix,entry_body_at] using sequence_decode (Γ := Γ) entryBody (x := P) hi

private theorem prefix_power_at (f r P K i : PTm n) (hc : Γ ⊢[PRAAx] le K (length P)) (hp : Γ ⊢[PRAAx] pointPowers f r P)
    (hi : Γ ⊢[PRAAx] lt i (length (pointPrefix P K))) : Γ ⊢[PRAAx]
    rationalEq (RationalScalarPowerGaussianEmbedding.power (ordinate (pointPrefix P K) i) r)
      (RationalPolynomialGaussianEmbedding.evaluate f (abscissa (pointPrefix P K) i)) := by
  have ik := lt_congr (.eqRefl i) (prefix_length P K) hi
  have eq := prefix_lookup P K i ik
  have old := point_power_at f r P i hp (le_trans ik hc)
  exact rationalEq_congr (congrAp2 RationalScalarPowerGaussianEmbedding.powerF (.eqRefl r) (congrSnd eq)).eqSymm
    (congrAp3 RationalPolynomialGaussianEmbedding.hornerF (.eqRefl (length f)) (.eqRefl f) (congrFst eq)).eqSymm old

theorem prefix_powers (f r P K : PTm n) (hc : Γ ⊢[PRAAx] le K (length P)) (hp : Γ ⊢[PRAAx] pointPowers f r P) : Γ ⊢[PRAAx]
    pointPowers f r (pointPrefix P K) := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift K) (length (Syn.shift P)) := by simpa [Fm.shift,Syn.shift] using hc.shift
  have ps : Γ.map Fm.shift ⊢[PRAAx] pointPowers (Syn.shift f) (Syn.shift r) (Syn.shift P) := by simpa [Fm.shift,Syn.shift] using hp.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_prefix,RationalScalarPowerGaussianEmbedding.subst_power,RationalPolynomialGaussianEmbedding.subst_evaluate,
    GaussianRationalFiberGrouping.subst_abscissa,GaussianRationalFiberGrouping.subst_ordinate] using
    prefix_power_at (Syn.shift f) (Syn.shift r) (Syn.shift P) (Syn.shift K) (var 0) cs.wk ps.wk Prf.hyp0

private theorem prefix_distinct_at (P K i j : PTm n) (hc : Γ ⊢[PRAAx] le K (length P)) (hd : Γ ⊢[PRAAx] distinct P)
    (hi : Γ ⊢[PRAAx] lt i (length (pointPrefix P K))) (hj : Γ ⊢[PRAAx] lt j (length (pointPrefix P K))) (hij : Γ ⊢[PRAAx] lt i j) : Γ ⊢[PRAAx]
    neg (rationalEq (abscissa (pointPrefix P K) j) (abscissa (pointPrefix P K) i) ⋏ rationalEq (ordinate (pointPrefix P K) j) (ordinate (pointPrefix P K) i)) := by
  have ik := lt_congr (.eqRefl i) (prefix_length P K) hi
  have jk := lt_congr (.eqRefl j) (prefix_length P K) hj
  have ei := prefix_lookup P K i ik
  have ej := prefix_lookup P K j jk
  have old := distinct_at P i j hd (le_trans ik hc) (le_trans jk hc) hij
  exact .impI (.impE old.wk (.andI (rationalEq_congr (congrFst ej.wk) (congrFst ei.wk) (.andE₁ Prf.hyp0))
    (rationalEq_congr (congrSnd ej.wk) (congrSnd ei.wk) (.andE₂ Prf.hyp0))))

theorem prefix_distinct (P K : PTm n) (hc : Γ ⊢[PRAAx] le K (length P)) (hd : Γ ⊢[PRAAx] distinct P) : Γ ⊢[PRAAx] distinct (pointPrefix P K) := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift K) (length (Syn.shift P)) := by simpa [Fm.shift,Syn.shift] using hc.shift
  have ds : Γ.map Fm.shift ⊢[PRAAx] distinct (Syn.shift P) := by simpa [Fm.shift,Syn.shift] using hd.shift
  refine .allI (.impI ?_)
  let Q := pointPrefix (Syn.shift P) (Syn.shift K)
  let Δ := lt (var 0) (length Q) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (length Q) := Prf.hyp0
  have inner : Δ ⊢[PRAAx] distinctFrom Q (var 0) := by
    refine .allI (.impI (.impI ?_))
    let i := Syn.shift (var 0 : PTm (n+1))
    let Q' := pointPrefix (Syn.shift (Syn.shift P)) (Syn.shift (Syn.shift K))
    have is : Δ.map Fm.shift ⊢[PRAAx] lt i (length Q') := by
      simpa [i,Q,Q',Fm.shift,Syn.shift] using hi.shift
    have c : Δ.map Fm.shift ⊢[PRAAx] le (Syn.shift (Syn.shift K)) (length (Syn.shift (Syn.shift P))) := by
      simpa [Δ,Q,Fm.shift,Syn.shift] using (cs.wk : Δ ⊢[PRAAx] _).shift
    have d : Δ.map Fm.shift ⊢[PRAAx] distinct (Syn.shift (Syn.shift P)) := by
      simpa [Δ,Q,Fm.shift,Syn.shift] using (ds.wk : Δ ⊢[PRAAx] _).shift
    simpa only [i,Q,Q',Syn.shift,subst_prefix,GaussianRationalFiberGrouping.subst_abscissa,GaussianRationalFiberGrouping.subst_ordinate,
      RationalArgmin.subst_rationalEq,Fm.subst_and] using prefix_distinct_at (Syn.shift (Syn.shift P)) (Syn.shift (Syn.shift K)) i (var 0)
        c.wk.wk d.wk.wk is.wk.wk Prf.hyp1 Prf.hyp0
  simpa only [Δ,Q,Syn.shift,subst_prefix,Foundations.SequenceComposition.subst_length] using inner

theorem extra_at (A : BFm 2) (P x i : PTm n) (h : Γ ⊢[PRAAx] extra A P x) (hi : Γ ⊢[PRAAx] lt i (length P)) : Γ ⊢[PRAAx]
    (formula A).subst ![entry P i,x] := by
  have rule : Γ ⊢[PRAAx] lt i (length P) ⟶ (formula A).subst ![entry P i,x] := by
    simpa only [extra,Fm.subst_imp,Foundations.FiniteCoverAssignment.property_inst,subst_lt,Foundations.SequenceComposition.subst_length,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i
  exact .impE rule hi

theorem prefix_extra (A : BFm 2) (P K x : PTm n) (hc : Γ ⊢[PRAAx] le K (length P)) (he : Γ ⊢[PRAAx] extra A P x) : Γ ⊢[PRAAx]
    extra A (pointPrefix P K) x := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift K) (length (Syn.shift P)) := by simpa [Fm.shift,Syn.shift] using hc.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] extra A (Syn.shift P) (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using he.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (pointPrefix (Syn.shift P) (Syn.shift K))) :: Γ.map Fm.shift
  have ik : Δ ⊢[PRAAx] lt (var 0) (Syn.shift K) := lt_congr (.eqRefl _) (prefix_length _ _) Prf.hyp0
  have old := extra_at A (Syn.shift P) (Syn.shift x) (var 0) es.wk (le_trans ik cs.wk)
  simpa only [Δ,Syn.shift,subst_prefix] using Foundations.FiniteCoverAssignment.property_congr (formula A)
    (entry (Syn.shift P) (var 0)) (entry (pointPrefix (Syn.shift P) (Syn.shift K)) (var 0)) (Syn.shift x)
    (prefix_lookup _ _ _ ik).eqSymm old

theorem cutoff_cover_at (A : BFm 2) (f s r m M x Q : PTm n) (h : Γ ⊢[PRAAx] cutoffCover A f s r m M x)
    (hl : Γ ⊢[PRAAx] length Q ≐ cutoff m M) (hd : Γ ⊢[PRAAx] distinct Q)
    (hp : Γ ⊢[PRAAx] pointPowers f r Q) (he : Γ ⊢[PRAAx] extra A Q x) : Γ ⊢[PRAAx] sourceCoverBit s Q M ≐ one := by
  have rule : Γ ⊢[PRAAx] length Q ≐ cutoff m M ⟶ distinct Q ⟶ pointPowers f r Q ⟶ extra A Q x ⟶ sourceCoverBit s Q M ≐ one := by
    simpa [cutoffCover] using h.allE Q
  exact .impE (.impE (.impE (.impE rule hl) hd) hp) he

/-- Only the exact cutoff length is quantified in the cover hypothesis. -/
theorem cutoff_bound (A : BFm 2) (f s r m P M x : PTm n) (h : Γ ⊢[PRAAx] curveInput f s r m)
    (hd : Γ ⊢[PRAAx] distinct P) (hp : Γ ⊢[PRAAx] pointPowers f r P) (he : Γ ⊢[PRAAx] extra A P x)
    (hc : Γ ⊢[PRAAx] cutoffCover A f s r m M x) : Γ ⊢[PRAAx] le (length P) (m*M) := by
  refine .orE (lt_or_le (m*M) (length P)) ?_ Prf.hyp0
  let Δ := lt (m*M) (length P) :: Γ
  let Q := pointPrefix P (cutoff m M)
  have cap : Δ ⊢[PRAAx] le (cutoff m M) (length P) := Prf.hyp0
  have d := prefix_distinct P (cutoff m M) cap hd.wk
  have p := prefix_powers f r P (cutoff m M) cap hp.wk
  have e := prefix_extra A P (cutoff m M) x cap he.wk
  have bit := cutoff_cover_at A f s r m M x Q hc.wk (prefix_length _ _) d p e
  have bound := RationalPhiCoverBound.cover_bit_bound f s r m Q M h.wk d p bit
  exact .botE _ (not_succ_le_self (m*M) Fm.bot (le_congr (prefix_length P (cutoff m M)) (.eqRefl _) bound))

/-- The actual cutoff prefix, its computed length, and the original list. -/
def output (P m M : PTm n) : PTm n := pairT (pointPrefix P (cutoff m M)) (pairT (cutoff m M) P)
def prefixF : PR 2 := PTm.toPR (pointPrefix (var 0) (var 1))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (P m M : PTm n) : PTm n := app outputF ![P,m,M]

@[simp] theorem subst_output {q : ℕ} (σ : Fin n → PTm q) (P m M : PTm n) :
    Syn.subst σ (output P m M) = output (Syn.subst σ P) (Syn.subst σ m) (Syn.subst σ M) := by simp [output]
@[simp] theorem subst_run {q : ℕ} (σ : Fin n → PTm q) (P m M : PTm n) :
    Syn.subst σ (run P m M) = run (Syn.subst σ P) (Syn.subst σ m) (Syn.subst σ M) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem prefix_program_at (P K : PTm n) : Γ ⊢[PRAAx] app prefixF ![P,K] ≐ pointPrefix P K := by
  simpa [prefixF] using toPR_eq (Γ := Γ) (pointPrefix (var 0) (var 1) : PTm 2) ![P,K]
theorem program_at (P m M : PTm n) : Γ ⊢[PRAAx] run P m M ≐ output P m M := by
  simpa [run,outputF,output,Matrix.cons_val_succ',Matrix.cons_val_zero'] using
    toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![P,m,M]
theorem returned_prefix (P m M : PTm n) : Γ ⊢[PRAAx] fstT (run P m M) ≐ pointPrefix P (cutoff m M) :=
  (congrFst (program_at P m M)).eqTrans (fst_pair _ _)
theorem returned_cutoff (P m M : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run P m M)) ≐ cutoff m M :=
  (congrFst ((congrSnd (program_at P m M)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_original (P m M : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run P m M)) ≐ P :=
  (congrSnd ((congrSnd (program_at P m M)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_length (P m M : PTm n) : Γ ⊢[PRAAx] length (fstT (run P m M)) ≐ fstT (sndT (run P m M)) :=
  ((congrFst (returned_prefix P m M)).eqTrans (prefix_length _ _)).eqTrans
    (returned_cutoff P m M).eqSymm
theorem returned_lookup (P m M i : PTm n) (hi : Γ ⊢[PRAAx] lt i (cutoff m M)) : Γ ⊢[PRAAx]
    entry (fstT (run P m M)) i ≐ entry P i :=
  (entry_congr (returned_prefix P m M) (.eqRefl i)).eqTrans (prefix_lookup _ _ _ hi)
theorem returned_bound (A : BFm 2) (f s r m P M x : PTm n) (h : Γ ⊢[PRAAx] curveInput f s r m)
    (hd : Γ ⊢[PRAAx] distinct P) (hp : Γ ⊢[PRAAx] pointPowers f r P) (he : Γ ⊢[PRAAx] extra A P x)
    (hc : Γ ⊢[PRAAx] cutoffCover A f s r m M x) : Γ ⊢[PRAAx]
    le (length (sndT (sndT (run P m M)))) (m*M) :=
  le_congr (congrFst (returned_original P m M)).eqSymm (.eqRefl _)
    (cutoff_bound A f s r m P M x h hd hp he hc)

theorem actual_raw_prefix_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (length (pointPrefix (var 0) (var 1)) ≐ var 1) := closeUniv 2 (prefix_length _ _)
theorem actual_raw_prefix_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 1) ⟶ entry (pointPrefix (var 0) (var 1)) (var 2) ≐ entry (var 0) (var 2)) :=
  closeUniv 3 (.impI (prefix_lookup _ _ _ Prf.hyp0))
theorem actual_prefix_curve_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (length (var 2)) ⟶ pointPowers (var 0) (var 1) (var 2) ⟶
      pointPowers (var 0) (var 1) (pointPrefix (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (prefix_powers _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_prefix_distinct_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (var 1) (length (var 0)) ⟶ distinct (var 0) ⟶ distinct (pointPrefix (var 0) (var 1))) :=
  closeUniv 2 (.impI (.impI (prefix_distinct _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_prefix_extra_closed (A : BFm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 1) (length (var 0)) ⟶ extra A (var 0) (var 2) ⟶ extra A (pointPrefix (var 0) (var 1)) (var 2)) :=
  closeUniv 3 (.impI (.impI (prefix_extra A _ _ _ Prf.hyp1 Prf.hyp0)))
/-- All numerical source data are internal; only the fixed bounded syntax A is external. -/
theorem actual_original_phi_cutoff_bound_closed (A : BFm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (curveInput (var 0) (var 1) (var 2) (var 3) ⟶ distinct (var 4) ⟶ pointPowers (var 0) (var 2) (var 4) ⟶
      extra A (var 4) (var 6) ⟶ cutoffCover A (var 0) (var 1) (var 2) (var 3) (var 5) (var 6) ⟶
        le (length (var 4)) (var 3*var 5)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (cutoff_bound A (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)
    (.hyp (by simp)) (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0))))))
theorem actual_prefix_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (app prefixF ![var 0,var 1] ≐ pointPrefix (var 0) (var 1)) := closeUniv 2 (prefix_program_at _ _)
theorem actual_cutoff_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_prefix_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (fstT (run (var 0) (var 1) (var 2))) ≐ fstT (sndT (run (var 0) (var 1) (var 2)))) := closeUniv 3 (returned_length _ _ _)
theorem actual_returned_prefix_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (cutoff (var 1) (var 2)) ⟶ entry (fstT (run (var 0) (var 1) (var 2))) (var 3) ≐ entry (var 0) (var 3)) :=
  closeUniv 4 (.impI (returned_lookup _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalPhiCoverPrefix
