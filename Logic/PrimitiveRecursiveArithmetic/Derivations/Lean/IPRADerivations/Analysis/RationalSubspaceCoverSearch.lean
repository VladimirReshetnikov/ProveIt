import IPRADerivations.Analysis.RationalSubspaceCoverCandidates
import IPRADerivations.Foundations.BoundedSyntax

/-!
# Exact bounded testing and search of finite rational subspace covers

A fixed bounded formula checks actual rank deficits of the candidate spans
and the original rational membership tests for every original tuple vector.
Its Boolean reflection is equivalent to genuine properness and finite cover.
The actual least search ranges over codes below 2^(tM). A supplied proper
finite cover proves search success; a default result rejects every candidate.
No quantitative cover-existence theorem is inferred from this finite search.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalSubspaceCoverSearch

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalSubspaceCoverCandidates (candidate bound encode encode_bound reconstructed_certificate)
open RationalFiniteSpanCover (family covered coveredAt)
open RationalRowSpanGaussianEmbedding (matrix hasCoefficients)
open GaussianRationalRankNullityCriterion (rank)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula bit bit_cases bit_subst)
open LeanProofs.IPRA.Foundations.BoundedReflection (wit)
open ConciseIPRA.PTm (zero succ app)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def properBF : BFm 2 := .all (length (var 0)) (.lt
  (rank (matrix (entry (var 1) (var 0)) (length (entry (var 1) (var 0))) (var 2))
    (length (entry (var 1) (var 0))) (var 2)) (var 2))
def coverBF : BFm 3 := .all (length (var 0)) (.ex (length (var 2)) (.eq
  (RationalOriginalSpanMembership.test (entry (var 3) (var 0)) (length (entry (var 3) (var 0))) (var 4)
    (entry (var 2) (var 1))) one))
def properTest (D N : PTm n) : PTm n := bit properBF ![D,N]
def coverTest (T D N : PTm n) : PTm n := bit coverBF ![T,D,N]
def certified (T M N w : PTm n) : Fm PTm n := family (candidate T M w) N ⋏ covered T (candidate T M w) N
def test (T M N w : PTm n) : PTm n := eqb
  (properTest (candidate T M w) N * coverTest T (candidate T M w) N) one

@[simp] theorem subst_properTest {q : ℕ} (σ : Fin n → PTm q) (D N : PTm n) :
    Syn.subst σ (properTest D N) = properTest (Syn.subst σ D) (Syn.subst σ N) := by
  simp only [properTest,bit_subst]
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem subst_coverTest {q : ℕ} (σ : Fin n → PTm q) (T D N : PTm n) :
    Syn.subst σ (coverTest T D N) = coverTest (Syn.subst σ T) (Syn.subst σ D) (Syn.subst σ N) := by
  simp only [coverTest,bit_subst]
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem subst_certified {q : ℕ} (σ : Fin n → PTm q) (T M N w : PTm n) :
    (certified T M N w).subst σ = certified (Syn.subst σ T) (Syn.subst σ M) (Syn.subst σ N) (Syn.subst σ w) := by simp [certified]
@[simp] theorem subst_test {q : ℕ} (σ : Fin n → PTm q) (T M N w : PTm n) :
    Syn.subst σ (test T M N w) = test (Syn.subst σ T) (Syn.subst σ M) (Syn.subst σ N) (Syn.subst σ w) := by simp [test]

private theorem iff_and {a b c d : Fm PTm n} (h : Γ ⊢[PRAAx] Fm.iff a b) (j : Γ ⊢[PRAAx] Fm.iff c d) :
    Γ ⊢[PRAAx] Fm.iff (a ⋏ c) (b ⋏ d) :=
  .iffI (.impI (.andI (.iffMp h.wk (.andE₁ Prf.hyp0)) (.iffMp j.wk (.andE₂ Prf.hyp0))))
    (.impI (.andI (.iffMpr h.wk (.andE₁ Prf.hyp0)) (.iffMpr j.wk (.andE₂ Prf.hyp0))))
private theorem iff_imp {a b c d : Fm PTm n} (h : Γ ⊢[PRAAx] Fm.iff a b) (j : Γ ⊢[PRAAx] Fm.iff c d) :
    Γ ⊢[PRAAx] Fm.iff (a ⟶ c) (b ⟶ d) :=
  .iffI (.impI (.impI (.iffMp j.wk.wk (.impE Prf.hyp1 (.iffMpr h.wk.wk Prf.hyp0)))))
    (.impI (.impI (.iffMpr j.wk.wk (.impE Prf.hyp1 (.iffMp h.wk.wk Prf.hyp0)))))
private theorem iff_all {a b : Fm PTm (n+1)} (h : Γ.map Fm.shift ⊢[PRAAx] Fm.iff a b) :
    Γ ⊢[PRAAx] Fm.iff (Fm.all a) (Fm.all b) := by
  refine .iffI (.impI (.allI ?_)) (.impI (.allI ?_))
  · exact .iffMp h.wk (Prf.hyp0 (Γ := Γ) (φ := Fm.all a)).allOpen
  · exact .iffMpr h.wk (Prf.hyp0 (Γ := Γ) (φ := Fm.all b)).allOpen
private theorem iff_ex {a b : Fm PTm (n+1)} (h : Γ.map Fm.shift ⊢[PRAAx] Fm.iff a b) :
    Γ ⊢[PRAAx] Fm.iff (Fm.ex a) (Fm.ex b) := by
  refine .iffI (.impI (.exE Prf.hyp0 ?_)) (.impI (.exE Prf.hyp0 ?_))
  · have hb : (a :: (Fm.ex a).shift :: Γ.map Fm.shift) ⊢[PRAAx] b := .iffMp h.wk.wk Prf.hyp0
    exact .exI (var 0) (by simpa only [Fm.shift,Fm.subst_ex,Fm.subst_up_succ_inst,List.map_cons] using hb)
  · have ha : (b :: (Fm.ex b).shift :: Γ.map Fm.shift) ⊢[PRAAx] a := .iffMpr h.wk.wk Prf.hyp0
    exact .exI (var 0) (by simpa only [Fm.shift,Fm.subst_ex,Fm.subst_up_succ_inst,List.map_cons] using ha)

private theorem up_two {k q : ℕ} (σ : Fin (k+2) → PTm q) : Syn.up σ 2 = Syn.shift (σ 1) := Syn.up_succ σ 1
private theorem up_three {k q : ℕ} (σ : Fin (k+3) → PTm q) : Syn.up σ 3 = Syn.shift (σ 2) := Syn.up_succ σ 2
private theorem up_four {k q : ℕ} (σ : Fin (k+4) → PTm q) : Syn.up σ 4 = Syn.shift (σ 3) := Syn.up_succ σ 3

theorem proper_test_iff (D N : PTm n) : Γ ⊢[PRAAx] Fm.iff (properTest D N ≐ one) (family D N) := by
  have body := RationalSuperellipticSubspace.proper_iff_deficit (Γ := Γ.map Fm.shift)
    (entry (Syn.shift D) (var 0)) (length (entry (Syn.shift D) (var 0))) (Syn.shift N)
  have logical := iff_all (iff_imp (Prf.iffRefl (lt (var 0) (length (Syn.shift D)))) body.iffSymm)
  have law : Γ ⊢[PRAAx] Fm.iff ((formula properBF).subst ![D,N]) (family D N) := by
    simpa [properBF,formula,BFm.lt,BFm.le,family,lt,le,Syn.subst_shift,Syn.shift_subst,Syn.up_one,up_two,up_three,up_four] using logical
  exact (Foundations.BoundedSyntax.bounded_reflection properBF ![D,N]).iffTrans law

theorem cover_test_iff (T D N : PTm n) : Γ ⊢[PRAAx] Fm.iff (coverTest T D N ≐ one) (covered T D N) := by
  have body := RationalOriginalSpanMembership.test_iff (Γ := (Γ.map Fm.shift).map Fm.shift)
    (entry (Syn.shift (Syn.shift D)) (var 0)) (length (entry (Syn.shift (Syn.shift D)) (var 0)))
    (Syn.shift (Syn.shift N)) (entry (Syn.shift (Syn.shift T)) (var 1))
  have logical := iff_all (iff_imp (Prf.iffRefl (lt (var 0) (length (Syn.shift T))))
    (iff_ex (iff_and (Prf.iffRefl (lt (var 0) (length (Syn.shift (Syn.shift D))))) body)))
  have law : Γ ⊢[PRAAx] Fm.iff ((formula coverBF).subst ![T,D,N]) (covered T D N) := by
    simpa [coverBF,formula,covered,coveredAt,Syn.subst_shift,Syn.shift_subst,Syn.up_one,up_two,up_three,up_four,Syn.shift_var,Fin.succ_zero_eq_one,Syn.shift] using logical
  exact (Foundations.BoundedSyntax.bounded_reflection coverBF ![T,D,N]).iffTrans law

theorem test_cases (T M N w : PTm n) : Γ ⊢[PRAAx] (test T M N w ≐ zero) ⋎ (test T M N w ≐ one) :=
  Foundations.BoundedReflection.eqb_cases _ _
theorem test_complete (T M N w : PTm n) (h : Γ ⊢[PRAAx] certified T M N w) : Γ ⊢[PRAAx] test T M N w ≐ one := by
  have hp := (proper_test_iff (candidate T M w) N).iffMpr (.andE₁ h)
  have hc := (cover_test_iff T (candidate T M w) N).iffMpr (.andE₂ h)
  exact eqb_of_eq ((congrMul hp hc).eqTrans (one_mul one))
theorem test_sound (T M N w : PTm n) (h : Γ ⊢[PRAAx] test T M N w ≐ one) : Γ ⊢[PRAAx] certified T M N w := by
  have product := Foundations.BoundedReflection.eq_of_eqb h
  have hp : Γ ⊢[PRAAx] properTest (candidate T M w) N ≐ one := by
    refine .orE (bit_cases properBF ![candidate T M w,N]) ?_ Prf.hyp0
    exact .botE _ (succ_ne_zero (product.wk.eqSymm.eqTrans ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _))))
  have hc : Γ ⊢[PRAAx] coverTest T (candidate T M w) N ≐ one := by
    refine .orE (bit_cases coverBF ![T,candidate T M w,N]) ?_ Prf.hyp0
    exact .botE _ (succ_ne_zero (product.wk.eqSymm.eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))))
  exact .andI ((proper_test_iff _ _).iffMp hp) ((cover_test_iff _ _ _).iffMp hc)
theorem test_iff (T M N w : PTm n) : Γ ⊢[PRAAx] Fm.iff (test T M N w ≐ one) (certified T M N w) :=
  .andI (.impI (test_sound _ _ _ _ Prf.hyp0)) (.impI (test_complete _ _ _ _ Prf.hyp0))
theorem test_nonzero_one (T M N w : PTm n) (h : Γ ⊢[PRAAx] neg (test T M N w ≐ zero)) : Γ ⊢[PRAAx] test T M N w ≐ one :=
  .orE (test_cases _ _ _ _) (.botE _ (.impE h.wk Prf.hyp0)) Prf.hyp0
theorem test_zero_iff (T M N w : PTm n) : Γ ⊢[PRAAx] Fm.iff (test T M N w ≐ zero) (neg (certified T M N w)) := by
  refine .andI (.impI (.impI ?_)) (.impI ?_)
  · exact succ_ne_zero ((test_complete T M N w Prf.hyp0).eqSymm.eqTrans Prf.hyp1)
  · refine .orE (test_cases T M N w) Prf.hyp0 ?_
    exact .botE _ (.impE Prf.hyp1 (test_sound _ _ _ _ Prf.hyp0))

def data (T M N : PTm n) : PTm n := pairT T (pairT M N)
def testBody : PTm 2 := test (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def selected (T M N : PTm n) : PTm n := wit testBody (bound T M) (data T M N)
def chosen (T M N : PTm n) : PTm n := candidate T M (selected T M N)
@[simp] theorem subst_data {q : ℕ} (σ : Fin n → PTm q) (T M N : PTm n) :
    Syn.subst σ (data T M N) = data (Syn.subst σ T) (Syn.subst σ M) (Syn.subst σ N) := by simp [data]
@[simp] theorem subst_selected {q : ℕ} (σ : Fin n → PTm q) (T M N : PTm n) :
    Syn.subst σ (selected T M N) = selected (Syn.subst σ T) (Syn.subst σ M) (Syn.subst σ N) := by
  simp [selected,Foundations.BoundedReflection.wit,Search.mu]
@[simp] theorem subst_chosen {q : ℕ} (σ : Fin n → PTm q) (T M N : PTm n) :
    Syn.subst σ (chosen T M N) = chosen (Syn.subst σ T) (Syn.subst σ M) (Syn.subst σ N) := by simp [chosen]

private theorem test_congr {T S M P N Q w v : PTm n} (hT : Γ ⊢[PRAAx] T ≐ S)
    (hM : Γ ⊢[PRAAx] M ≐ P) (hN : Γ ⊢[PRAAx] N ≐ Q) (hw : Γ ⊢[PRAAx] w ≐ v) : Γ ⊢[PRAAx]
    test T M N w ≐ test S P Q v := by
  simpa only [subst_test,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (test (var 0) (var 1) (var 2) (var 3) : PTm 4) (σ := ![T,M,N,w]) (σ' := ![S,P,Q,v])
      (fun i => by fin_cases i; exact hT; exact hM; exact hN; exact hw)
theorem test_body_at (T M N w : PTm n) : Γ ⊢[PRAAx] inst2 testBody w (data T M N) ≐ test T M N w := by
  simp only [testBody,inst2,subst_test,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact test_congr (fst_pair _ _) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)) (.eqRefl _)

theorem selected_bound (T M N : PTm n) : Γ ⊢[PRAAx] le (selected T M N) (bound T M) :=
  .andE₁ (Search.search_spec (f := Foundations.BoundedReflection.nB testBody) (bound T M) zero (data T M N))
theorem selected_success (T M N : PTm n) (hs : Γ ⊢[PRAAx] lt (selected T M N) (bound T M)) : Γ ⊢[PRAAx]
    test T M N (selected T M N) ≐ one := by
  have z := Prf.impE (.andE₁ (.andE₂ (Search.search_spec (Γ := Γ) (f := Foundations.BoundedReflection.nB testBody)
    (bound T M) zero (data T M N)))) hs
  rw [Foundations.BoundedReflection.inst2_nB] at z
  have nz := Foundations.BoundedReflection.ne_of_compl z
  exact test_nonzero_one T M N (selected T M N) (.impI (.impE nz.wk ((test_body_at T M N (selected T M N)).wk.eqTrans Prf.hyp0)))
theorem selected_found (T M N w : PTm n) (hw : Γ ⊢[PRAAx] lt w (bound T M)) (ht : Γ ⊢[PRAAx] test T M N w ≐ one) : Γ ⊢[PRAAx]
    lt (selected T M N) (bound T M) ⋏ test T M N (selected T M N) ≐ one := by
  have nz : Γ ⊢[PRAAx] neg (inst2 testBody w (data T M N) ≐ zero) :=
    .impI (succ_ne_zero (((test_body_at T M N w).eqTrans ht).wk.eqSymm.eqTrans Prf.hyp0))
  have found := Foundations.BoundedReflection.ex_elim testBody (Foundations.BoundedReflection.ex_intro testBody nz hw)
  exact .andI (.andE₁ found) (selected_success T M N (.andE₁ found))
theorem selected_least (T M N w : PTm n) (hw : Γ ⊢[PRAAx] lt w (selected T M N)) : Γ ⊢[PRAAx] test T M N w ≐ zero :=
  (test_body_at T M N w).eqSymm.eqTrans (Foundations.BoundedReflection.ex_least testBody hw)
theorem default_rejects (T M N w : PTm n) (hs : Γ ⊢[PRAAx] selected T M N ≐ bound T M)
    (hw : Γ ⊢[PRAAx] lt w (bound T M)) : Γ ⊢[PRAAx] neg (certified T M N w) :=
  (test_zero_iff T M N w).iffMp (selected_least T M N w (lt_congr (.eqRefl _) hs.eqSymm hw))

theorem source_success (T D N : PTm n) (hf : Γ ⊢[PRAAx] family D N) (hc : Γ ⊢[PRAAx] covered T D N) : Γ ⊢[PRAAx]
    lt (selected T (length D) N) (bound T (length D)) ⋏ certified T (length D) N (selected T (length D) N) := by
  have source := reconstructed_certificate T D N hf hc
  have cert : Γ ⊢[PRAAx] certified T (length D) N (encode T D N) := .andE₂ source
  have found := selected_found T (length D) N (encode T D N) (encode_bound T D N) (test_complete _ _ _ _ cert)
  exact .andI (.andE₁ found) (test_sound _ _ _ _ (.andE₂ found))
theorem chosen_length (T M N : PTm n) : Γ ⊢[PRAAx] length (chosen T M N) ≐ M :=
  RationalSubspaceCoverCandidates.candidate_length _ _ _

/-- The source decision bit is the bounded existential over ALL candidate codes. -/
def coverBit (T M N : PTm n) : PTm n := Foundations.BoundedReflection.exB testBody (bound T M) (data T M N)
def existsCandidate (T M N : PTm n) : Fm PTm n := .ex
  (lt (var 0) (bound (Syn.shift T) (Syn.shift M)) ⋏ certified (Syn.shift T) (Syn.shift M) (Syn.shift N) (var 0))
@[simp] theorem subst_coverBit {q : ℕ} (σ : Fin n → PTm q) (T M N : PTm n) :
    Syn.subst σ (coverBit T M N) = coverBit (Syn.subst σ T) (Syn.subst σ M) (Syn.subst σ N) := by
  simp [coverBit,Foundations.BoundedReflection.exB,Foundations.BoundedReflection.allB]
@[simp] theorem subst_existsCandidate {q : ℕ} (σ : Fin n → PTm q) (T M N : PTm n) :
    (existsCandidate T M N).subst σ = existsCandidate (Syn.subst σ T) (Syn.subst σ M) (Syn.subst σ N) := by
  simp [existsCandidate,Syn.subst_shift,Syn.shift_subst]

theorem cover_bit_cases (T M N : PTm n) : Γ ⊢[PRAAx] (coverBit T M N ≐ zero) ⋎ (coverBit T M N ≐ one) :=
  Foundations.BoundedReflection.ex_cases _ _ _
theorem cover_bit_found (T M N : PTm n) (h : Γ ⊢[PRAAx] coverBit T M N ≐ one) : Γ ⊢[PRAAx]
    lt (selected T M N) (bound T M) := .andE₁ (Foundations.BoundedReflection.ex_elim testBody h)
theorem cover_bit_of_found (T M N : PTm n) (h : Γ ⊢[PRAAx] lt (selected T M N) (bound T M)) : Γ ⊢[PRAAx]
    coverBit T M N ≐ one := by
  have accepted := selected_success T M N h
  have nonzero : Γ ⊢[PRAAx] neg (inst2 testBody (selected T M N) (data T M N) ≐ zero) :=
    .impI (succ_ne_zero (((test_body_at T M N (selected T M N)).eqTrans accepted).wk.eqSymm.eqTrans Prf.hyp0))
  exact Foundations.BoundedReflection.ex_intro testBody nonzero h

theorem cover_bit_one_iff (T M N : PTm n) : Γ ⊢[PRAAx] Fm.iff (coverBit T M N ≐ one)
    (lt (selected T M N) (bound T M)) :=
  .andI (.impI (cover_bit_found _ _ _ Prf.hyp0)) (.impI (cover_bit_of_found _ _ _ Prf.hyp0))
theorem cover_bit_zero_iff (T M N : PTm n) : Γ ⊢[PRAAx] Fm.iff (coverBit T M N ≐ zero)
    (selected T M N ≐ bound T M) := by
  refine .andI (.impI ?_) (.impI ?_)
  · refine .orE (lt_or_eq_of_le (selected_bound T M N)) ?_ Prf.hyp0
    exact .botE _ (succ_ne_zero ((cover_bit_of_found T M N Prf.hyp0).eqSymm.eqTrans Prf.hyp1))
  · refine .orE (cover_bit_cases T M N) Prf.hyp0 ?_
    exact .botE _ (lt_irrefl _ _ (lt_congr Prf.hyp1 (.eqRefl _) (cover_bit_found T M N Prf.hyp0)))

theorem cover_bit_exists_iff (T M N : PTm n) : Γ ⊢[PRAAx] Fm.iff (coverBit T M N ≐ one) (existsCandidate T M N) := by
  refine .andI (.impI ?_) (.impI ?_)
  · have hs : (coverBit T M N ≐ one) :: Γ ⊢[PRAAx] lt (selected T M N) (bound T M) := cover_bit_found T M N Prf.hyp0
    have valid := test_sound T M N (selected T M N) (selected_success T M N hs)
    refine .exI (selected T M N) ?_
    simpa only [existsCandidate,Fm.subst_and,subst_lt,subst_certified,RationalSubspaceCoverCandidates.subst_bound,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.andI hs valid
  · refine .exE Prf.hyp0 ?_
    let Δ := (lt (var 0) (bound (Syn.shift T) (Syn.shift M)) ⋏ certified (Syn.shift T) (Syn.shift M) (Syn.shift N) (var 0)) ::
      (existsCandidate T M N).shift :: Γ.map Fm.shift
    have found := selected_found (Γ := Δ) (Syn.shift T) (Syn.shift M) (Syn.shift N) (var 0) (.andE₁ Prf.hyp0)
      (test_complete _ _ _ _ (.andE₂ Prf.hyp0))
    simpa only [Δ,Fm.shift,Fm.subst_eq,List.map_cons,subst_coverBit,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using cover_bit_of_found _ _ _ (.andE₁ found)

theorem source_cover_bit (T D N : PTm n) (hf : Γ ⊢[PRAAx] family D N) (hc : Γ ⊢[PRAAx] covered T D N) : Γ ⊢[PRAAx]
    coverBit T (length D) N ≐ one := cover_bit_of_found _ _ _ (.andE₁ (source_success T D N hf hc))
theorem cover_bit_rejects (T M N w : PTm n) (hb : Γ ⊢[PRAAx] coverBit T M N ≐ zero)
    (hw : Γ ⊢[PRAAx] lt w (bound T M)) : Γ ⊢[PRAAx] neg (certified T M N w) :=
  default_rejects _ _ _ _ ((cover_bit_zero_iff T M N).iffMp hb) hw

def testF : PR 4 := PTm.toPR (test (var 0) (var 1) (var 2) (var 3))
def output (T M N : PTm n) : PTm n := pairT (selected T M N)
  (pairT (chosen T M N) (pairT (bound T M) (coverBit T M N)))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (T M N : PTm n) : PTm n := app outputF ![T,M,N]
@[simp] theorem subst_output {q : ℕ} (σ : Fin n → PTm q) (T M N : PTm n) :
    Syn.subst σ (output T M N) = output (Syn.subst σ T) (Syn.subst σ M) (Syn.subst σ N) := by simp [output]
@[simp] theorem subst_run {q : ℕ} (σ : Fin n → PTm q) (T M N : PTm n) :
    Syn.subst σ (run T M N) = run (Syn.subst σ T) (Syn.subst σ M) (Syn.subst σ N) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem test_program_at (T M N w : PTm n) : Γ ⊢[PRAAx] app testF ![T,M,N,w] ≐ test T M N w := by
  simpa [testF] using toPR_eq (Γ := Γ) (test (var 0) (var 1) (var 2) (var 3) : PTm 4) ![T,M,N,w]
theorem program_at (T M N : PTm n) : Γ ⊢[PRAAx] run T M N ≐ output T M N := by
  simpa [run,outputF,output,Matrix.cons_val_succ',Matrix.cons_val_zero'] using
    toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![T,M,N]
theorem returned_code (T M N : PTm n) : Γ ⊢[PRAAx] fstT (run T M N) ≐ selected T M N :=
  (congrFst (program_at T M N)).eqTrans (fst_pair _ _)
theorem returned_family (T M N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run T M N)) ≐ chosen T M N :=
  (congrFst ((congrSnd (program_at T M N)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_bound (T M N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run T M N))) ≐ bound T M :=
  (congrFst ((congrSnd ((congrSnd (program_at T M N)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_bit (T M N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run T M N))) ≐ coverBit T M N :=
  (congrSnd ((congrSnd ((congrSnd (program_at T M N)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem returned_source_cover (T D N : PTm n) (hf : Γ ⊢[PRAAx] family D N) (hc : Γ ⊢[PRAAx] covered T D N) : Γ ⊢[PRAAx]
    family (fstT (sndT (run T (length D) N))) N ⋏ covered T (fstT (sndT (run T (length D) N))) N := by
  let φ := family (var 0) (Syn.shift N) ⋏ covered (Syn.shift T) (var 0) (Syn.shift N)
  have start : Γ ⊢[PRAAx] φ.subst (Syn.inst (chosen T (length D) N)) := by
    simpa only [φ,Fm.subst_and,RationalFiniteSpanCover.subst_family,RationalFiniteSpanCover.subst_covered,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,certified,chosen] using Prf.andE₂ (source_success T D N hf hc)
  simpa only [φ,Fm.subst_and,RationalFiniteSpanCover.subst_family,RationalFiniteSpanCover.subst_covered,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Prf.eqSubst1 φ (returned_family T (length D) N).eqSymm start

theorem actual_global_cover_bit_binary_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((coverBit (var 0) (var 1) (var 2) ≐ zero) ⋎ (coverBit (var 0) (var 1) (var 2) ≐ one)) := closeUniv 3 (cover_bit_cases _ _ _)
theorem actual_global_cover_bit_witness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (Fm.iff (coverBit (var 0) (var 1) (var 2) ≐ one) (existsCandidate (var 0) (var 1) (var 2))) := closeUniv 3 (cover_bit_exists_iff _ _ _)
theorem actual_global_cover_bit_failure_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (Fm.iff (coverBit (var 0) (var 1) (var 2) ≐ zero) (selected (var 0) (var 1) (var 2) ≐ bound (var 0) (var 1))) :=
  closeUniv 3 (cover_bit_zero_iff _ _ _)
theorem actual_supplied_cover_bit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (family (var 1) (var 2) ⟶ covered (var 0) (var 1) (var 2) ⟶ coverBit (var 0) (length (var 1)) (var 2) ≐ one) :=
  closeUniv 3 (.impI (.impI (source_cover_bit _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_returned_global_cover_bit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (sndT (sndT (sndT (run (var 0) (var 1) (var 2)))) ≐ coverBit (var 0) (var 1) (var 2)) := closeUniv 3 (returned_bit _ _ _)

theorem actual_candidate_test_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (Fm.iff (test (var 0) (var 1) (var 2) (var 3) ≐ one) (certified (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (test_iff _ _ _ _)
theorem actual_candidate_test_rejection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (Fm.iff (test (var 0) (var 1) (var 2) (var 3) ≐ zero) (neg (certified (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (test_zero_iff _ _ _ _)
theorem actual_candidate_least_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (selected (var 0) (var 1) (var 2)) ⟶ test (var 0) (var 1) (var 2) (var 3) ≐ zero) :=
  closeUniv 4 (.impI (selected_least _ _ _ _ Prf.hyp0))
theorem actual_default_cover_rejection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (selected (var 0) (var 1) (var 2) ≐ bound (var 0) (var 1) ⟶ lt (var 3) (bound (var 0) (var 1)) ⟶
      neg (certified (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (default_rejects _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_supplied_cover_search_success_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (family (var 1) (var 2) ⟶ covered (var 0) (var 1) (var 2) ⟶
      lt (selected (var 0) (length (var 1)) (var 2)) (bound (var 0) (length (var 1))) ⋏
        certified (var 0) (length (var 1)) (var 2) (selected (var 0) (length (var 1)) (var 2))) :=
  closeUniv 3 (.impI (.impI (source_success _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_cover_test_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (app testF ![var 0,var 1,var 2,var 3] ≐ test (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (test_program_at _ _ _ _)
theorem actual_cover_search_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_source_cover_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (family (var 1) (var 2) ⟶ covered (var 0) (var 1) (var 2) ⟶
      family (fstT (sndT (run (var 0) (length (var 1)) (var 2)))) (var 2) ⋏
        covered (var 0) (fstT (sndT (run (var 0) (length (var 1)) (var 2)))) (var 2)) :=
  closeUniv 3 (.impI (.impI (returned_source_cover _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalSubspaceCoverSearch
