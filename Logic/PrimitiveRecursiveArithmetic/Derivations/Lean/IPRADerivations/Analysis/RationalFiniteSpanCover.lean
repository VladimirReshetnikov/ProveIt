import IPRADerivations.Analysis.RationalSubtupleSpan
import IPRADerivations.Analysis.RationalOriginalSpanMembership

/-!
# Actual finite covers normalized to spans of subtuples

For each supplied rational span, the original membership classifier produces
one binary digit for each original tuple position. Its actual mixed-radix
code is below 2^t and decodes to exactly those digits. The mask-selected raw
subtuple therefore retains exactly the qualifying original vectors. A given
proper finite cover becomes an actual equally long family of proper subtuple
spans covering the same tuple. No quantitative cover-existence theorem is
assumed proved, and no global cover of an unbounded set is constructed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalFiniteSpanCover

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalRowSpanGaussianEmbedding (hasCoefficients)
open RationalSuperellipticSubspace (properSpan)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Foundations.MixedRadix (Cd Pl dP)
open ConciseIPRA.PTm (zero succ app)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def memberBit (A N T i : PTm n) : PTm n := eqb
  (RationalOriginalSpanMembership.test A (length A) N (entry T i)) one
def data (A N T : PTm n) : PTm n := pairT A (pairT N T)
def digitBody : PTm 2 := memberBit (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def mask (A N T : PTm n) : PTm n := Cd (two : PTm 2) digitBody (length T) (data A N T)
def subtuple (A N T : PTm n) : PTm n := RationalSubtupleSpan.selected T (mask A N T)
def count (A N T : PTm n) : PTm n := RationalSubtupleSpan.size T (mask A N T)
def position (A N T r : PTm n) : PTm n := RationalSubtupleSpan.selectedIndex T (mask A N T) r

@[simp] theorem subst_memberBit {q : ℕ} (σ : Fin n → PTm q) (A N T i : PTm n) :
    Syn.subst σ (memberBit A N T i) = memberBit (Syn.subst σ A) (Syn.subst σ N) (Syn.subst σ T) (Syn.subst σ i) := by simp [memberBit]
@[simp] theorem subst_data {q : ℕ} (σ : Fin n → PTm q) (A N T : PTm n) :
    Syn.subst σ (data A N T) = data (Syn.subst σ A) (Syn.subst σ N) (Syn.subst σ T) := by simp [data]
@[simp] theorem subst_mask {q : ℕ} (σ : Fin n → PTm q) (A N T : PTm n) :
    Syn.subst σ (mask A N T) = mask (Syn.subst σ A) (Syn.subst σ N) (Syn.subst σ T) := by simp [mask]
@[simp] theorem subst_subtuple {q : ℕ} (σ : Fin n → PTm q) (A N T : PTm n) :
    Syn.subst σ (subtuple A N T) = subtuple (Syn.subst σ A) (Syn.subst σ N) (Syn.subst σ T) := by simp [subtuple]
@[simp] theorem subst_count {q : ℕ} (σ : Fin n → PTm q) (A N T : PTm n) :
    Syn.subst σ (count A N T) = count (Syn.subst σ A) (Syn.subst σ N) (Syn.subst σ T) := by simp [count]
@[simp] theorem subst_position {q : ℕ} (σ : Fin n → PTm q) (A N T r : PTm n) :
    Syn.subst σ (position A N T r) = position (Syn.subst σ A) (Syn.subst σ N) (Syn.subst σ T) (Syn.subst σ r) := by simp [position]

theorem member_bit_bound (A N T i : PTm n) : Γ ⊢[PRAAx] lt (memberBit A N T i) two := by
  refine .orE (eq_or_ne (RationalOriginalSpanMembership.test A (length A) N (entry T i)) one) ?_ ?_
  · exact lt_congr (eqb_of_eq Prf.hyp0).eqSymm (.eqRefl _) (le_refl two)
  · exact lt_congr (eqb_of_ne Prf.hyp0).eqSymm (.eqRefl _) (le_succ_self one)

theorem member_bit_complete (A N T i : PTm n) (hm : Γ ⊢[PRAAx] hasCoefficients A (length A) N (entry T i)) : Γ ⊢[PRAAx]
    memberBit A N T i ≐ one := eqb_of_eq (RationalOriginalSpanMembership.test_complete _ _ _ _ hm)
theorem member_bit_sound (A N T i : PTm n) (hm : Γ ⊢[PRAAx] neg (memberBit A N T i ≐ zero)) : Γ ⊢[PRAAx]
    hasCoefficients A (length A) N (entry T i) :=
  (RationalOriginalSpanMembership.test_iff _ _ _ _).iffMp (Foundations.FiniteFiberGrouping.equality_of_nonzero_eqb hm)

private theorem member_bit_congr {A B N M T S i j : PTm n} (hA : Γ ⊢[PRAAx] A ≐ B)
    (hN : Γ ⊢[PRAAx] N ≐ M) (hT : Γ ⊢[PRAAx] T ≐ S) (hi : Γ ⊢[PRAAx] i ≐ j) : Γ ⊢[PRAAx]
    memberBit A N T i ≐ memberBit B M S j := by
  simpa only [subst_memberBit,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (memberBit (var 0) (var 1) (var 2) (var 3) : PTm 4) (σ := ![A,N,T,i]) (σ' := ![B,M,S,j])
      (fun r => by fin_cases r; exact hA; exact hN; exact hT; exact hi)

theorem digit_body_at (A N T i : PTm n) : Γ ⊢[PRAAx] inst2 digitBody i (data A N T) ≐ memberBit A N T i := by
  simp only [digitBody,inst2,subst_memberBit,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact member_bit_congr (fst_pair _ _) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)) (.eqRefl _)
theorem places (k p : PTm n) : Γ ⊢[PRAAx] Pl (two : PTm 2) k p ≐ pw two k := by
  apply prod_const_of
  refine .allI (.impI ?_)
  simpa [inst2,Syn.shift,two,one] using
    (Prf.eqRefl (Γ := lt (var 0) (Syn.shift k) :: Γ.map Fm.shift) (two : PTm (n+1)))

theorem mask_bound (A N T : PTm n) : Γ ⊢[PRAAx] lt (mask A N T) (pw two (length T)) := by
  have digits : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift (length T)) ⟶
      lt (inst2 digitBody (var 0) (Syn.shift (data A N T))) (inst2 (two : PTm 2) (var 0) (Syn.shift (data A N T)))) := by
    refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_data,inst2,two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      lt_congr (digit_body_at (Syn.shift A) (Syn.shift N) (Syn.shift T) (var 0)).eqSymm (.eqRefl _)
        (member_bit_bound (Γ := lt (var 0) (Syn.shift (length T)) :: Γ.map Fm.shift) _ _ _ _)
  exact lt_congr (.eqRefl _) (places (length T) (data A N T)) (Foundations.MixedRadix.code_lt _ _ _ _ digits)

theorem mask_digit (A N T i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length T)) : Γ ⊢[PRAAx]
    RationalSubtupleSpan.bit (mask A N T) i ≐ memberBit A N T i := by
  let t := monus (length T) (succ i)
  have span : Γ ⊢[PRAAx] succ i + t ≐ length T := (eq_add_of_le hi).eqSymm
  have digits : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift (succ i+t)) ⟶
      lt (inst2 digitBody (var 0) (Syn.shift (data A N T))) (inst2 (two : PTm 2) (var 0) (Syn.shift (data A N T)))) := by
    refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_data,inst2,two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      lt_congr (digit_body_at (Syn.shift A) (Syn.shift N) (Syn.shift T) (var 0)).eqSymm (.eqRefl _)
        (member_bit_bound (Γ := lt (var 0) (Syn.shift (succ i+t)) :: Γ.map Fm.shift) _ _ _ _)
  have codeEq : Γ ⊢[PRAAx] Cd (two : PTm 2) digitBody (succ i+t) (data A N T) ≐ mask A N T :=
    congrAp2 (sumF (dP (two : PTm 2) digitBody)) span (.eqRefl _)
  have decoded := Foundations.MixedRadix.decode digits
  have twoAt : inst2 (two : PTm 2) i (data A N T) = (two : PTm n) := by simp [inst2,two,one]
  rw [twoAt] at decoded
  exact (congrAp2 remF (congrAp2 quoF codeEq (places i (data A N T))) (.eqRefl two)).eqSymm.eqTrans
    (decoded.eqTrans (digit_body_at A N T i))

theorem source_members (A N T : PTm n) : Γ ⊢[PRAAx]
    RationalSubtupleSpan.sourceMembers A (length A) N T (mask A N T) := by
  refine .allI (.impI (.impI ?_))
  let Δ := neg (RationalSubtupleSpan.bit (mask (Syn.shift A) (Syn.shift N) (Syn.shift T)) (var 0) ≐ zero) ::
    lt (var 0) (length (Syn.shift T)) :: Γ.map Fm.shift
  have hb : Δ ⊢[PRAAx] neg (memberBit (Syn.shift A) (Syn.shift N) (Syn.shift T) (var 0) ≐ zero) :=
    .impI (.impE Prf.hyp1 ((mask_digit (Γ := Δ) _ _ _ _ Prf.hyp1).wk.eqTrans Prf.hyp0))
  simpa only [Δ,Syn.shift,subst_mask,Foundations.SequenceComposition.subst_length] using member_bit_sound _ _ _ _ hb

theorem subtuple_length (A N T : PTm n) : Γ ⊢[PRAAx] length (subtuple A N T) ≐ count A N T :=
  RationalSubtupleSpan.selected_length _ _
theorem subtuple_lookup (A N T r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count A N T)) : Γ ⊢[PRAAx]
    entry (subtuple A N T) r ≐ entry T (position A N T r) := RationalSubtupleSpan.selected_lookup _ _ _ hr
theorem subtuple_proper (A N T : PTm n) (hp : Γ ⊢[PRAAx] properSpan A (length A) N) : Γ ⊢[PRAAx]
    properSpan (subtuple A N T) (count A N T) N := RationalSubtupleSpan.selected_proper _ _ _ _ _ hp (source_members A N T)
theorem original_member_retained (A N T i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length T))
    (hm : Γ ⊢[PRAAx] hasCoefficients A (length A) N (entry T i)) : Γ ⊢[PRAAx]
    hasCoefficients (subtuple A N T) (count A N T) N (entry T i) := by
  have oneBit := (mask_digit A N T i hi).eqTrans (member_bit_complete A N T i hm)
  exact RationalSubtupleSpan.retained_vector_belongs T (mask A N T) N i hi
    (.impI (succ_ne_zero (oneBit.wk.eqSymm.eqTrans Prf.hyp0)))

private theorem proper_congr {A B R S N M : PTm n} (hA : Γ ⊢[PRAAx] A ≐ B)
    (hR : Γ ⊢[PRAAx] R ≐ S) (hN : Γ ⊢[PRAAx] N ≐ M) (h : Γ ⊢[PRAAx] properSpan A R N) :
    Γ ⊢[PRAAx] properSpan B S M := by
  simpa only [RationalSuperellipticSubspace.subst_properSpan,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqSubst (properSpan (var 0) (var 1) (var 2) : Fm PTm 3) ![A,R,N] ![B,S,M]
      (fun i => by fin_cases i; exact hA; exact hR; exact hN)
      (by simpa only [RationalSuperellipticSubspace.subst_properSpan,Syn.subst_var,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using h)
private theorem member_congr {A B R S N M v w : PTm n} (hA : Γ ⊢[PRAAx] A ≐ B)
    (hR : Γ ⊢[PRAAx] R ≐ S) (hN : Γ ⊢[PRAAx] N ≐ M) (hv : Γ ⊢[PRAAx] v ≐ w)
    (h : Γ ⊢[PRAAx] hasCoefficients A R N v) : Γ ⊢[PRAAx] hasCoefficients B S M w := by
  simpa only [RationalRowSpanGaussianEmbedding.subst_hasCoefficients,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqSubst (hasCoefficients (var 0) (var 1) (var 2) (var 3) : Fm PTm 4) ![A,R,N,v] ![B,S,M,w]
      (fun i => by fin_cases i; exact hA; exact hR; exact hN; exact hv)
      (by simpa only [RationalRowSpanGaussianEmbedding.subst_hasCoefficients,Syn.subst_var,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using h)
private theorem subtuple_congr {A B N M T S : PTm n} (hA : Γ ⊢[PRAAx] A ≐ B)
    (hN : Γ ⊢[PRAAx] N ≐ M) (hT : Γ ⊢[PRAAx] T ≐ S) : Γ ⊢[PRAAx] subtuple A N T ≐ subtuple B M S := by
  simpa only [subst_subtuple,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (subtuple (var 0) (var 1) (var 2) : PTm 3) (σ := ![A,N,T]) (σ' := ![B,M,S])
      (fun i => by fin_cases i; exact hA; exact hN; exact hT)

/-- A family consists of actual original rational row matrices. -/
def family (D N : PTm n) : Fm PTm n := .all (lt (var 0) (length (Syn.shift D)) ⟶
  properSpan (entry (Syn.shift D) (var 0)) (length (entry (Syn.shift D) (var 0))) (Syn.shift N))
def coveredAt (D N v : PTm n) : Fm PTm n := .ex (lt (var 0) (length (Syn.shift D)) ⋏
  hasCoefficients (entry (Syn.shift D) (var 0)) (length (entry (Syn.shift D) (var 0))) (Syn.shift N) (Syn.shift v))
def covered (T D N : PTm n) : Fm PTm n := .all (lt (var 0) (length (Syn.shift T)) ⟶
  coveredAt (Syn.shift D) (Syn.shift N) (entry (Syn.shift T) (var 0)))
def familyBody : PTm 2 := subtuple (entry (fstT (var 1)) (var 0))
  (fstT (sndT (var 1))) (sndT (sndT (var 1)))
def normalized (D N T : PTm n) : PTm n := sequence familyBody (length D) (data D N T)

@[simp] theorem subst_family {q : ℕ} (σ : Fin n → PTm q) (D N : PTm n) :
    (family D N).subst σ = family (Syn.subst σ D) (Syn.subst σ N) := by simp [family,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_coveredAt {q : ℕ} (σ : Fin n → PTm q) (D N v : PTm n) :
    (coveredAt D N v).subst σ = coveredAt (Syn.subst σ D) (Syn.subst σ N) (Syn.subst σ v) := by simp [coveredAt,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_covered {q : ℕ} (σ : Fin n → PTm q) (T D N : PTm n) :
    (covered T D N).subst σ = covered (Syn.subst σ T) (Syn.subst σ D) (Syn.subst σ N) := by simp [covered,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_normalized {q : ℕ} (σ : Fin n → PTm q) (D N T : PTm n) :
    Syn.subst σ (normalized D N T) = normalized (Syn.subst σ D) (Syn.subst σ N) (Syn.subst σ T) := by simp [normalized]

theorem family_body_at (D N T g : PTm n) : Γ ⊢[PRAAx]
    inst2 familyBody g (data D N T) ≐ subtuple (entry D g) N T := by
  simp only [familyBody,inst2,subst_subtuple,Foundations.MasterCertificate.subst_entry,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact subtuple_congr (entry_congr (fst_pair _ _) (.eqRefl _))
    ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)) ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))
theorem normalized_length (D N T : PTm n) : Γ ⊢[PRAAx] length (normalized D N T) ≐ length D := sequence_length _ _ _
theorem normalized_lookup (D N T g : PTm n) (hg : Γ ⊢[PRAAx] lt g (length D)) : Γ ⊢[PRAAx]
    entry (normalized D N T) g ≐ subtuple (entry D g) N T :=
  (sequence_decode familyBody (x := data D N T) hg).eqTrans (family_body_at _ _ _ _)

theorem family_at (D N g : PTm n) (h : Γ ⊢[PRAAx] family D N) (hg : Γ ⊢[PRAAx] lt g (length D)) : Γ ⊢[PRAAx]
    properSpan (entry D g) (length (entry D g)) N := by
  have rule : Γ ⊢[PRAAx] lt g (length D) ⟶ properSpan (entry D g) (length (entry D g)) N := by simpa [family] using h.allE g
  exact .impE rule hg

theorem normalized_proper_at (D N T g : PTm n) (h : Γ ⊢[PRAAx] family D N) (hg : Γ ⊢[PRAAx] lt g (length D)) : Γ ⊢[PRAAx]
    properSpan (entry (normalized D N T) g) (length (entry (normalized D N T) g)) N := by
  have lookup := normalized_lookup D N T g hg
  have proper := subtuple_proper (entry D g) N T (family_at D N g h hg)
  exact proper_congr lookup.eqSymm
    ((subtuple_length (entry D g) N T).eqSymm.eqTrans (congrFst lookup).eqSymm) (.eqRefl N) proper

theorem normalized_family (D N T : PTm n) (h : Γ ⊢[PRAAx] family D N) : Γ ⊢[PRAAx] family (normalized D N T) N := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] family (Syn.shift D) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (normalized (Syn.shift D) (Syn.shift N) (Syn.shift T))) :: Γ.map Fm.shift
  have hg : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift D)) :=
    lt_congr (.eqRefl _) (normalized_length _ _ _) Prf.hyp0
  simpa only [Δ,Syn.shift,subst_normalized] using normalized_proper_at _ _ _ _ hs.wk hg

theorem covered_at (T D N i : PTm n) (h : Γ ⊢[PRAAx] covered T D N) (hi : Γ ⊢[PRAAx] lt i (length T)) : Γ ⊢[PRAAx]
    coveredAt D N (entry T i) := by
  have rule : Γ ⊢[PRAAx] lt i (length T) ⟶ coveredAt D N (entry T i) := by simpa [covered] using h.allE i
  exact .impE rule hi

theorem member_normalized (D N T g i : PTm n) (hg : Γ ⊢[PRAAx] lt g (length D)) (hi : Γ ⊢[PRAAx] lt i (length T))
    (hm : Γ ⊢[PRAAx] hasCoefficients (entry D g) (length (entry D g)) N (entry T i)) : Γ ⊢[PRAAx]
    hasCoefficients (entry (normalized D N T) g) (length (entry (normalized D N T) g)) N (entry T i) := by
  have lookup := normalized_lookup D N T g hg
  exact member_congr lookup.eqSymm
    ((subtuple_length (entry D g) N T).eqSymm.eqTrans (congrFst lookup).eqSymm) (.eqRefl N) (.eqRefl _)
      (original_member_retained (entry D g) N T i hi hm)

theorem covered_at_normalized (T D N i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length T))
    (h : Γ ⊢[PRAAx] coveredAt D N (entry T i)) : Γ ⊢[PRAAx] coveredAt (normalized D N T) N (entry T i) := by
  have his : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift i) (length (Syn.shift T)) := by simpa [Fm.shift,Syn.shift] using hi.shift
  refine .exE h ?_
  let Δ := (lt (var 0) (length (Syn.shift D)) ⋏ hasCoefficients (entry (Syn.shift D) (var 0))
    (length (entry (Syn.shift D) (var 0))) (Syn.shift N) (entry (Syn.shift T) (Syn.shift i))) :: Γ.map Fm.shift
  have member := member_normalized (Γ := Δ) (Syn.shift D) (Syn.shift N) (Syn.shift T) (var 0) (Syn.shift i)
    (.andE₁ Prf.hyp0) his.wk (.andE₂ Prf.hyp0)
  have hg : Δ ⊢[PRAAx] lt (var 0) (length (normalized (Syn.shift D) (Syn.shift N) (Syn.shift T))) :=
    lt_congr (.eqRefl _) (normalized_length _ _ _).eqSymm (.andE₁ Prf.hyp0)
  have result : Δ ⊢[PRAAx] coveredAt (normalized (Syn.shift D) (Syn.shift N) (Syn.shift T)) (Syn.shift N) (entry (Syn.shift T) (Syn.shift i)) := by
    refine .exI (var 0) ?_
    simpa only [coveredAt,Fm.subst_and,subst_lt,RationalRowSpanGaussianEmbedding.subst_hasCoefficients,
      Foundations.MasterCertificate.subst_entry,Foundations.SequenceComposition.subst_length,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.andI hg member
  simpa only [Δ,Fm.shift,Syn.shift,subst_normalized,subst_coveredAt,Foundations.MasterCertificate.subst_entry] using result

theorem normalized_coverage (T D N : PTm n) (h : Γ ⊢[PRAAx] covered T D N) : Γ ⊢[PRAAx] covered T (normalized D N T) N := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] covered (Syn.shift T) (Syn.shift D) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_normalized] using covered_at_normalized (Syn.shift T) (Syn.shift D) (Syn.shift N) (var 0)
    (Γ := lt (var 0) (length (Syn.shift T)) :: Γ.map Fm.shift) Prf.hyp0 (covered_at _ _ _ _ hs.wk Prf.hyp0)

theorem subtuple_source_member (A N T r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count A N T)) : Γ ⊢[PRAAx]
    hasCoefficients A (length A) N (entry T (position A N T r)) :=
  RationalSubtupleSpan.selected_source_member _ _ _ _ _ _ (source_members A N T) hr

theorem subtuple_count_bound (A N T : PTm n) : Γ ⊢[PRAAx] le (count A N T) (length T) := RationalSubtupleSpan.size_bound _ _

private theorem mask_congr {A B N M T S : PTm n} (hA : Γ ⊢[PRAAx] A ≐ B)
    (hN : Γ ⊢[PRAAx] N ≐ M) (hT : Γ ⊢[PRAAx] T ≐ S) : Γ ⊢[PRAAx] mask A N T ≐ mask B M S := by
  simpa only [subst_mask,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (mask (var 0) (var 1) (var 2) : PTm 3) (σ := ![A,N,T]) (σ' := ![B,M,S])
      (fun i => by fin_cases i; exact hA; exact hN; exact hT)

def maskBody : PTm 2 := mask (entry (fstT (var 1)) (var 0)) (fstT (sndT (var 1))) (sndT (sndT (var 1)))
def masks (D N T : PTm n) : PTm n := sequence maskBody (length D) (data D N T)
@[simp] theorem subst_masks {q : ℕ} (σ : Fin n → PTm q) (D N T : PTm n) :
    Syn.subst σ (masks D N T) = masks (Syn.subst σ D) (Syn.subst σ N) (Syn.subst σ T) := by simp [masks]
theorem mask_body_at (D N T g : PTm n) : Γ ⊢[PRAAx] inst2 maskBody g (data D N T) ≐ mask (entry D g) N T := by
  simp only [maskBody,inst2,subst_mask,Foundations.MasterCertificate.subst_entry,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact mask_congr (entry_congr (fst_pair _ _) (.eqRefl _))
    ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)) ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))
theorem masks_length (D N T : PTm n) : Γ ⊢[PRAAx] length (masks D N T) ≐ length D := sequence_length _ _ _
theorem masks_lookup (D N T g : PTm n) (hg : Γ ⊢[PRAAx] lt g (length D)) : Γ ⊢[PRAAx]
    entry (masks D N T) g ≐ mask (entry D g) N T :=
  (sequence_decode maskBody (x := data D N T) hg).eqTrans (mask_body_at _ _ _ _)
theorem masks_bound (D N T g : PTm n) (hg : Γ ⊢[PRAAx] lt g (length D)) : Γ ⊢[PRAAx]
    lt (entry (masks D N T) g) (pw two (length T)) :=
  lt_congr (masks_lookup D N T g hg).eqSymm (.eqRefl _) (mask_bound (entry D g) N T)

/-- Exact finite normalization; cover existence remains an original hypothesis. -/
def certificate (T D N E : PTm n) : Fm PTm n := length E ≐ length D ⋏ (family E N ⋏ covered T E N)
@[simp] theorem subst_certificate {q : ℕ} (σ : Fin n → PTm q) (T D N E : PTm n) :
    (certificate T D N E).subst σ = certificate (Syn.subst σ T) (Syn.subst σ D) (Syn.subst σ N) (Syn.subst σ E) := by simp [certificate]
theorem produced_certificate (T D N : PTm n) (hf : Γ ⊢[PRAAx] family D N) (hc : Γ ⊢[PRAAx] covered T D N) : Γ ⊢[PRAAx]
    certificate T D N (normalized D N T) :=
  .andI (normalized_length D N T) (.andI (normalized_family D N T hf) (normalized_coverage T D N hc))

def output (T D N : PTm n) : PTm n := pairT (normalized D N T) (pairT (masks D N T) T)
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (T D N : PTm n) : PTm n := app outputF ![T,D,N]
@[simp] theorem subst_output {q : ℕ} (σ : Fin n → PTm q) (T D N : PTm n) :
    Syn.subst σ (output T D N) = output (Syn.subst σ T) (Syn.subst σ D) (Syn.subst σ N) := by simp [output]
@[simp] theorem subst_run {q : ℕ} (σ : Fin n → PTm q) (T D N : PTm n) :
    Syn.subst σ (run T D N) = run (Syn.subst σ T) (Syn.subst σ D) (Syn.subst σ N) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (T D N : PTm n) : Γ ⊢[PRAAx] run T D N ≐ output T D N := by
  simpa [run,outputF,output,Matrix.cons_val_succ',Matrix.cons_val_zero'] using
    toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![T,D,N]
theorem returned_family (T D N : PTm n) : Γ ⊢[PRAAx] fstT (run T D N) ≐ normalized D N T :=
  (congrFst (program_at T D N)).eqTrans (fst_pair _ _)
theorem returned_masks (T D N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run T D N)) ≐ masks D N T :=
  (congrFst ((congrSnd (program_at T D N)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_tuple (T D N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run T D N)) ≐ T :=
  (congrSnd ((congrSnd (program_at T D N)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_certificate (T D N : PTm n) (hf : Γ ⊢[PRAAx] family D N) (hc : Γ ⊢[PRAAx] covered T D N) : Γ ⊢[PRAAx]
    certificate T D N (fstT (run T D N)) := by
  let φ := certificate (Syn.shift T) (Syn.shift D) (Syn.shift N) (var 0)
  have start : Γ ⊢[PRAAx] φ.subst (Syn.inst (normalized D N T)) := by
    simpa only [φ,subst_certificate,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using produced_certificate T D N hf hc
  simpa only [φ,subst_certificate,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Prf.eqSubst1 φ (returned_family T D N).eqSymm start

theorem actual_membership_mask_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (mask (var 0) (var 1) (var 2)) (pw two (length (var 2)))) := closeUniv 3 (mask_bound _ _ _)
theorem actual_membership_mask_decode_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (length (var 2)) ⟶ RationalSubtupleSpan.bit (mask (var 0) (var 1) (var 2)) (var 3) ≐
      memberBit (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (.impI (mask_digit _ _ _ _ Prf.hyp0))
theorem actual_qualifying_subtuple_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (properSpan (var 0) (length (var 0)) (var 1) ⟶ properSpan (subtuple (var 0) (var 1) (var 2))
      (count (var 0) (var 1) (var 2)) (var 1)) := closeUniv 3 (.impI (subtuple_proper _ _ _ Prf.hyp0))
theorem actual_source_member_retained_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (length (var 2)) ⟶ hasCoefficients (var 0) (length (var 0)) (var 1) (entry (var 2) (var 3)) ⟶
      hasCoefficients (subtuple (var 0) (var 1) (var 2)) (count (var 0) (var 1) (var 2)) (var 1) (entry (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (original_member_retained _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_normalized_family_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (family (var 0) (var 1) ⟶ family (normalized (var 0) (var 1) (var 2)) (var 1)) :=
  closeUniv 3 (.impI (normalized_family _ _ _ Prf.hyp0))
theorem actual_normalized_cover_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (covered (var 0) (var 1) (var 2) ⟶ covered (var 0) (normalized (var 1) (var 2) (var 0)) (var 2)) :=
  closeUniv 3 (.impI (normalized_coverage _ _ _ Prf.hyp0))
theorem actual_finite_cover_normalization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (family (var 1) (var 2) ⟶ covered (var 0) (var 1) (var 2) ⟶
      certificate (var 0) (var 1) (var 2) (normalized (var 1) (var 2) (var 0))) :=
  closeUniv 3 (.impI (.impI (produced_certificate _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_finite_cover_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_finite_cover_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (family (var 1) (var 2) ⟶ covered (var 0) (var 1) (var 2) ⟶
      certificate (var 0) (var 1) (var 2) (fstT (run (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (.impI (returned_certificate _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalFiniteSpanCover
