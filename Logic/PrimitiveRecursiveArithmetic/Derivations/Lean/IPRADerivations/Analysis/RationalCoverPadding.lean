import IPRADerivations.Analysis.RationalSubspaceCoverSearch

/-!
# Padding a supplied rational span cover

The actual padded family retains the original matrices and appends empty
row matrices. In positive ambient dimension, an empty matrix is proper,
because its actual pivot history admits no pivot row. The global finite
cover bit is therefore equivalent to existence of a supplied family of
at most the requested size.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalCoverPadding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalFiniteSpanCover (family covered coveredAt)
open RationalSuperellipticSubspace (properSpan)
open RationalRowSpanGaussianEmbedding (hasCoefficients matrix)
open RationalSubspaceCoverSearch (coverBit chosen selected)
open GaussianRationalRankNullityCriterion (finalHistory)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_decode sequence_length)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def empty : PTm n := pairT zero zero
def rowAt (D g : PTm n) : PTm n :=
  RationalArithmetic.select (Signum.sg (monus (length D) g)) empty (entry D g)
def rowBody : PTm 2 := rowAt (var 1) (var 0)
def padded (D M : PTm n) : PTm n := sequence rowBody M D

@[simp] theorem subst_empty {k : ℕ} (σ : Fin n → PTm k) : Syn.subst σ (empty : PTm n) = empty := by simp [empty]
@[simp] theorem subst_rowAt {k : ℕ} (σ : Fin n → PTm k) (D g : PTm n) :
    Syn.subst σ (rowAt D g) = rowAt (Syn.subst σ D) (Syn.subst σ g) := by
  simp [rowAt,Signum.sg]
@[simp] theorem subst_padded {k : ℕ} (σ : Fin n → PTm k) (D M : PTm n) :
    Syn.subst σ (padded D M) = padded (Syn.subst σ D) (Syn.subst σ M) := by simp [padded]

theorem padded_length (D M : PTm n) : Γ ⊢[PRAAx] length (padded D M) ≐ M := sequence_length _ _ _
theorem padded_lookup (D M g : PTm n) (hg : Γ ⊢[PRAAx] lt g M) :
    Γ ⊢[PRAAx] entry (padded D M) g ≐ rowAt D g := by
  simpa [padded,rowBody,inst2] using sequence_decode (Γ := Γ) rowBody (x := D) hg

theorem padded_retains (D M g : PTm n) (hg : Γ ⊢[PRAAx] lt g M) (hd : Γ ⊢[PRAAx] lt g (length D)) :
    Γ ⊢[PRAAx] entry (padded D M) g ≐ entry D g :=
  (padded_lookup D M g hg).eqTrans (RationalArithmetic.select_one _ _ _ (AnalyticNumberTheory.Totatives.sg_lt hd))

theorem padded_empty (D M g : PTm n) (hg : Γ ⊢[PRAAx] lt g M) (hd : Γ ⊢[PRAAx] le (length D) g) :
    Γ ⊢[PRAAx] entry (padded D M) g ≐ empty :=
  (padded_lookup D M g hg).eqTrans (RationalArithmetic.select_zero _ _ _ (AnalyticNumberTheory.Totatives.sg_le hd))

theorem empty_proper (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] properSpan empty (length empty) N := by
  let H := finalHistory (matrix empty (length empty) N) (length empty) N
  have len : Γ ⊢[PRAAx] length (empty : PTm n) ≐ zero := fst_pair _ _
  have tag : Γ ⊢[PRAAx] entry H zero ≐ zero := by
    refine .orE (eq_or_ne (entry H zero) zero) Prf.hyp0 ?_
    have bound := GaussianRationalRankNullityCriterion.tag_row_bound
      (matrix empty (length empty) N) (length empty) N zero hN.wk Prf.hyp0
    exact le_lt_absurd _ (zero_le _) (lt_congr (.eqRefl _) len.wk bound)
  exact RationalSuperellipticSubspace.proper_of_deficit _ _ _
    (GaussianRationalPivotHistoryCount.count_lt_of_zero H N zero hN tag)

private theorem proper_congr {A B N : PTm n} (h : Γ ⊢[PRAAx] A ≐ B)
    (p : Γ ⊢[PRAAx] properSpan A (length A) N) : Γ ⊢[PRAAx] properSpan B (length B) N := by
  let φ := properSpan (var 0) (length (var 0)) (Syn.shift N)
  have p' : Γ ⊢[PRAAx] φ.subst (Syn.inst A) := by simpa [φ] using p
  simpa [φ] using Prf.eqSubst1 φ h p'

private theorem member_congr {A B N v : PTm n} (h : Γ ⊢[PRAAx] A ≐ B)
    (p : Γ ⊢[PRAAx] hasCoefficients A (length A) N v) : Γ ⊢[PRAAx] hasCoefficients B (length B) N v := by
  let φ := hasCoefficients (var 0) (length (var 0)) (Syn.shift N) (Syn.shift v)
  have p' : Γ ⊢[PRAAx] φ.subst (Syn.inst A) := by simpa [φ] using p
  simpa [φ] using Prf.eqSubst1 φ h p'

theorem padded_proper_at (D M N g : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hf : Γ ⊢[PRAAx] family D N) (hg : Γ ⊢[PRAAx] lt g M) : Γ ⊢[PRAAx]
    properSpan (entry (padded D M) g) (length (entry (padded D M) g)) N := by
  refine .orE (lt_or_le g (length D)) ?_ ?_
  · exact proper_congr (padded_retains _ _ _ hg.wk Prf.hyp0).eqSymm
      (RationalFiniteSpanCover.family_at D N g hf.wk Prf.hyp0)
  · exact proper_congr (padded_empty _ _ _ hg.wk Prf.hyp0).eqSymm (empty_proper N hN.wk)

theorem padded_family (D M N : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hf : Γ ⊢[PRAAx] family D N) :
    Γ ⊢[PRAAx] family (padded D M) N := by
  refine .allI (.impI ?_)
  have nn : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Syn.shift,Fm.shift,one] using hN.shift
  have ff : Γ.map Fm.shift ⊢[PRAAx] family (Syn.shift D) (Syn.shift N) := by simpa [Syn.shift,Fm.shift] using hf.shift
  have range : (lt (var 0) (length (Syn.shift (padded D M))) :: Γ.map Fm.shift) ⊢[PRAAx]
      lt (var 0) (length (padded (Syn.shift D) (Syn.shift M))) := by
    simpa [Syn.shift] using Prf.hyp0
  simpa [Syn.shift] using padded_proper_at (Syn.shift D) (Syn.shift M) (Syn.shift N) (var 0) nn.wk ff.wk
    (lt_congr (.eqRefl _) (padded_length _ _) range)

theorem padded_covers_at (D M N v : PTm n) (hm : Γ ⊢[PRAAx] le (length D) M)
    (hc : Γ ⊢[PRAAx] coveredAt D N v) : Γ ⊢[PRAAx] coveredAt (padded D M) N v := by
  let D' := Syn.shift D
  let M' := Syn.shift M
  let N' := Syn.shift N
  let v' := Syn.shift v
  let Δ := (lt (var 0) (length D') ⋏ hasCoefficients (entry D' (var 0))
    (length (entry D' (var 0))) N' v') :: Γ.map Fm.shift
  have mm : Δ ⊢[PRAAx] le (length D') M' := by simpa [Δ,D',M',Syn.shift,Fm.shift] using hm.shift.wk
  refine .exE hc ?_
  have source : Δ ⊢[PRAAx] lt (var 0) (length D') := .andE₁ Prf.hyp0
  have target := lt_of_lt_of_le source mm
  have retained := padded_retains D' M' (var 0) target source
  have member : Δ ⊢[PRAAx] hasCoefficients (entry D' (var 0)) (length (entry D' (var 0))) N' v' := .andE₂ Prf.hyp0
  have result : Δ ⊢[PRAAx] coveredAt (padded D' M') N' v' := by
    refine .exI (var 0) ?_
    simpa [coveredAt] using Prf.andI (lt_congr (.eqRefl _) (padded_length D' M').eqSymm target)
      (member_congr retained.eqSymm member)
  simpa [Δ,D',M',N',v',Syn.shift,Fm.shift] using result

theorem padded_coverage (T D M N : PTm n) (hm : Γ ⊢[PRAAx] le (length D) M)
    (hc : Γ ⊢[PRAAx] covered T D N) : Γ ⊢[PRAAx] covered T (padded D M) N := by
  refine .allI (.impI ?_)
  have mm : Γ.map Fm.shift ⊢[PRAAx] le (length (Syn.shift D)) (Syn.shift M) := by
    simpa [Syn.shift,Fm.shift] using hm.shift
  have cc : Γ.map Fm.shift ⊢[PRAAx] covered (Syn.shift T) (Syn.shift D) (Syn.shift N) := by
    simpa [Syn.shift,Fm.shift] using hc.shift
  simpa [Syn.shift] using padded_covers_at (Syn.shift D) (Syn.shift M) (Syn.shift N)
    (entry (Syn.shift T) (var 0)) mm.wk (RationalFiniteSpanCover.covered_at _ _ _ _ cc.wk Prf.hyp0)

private theorem cover_bit_congr (T N : PTm n) {M K : PTm n} (he : Γ ⊢[PRAAx] M ≐ K) :
    Γ ⊢[PRAAx] coverBit T M N ≐ coverBit T K N := by
  simpa only [RationalSubspaceCoverSearch.subst_coverBit,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (coverBit (var 0) (var 1) (var 2) : PTm 3) (σ := ![T,M,N]) (σ' := ![T,K,N])
      (fun i => by fin_cases i; exact .eqRefl _; exact he; exact .eqRefl _)

theorem supplied_at_most_cover_bit (T D M N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hm : Γ ⊢[PRAAx] le (length D) M) (hf : Γ ⊢[PRAAx] family D N) (hc : Γ ⊢[PRAAx] covered T D N) :
    Γ ⊢[PRAAx] coverBit T M N ≐ one :=
  (cover_bit_congr T N (padded_length D M).eqSymm).eqTrans
    (RationalSubspaceCoverSearch.source_cover_bit _ _ _ (padded_family D M N hN hf) (padded_coverage T D M N hm hc))

def supplied (T M N : PTm n) : Fm PTm n := .ex
  (le (length (var 0)) (Syn.shift M) ⋏ (family (var 0) (Syn.shift N) ⋏ covered (Syn.shift T) (var 0) (Syn.shift N)))

theorem cover_bit_produces (T M N : PTm n) (h : Γ ⊢[PRAAx] coverBit T M N ≐ one) : Γ ⊢[PRAAx]
    family (chosen T M N) N ⋏ covered T (chosen T M N) N :=
  RationalSubspaceCoverSearch.test_sound T M N (selected T M N)
    (RationalSubspaceCoverSearch.selected_success _ _ _ (RationalSubspaceCoverSearch.cover_bit_found _ _ _ h))

theorem cover_bit_supplied_iff (T M N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    Fm.iff (coverBit T M N ≐ one) (supplied T M N) := by
  refine .andI (.impI ?_) (.impI ?_)
  · refine .exI (chosen T M N) ?_
    have proves : (coverBit T M N ≐ one) :: Γ ⊢[PRAAx] le (length (chosen T M N)) M :=
      le_congr (RationalSubspaceCoverSearch.chosen_length T M N).eqSymm (.eqRefl _) (le_refl M)
    simpa [supplied] using Prf.andI proves (cover_bit_produces _ _ _ Prf.hyp0)
  · refine .exE Prf.hyp0 ?_
    let T' := Syn.shift T
    let M' := Syn.shift M
    let N' := Syn.shift N
    let Δ := (le (length (var 0)) M' ⋏ (family (var 0) N' ⋏ covered T' (var 0) N')) ::
      (supplied T M N).shift :: Γ.map Fm.shift
    have nn : Δ ⊢[PRAAx] le one N' := by simpa [Δ,N',one,Syn.shift,Fm.shift] using hN.shift.wk.wk
    simpa [Δ,T',M',N',Syn.shift,Fm.shift,supplied,one] using
      supplied_at_most_cover_bit (Γ := Δ) T' (var 0) M' N' nn (.andE₁ Prf.hyp0)
        (.andE₁ (.andE₂ Prf.hyp0)) (.andE₂ (.andE₂ Prf.hyp0))

def paddedF : PR 2 := PTm.toPR (padded (var 0) (var 1))
def run (D M : PTm n) : PTm n := ap2 paddedF D M

theorem program_at (D M : PTm n) : Γ ⊢[PRAAx] run D M ≐ padded D M := by
  simpa [run,paddedF,ap2] using toPR_eq (Γ := Γ) (padded (var 0) (var 1) : PTm 2) ![D,M]

theorem returned_length (D M : PTm n) : Γ ⊢[PRAAx] length (run D M) ≐ M :=
  (congrFst (program_at D M)).eqTrans (padded_length D M)

theorem actual_empty_rational_span_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ properSpan empty (length empty) (var 0)) :=
  closeUniv 1 (.impI (empty_proper _ Prf.hyp0))

theorem actual_padded_cover_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ le (length (var 1)) (var 2) ⟶ family (var 1) (var 3) ⟶ covered (var 0) (var 1) (var 3) ⟶
      (family (padded (var 1) (var 2)) (var 3) ⋏ covered (var 0) (padded (var 1) (var 2)) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.andI
    (padded_family _ _ _ (.hyp (by simp)) Prf.hyp1)
    (padded_coverage _ _ _ _ hyp2 Prf.hyp0))))))

theorem actual_cover_bit_at_most_family_iff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ Fm.iff (coverBit (var 0) (var 1) (var 2) ≐ one) (supplied (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (cover_bit_supplied_iff _ _ _ Prf.hyp0))

theorem actual_rational_cover_padding_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((run (var 0) (var 1) ≐ padded (var 0) (var 1)) ⋏ length (run (var 0) (var 1)) ≐ var 1) :=
  closeUniv 2 (.andI (program_at _ _) (returned_length _ _))

end LeanProofs.IPRA.Analysis.RationalCoverPadding
