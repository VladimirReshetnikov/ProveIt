import IPRADerivations.Analysis.RationalArithmetic.RationalPhiSection
import IPRADerivations.Analysis.RationalArithmetic.Covers.RationalPhiCoverAssignment
import IPRADerivations.Analysis.RationalArithmetic.Covers.RationalCoverPadding

/-!
# The original finite superelliptic cover bound

The cover bit tests the actual feature tuple of the original distinct
points. Its least successful family produces a genuine first-cover
partition. The full source section theorem bounds each group, and the
exact cardinal partition then bounds the original list by m*M.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPhiCoverBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalPhiFeatures (dimension)
open RationalPhiSectionNonzero (curveInput)
open RationalPhiCoverAssignment (cover group bounds sourceCoverBit selectedFamily featureList)
open RationalCurvePointsGaussianEmbedding (distinct)
open RationalSuperellipticNormDegree (pointPowers)
open RationalFiniteSpanCover (family)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

@[simp] theorem subst_curveInput {k : ℕ} (σ : Fin n → PTm k) (f s r m : PTm n) :
    (curveInput f s r m).subst σ = curveInput (Syn.subst σ f) (Syn.subst σ s) (Syn.subst σ r) (Syn.subst σ m) := by
  simp [curveInput,one]

theorem group_bound (f s r m P D g : PTm n) (h : Γ ⊢[PRAAx] curveInput f s r m)
    (hd : Γ ⊢[PRAAx] distinct P) (hp : Γ ⊢[PRAAx] pointPowers f r P)
    (hf : Γ ⊢[PRAAx] family D (dimension s)) (hc : Γ ⊢[PRAAx] cover s P D)
    (hg : Γ ⊢[PRAAx] lt g (length D)) :
    Γ ⊢[PRAAx] le (length (group s P D g)) m :=
  RationalPhiSection.proper_span_bound
    (entry D g) (length (entry D g)) f s r m (group s P D g) h
    (RationalFiniteSpanCover.family_at D (dimension s) g hf hg)
    (RationalPhiCoverAssignment.group_distinct s P D g hd)
    (RationalPhiCoverAssignment.group_powers f r s P D g hp)
    (RationalPhiCoverAssignment.group_members s P D g hc)

theorem group_bounds (f s r m P D : PTm n) (h : Γ ⊢[PRAAx] curveInput f s r m)
    (hd : Γ ⊢[PRAAx] distinct P) (hp : Γ ⊢[PRAAx] pointPowers f r P)
    (hf : Γ ⊢[PRAAx] family D (dimension s)) (hc : Γ ⊢[PRAAx] cover s P D) :
    Γ ⊢[PRAAx] bounds s P D m := by
  refine RationalPhiCoverAssignment.bounds_intro s P D m (.allI (.impI ?_))
  let f' := Syn.shift f
  let s' := Syn.shift s
  let r' := Syn.shift r
  let m' := Syn.shift m
  let P' := Syn.shift P
  let D' := Syn.shift D
  let Δ := Γ.map Fm.shift
  have input' : Δ ⊢[PRAAx] curveInput f' s' r' m' := by
    simpa [Δ,f',s',r',m',Syn.shift,Fm.shift] using h.shift
  have dist' : Δ ⊢[PRAAx] distinct P' := by simpa [Δ,P',Syn.shift,Fm.shift] using hd.shift
  have powers' : Δ ⊢[PRAAx] pointPowers f' r' P' := by simpa [Δ,f',r',P',Syn.shift,Fm.shift] using hp.shift
  have family' : Δ ⊢[PRAAx] family D' (dimension s') := by simpa [Δ,D',s',Syn.shift,Fm.shift] using hf.shift
  have cover' : Δ ⊢[PRAAx] cover s' P' D' := by simpa [Δ,s',P',D',Syn.shift,Fm.shift] using hc.shift
  simpa [Δ,f',s',r',m',P',D',Syn.shift] using
    group_bound f' s' r' m' P' D' (var 0) input'.wk dist'.wk powers'.wk family'.wk cover'.wk Prf.hyp0

theorem supplied_cover_bound (f s r m P D M : PTm n) (h : Γ ⊢[PRAAx] curveInput f s r m)
    (hd : Γ ⊢[PRAAx] distinct P) (hp : Γ ⊢[PRAAx] pointPowers f r P)
    (hf : Γ ⊢[PRAAx] family D (dimension s)) (hc : Γ ⊢[PRAAx] cover s P D)
    (hm : Γ ⊢[PRAAx] le (length D) M) : Γ ⊢[PRAAx] le (length P) (m*M) :=
  le_trans (RationalPhiCoverAssignment.count_from_groups s P D m hc (group_bounds f s r m P D h hd hp hf hc))
    (le_congr (.eqRefl _) (mul_comm _ _) (mul_le_mul_right m hm))

theorem cover_bit_bound (f s r m P M : PTm n) (h : Γ ⊢[PRAAx] curveInput f s r m)
    (hd : Γ ⊢[PRAAx] distinct P) (hp : Γ ⊢[PRAAx] pointPowers f r P)
    (hc : Γ ⊢[PRAAx] sourceCoverBit s P M ≐ one) : Γ ⊢[PRAAx] le (length P) (m*M) := by
  have c := RationalPhiCoverAssignment.selected_certificate s P M hc
  exact RationalPhiCoverAssignment.selected_count_from_groups s P M m hc
    (group_bounds f s r m P (selectedFamily s P M) h hd hp (.andE₁ c) (.andE₂ c))

theorem source_cover_iff (s P M : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (sourceCoverBit s P M ≐ one) (RationalCoverPadding.supplied (featureList s P) M (dimension s)) :=
  RationalCoverPadding.cover_bit_supplied_iff _ _ _ (le_trans (zero_lt_succ s) (le_succ_self (succ s)))

theorem actual_original_superelliptic_supplied_cover_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (curveInput (var 0) (var 1) (var 2) (var 3) ⟶ distinct (var 4) ⟶ pointPowers (var 0) (var 2) (var 4) ⟶
      family (var 5) (dimension (var 1)) ⟶ cover (var 1) (var 4) (var 5) ⟶ le (length (var 5)) (var 6) ⟶
      le (length (var 4)) (var 3*var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (.impI (supplied_cover_bound (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0)))))))

theorem actual_original_superelliptic_cover_bit_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (curveInput (var 0) (var 1) (var 2) (var 3) ⟶ distinct (var 4) ⟶ pointPowers (var 0) (var 2) (var 4) ⟶
      sourceCoverBit (var 1) (var 4) (var 5) ≐ one ⟶ le (length (var 4)) (var 3*var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (cover_bit_bound (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)
    (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0)))))

theorem actual_original_superelliptic_cover_iff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (Fm.iff (sourceCoverBit (var 0) (var 1) (var 2) ≐ one)
      (RationalCoverPadding.supplied (featureList (var 0) (var 1)) (var 2) (dimension (var 0)))) :=
  closeUniv 3 (source_cover_iff _ _ _)

end LeanProofs.IPRA.Analysis.RationalPhiCoverBound
