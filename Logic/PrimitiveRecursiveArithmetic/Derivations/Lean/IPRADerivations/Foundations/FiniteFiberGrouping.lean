import IPRADerivations.Foundations.FilteredEnumerationCode
import IPRADerivations.Core.Fubini
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.CommonLemmas

/-!
# Actual first-occurrence grouping of finite input positions

Source05's finite norm proof groups a supplied point list by its abscissae
and counts every original position in the resulting fibers. The fixed PR
reader below reads an actual list entry. Lists, persistent data, indices and
all counts are numerical object terms. No coverage or partition law is an
input. This generic key grouping asserts no curve or multiplicity theorem.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.FiniteFiberGrouping

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Foundations.BoundedReflection (wit ex_intro ex_elim ex_least eqb_cases eq_of_eqb one_ne_zero)
open LeanProofs.IPRA.Search (mu)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def key (f : PR 2) (L p i : PTm n) : PTm n := ap2 f (entry L i) p
def data (L p : PTm n) : PTm n := pairT L p
def matchData (L p v : PTm n) : PTm n := pairT L (pairT p v)
def matchBody (f : PR 2) : PTm 2 :=
  eqb (key f (fstT (var 1)) (fstT (sndT (var 1))) (var 0)) (sndT (sndT (var 1)))
def firstValue (f : PR 2) (L p v : PTm n) : PTm n := wit (matchBody f) (length L) (matchData L p v)
def first (f : PR 2) (L p i : PTm n) : PTm n := firstValue f L p (key f L p i)
def repBody (f : PR 2) : PTm 2 := eqb (first f (fstT (var 1)) (sndT (var 1)) (var 0)) (var 0)
def groupCount (f : PR 2) (L p : PTm n) : PTm n :=
  FilteredEnumerationCode.count (repBody f) (length L) (data L p)
def representatives (f : PR 2) (L p : PTm n) : PTm n :=
  FilteredEnumerationCode.list (repBody f) (length L) (data L p)
def representative (f : PR 2) (L p g : PTm n) : PTm n := entry (representatives f L p) g
def members (f : PR 2) (L p v : PTm n) : PTm n :=
  FilteredEnumerationCode.list (matchBody f) (length L) (matchData L p v)
def memberCount (f : PR 2) (L p v : PTm n) : PTm n :=
  FilteredEnumerationCode.count (matchBody f) (length L) (matchData L p v)
def fiber (f : PR 2) (L p g : PTm n) : PTm n := members f L p (key f L p (representative f L p g))
def fiberCount (f : PR 2) (L p g : PTm n) : PTm n := memberCount f L p (key f L p (representative f L p g))
def groupOf (f : PR 2) (L p i : PTm n) : PTm n :=
  FilteredEnumeration.rank (repBody f) (first f L p i) (data L p)

@[simp] theorem subst_key {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (L p i : PTm n) :
    Syn.subst σ (key f L p i) = key f (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ i) := by simp [key]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (L p : PTm n) :
    Syn.subst σ (data L p) = data (Syn.subst σ L) (Syn.subst σ p) := by simp [data]
@[simp] theorem subst_matchData {m : ℕ} (σ : Fin n → PTm m) (L p v : PTm n) :
    Syn.subst σ (matchData L p v) = matchData (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ v) := by simp [matchData]
@[simp] theorem subst_firstValue {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (L p v : PTm n) :
    Syn.subst σ (firstValue f L p v) = firstValue f (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ v) := by
  simp [firstValue,wit,mu]
@[simp] theorem subst_first {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (L p i : PTm n) :
    Syn.subst σ (first f L p i) = first f (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ i) := by simp [first]
@[simp] theorem subst_groupCount {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (L p : PTm n) :
    Syn.subst σ (groupCount f L p) = groupCount f (Syn.subst σ L) (Syn.subst σ p) := by simp [groupCount]
@[simp] theorem subst_representatives {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (L p : PTm n) :
    Syn.subst σ (representatives f L p) = representatives f (Syn.subst σ L) (Syn.subst σ p) := by simp [representatives]
@[simp] theorem subst_representative {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (L p g : PTm n) :
    Syn.subst σ (representative f L p g) = representative f (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ g) := by simp [representative]
@[simp] theorem subst_members {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (L p v : PTm n) :
    Syn.subst σ (members f L p v) = members f (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ v) := by simp [members]
@[simp] theorem subst_memberCount {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (L p v : PTm n) :
    Syn.subst σ (memberCount f L p v) = memberCount f (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ v) := by simp [memberCount]
@[simp] theorem subst_fiber {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (L p g : PTm n) :
    Syn.subst σ (fiber f L p g) = fiber f (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ g) := by simp [fiber]
@[simp] theorem subst_fiberCount {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (L p g : PTm n) :
    Syn.subst σ (fiberCount f L p g) = fiberCount f (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ g) := by simp [fiberCount]
@[simp] theorem subst_groupOf {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (L p i : PTm n) :
    Syn.subst σ (groupOf f L p i) = groupOf f (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ i) := by
  simp [groupOf,FilteredEnumeration.rank]

theorem key_congr (f : PR 2) {L L' p p' i i' : PTm n}
    (hL : Γ ⊢[PRAAx] L ≐ L') (hp : Γ ⊢[PRAAx] p ≐ p') (hi : Γ ⊢[PRAAx] i ≐ i') :
    Γ ⊢[PRAAx] key f L p i ≐ key f L' p' i' := congrAp2 f (entry_congr hL hi) hp
theorem firstValue_congr (f : PR 2) {L L' p p' v v' : PTm n}
    (hL : Γ ⊢[PRAAx] L ≐ L') (hp : Γ ⊢[PRAAx] p ≐ p') (hv : Γ ⊢[PRAAx] v ≐ v') :
    Γ ⊢[PRAAx] firstValue f L p v ≐ firstValue f L' p' v' := by
  ipra_congr (firstValue f (var 0) (var 1) (var 2) : PTm 3) with [hL, hp, hv]
theorem first_congr (f : PR 2) {L L' p p' i i' : PTm n}
    (hL : Γ ⊢[PRAAx] L ≐ L') (hp : Γ ⊢[PRAAx] p ≐ p') (hi : Γ ⊢[PRAAx] i ≐ i') :
    Γ ⊢[PRAAx] first f L p i ≐ first f L' p' i' := firstValue_congr f hL hp (key_congr f hL hp hi)
alias eqb_congr := Common.congrEqb
theorem match_at (f : PR 2) (L p v i : PTm n) : Γ ⊢[PRAAx]
    inst2 (matchBody f) i (matchData L p v) ≐ eqb (key f L p i) v := by
  simpa [matchBody,inst2,matchData] using eqb_congr
    (key_congr f (fst_pair L (pairT p v))
      ((congrFst (snd_pair L (pairT p v))).eqTrans (fst_pair p v)) (.eqRefl i))
    ((congrSnd (snd_pair L (pairT p v))).eqTrans (snd_pair p v))
theorem rep_at (f : PR 2) (L p i : PTm n) : Γ ⊢[PRAAx]
    inst2 (repBody f) i (data L p) ≐ eqb (first f L p i) i := by
  simpa [repBody,inst2,data] using eqb_congr (first_congr f (fst_pair L p) (snd_pair L p) (.eqRefl i)) (.eqRefl i)
theorem nonzero_of_one {a : PTm n} (h : Γ ⊢[PRAAx] a ≐ one) : Γ ⊢[PRAAx] neg (a ≐ zero) :=
  .impI (one_ne_zero _ (h.wk.eqSymm.eqTrans Prf.hyp0))
theorem equality_of_nonzero_eqb {a b : PTm n} (h : Γ ⊢[PRAAx] neg (eqb a b ≐ zero)) : Γ ⊢[PRAAx] a ≐ b :=
  .orE (eqb_cases a b) (.botE _ (.impE h.wk Prf.hyp0)) (eq_of_eqb Prf.hyp0)

theorem first_found (f : PR 2) (L p v i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length L))
    (hv : Γ ⊢[PRAAx] key f L p i ≐ v) : Γ ⊢[PRAAx]
    lt (firstValue f L p v) (length L) ⋏ (key f L p (firstValue f L p v) ≐ v) := by
  have accepted := nonzero_of_one ((match_at f L p v i).eqTrans (eqb_of_eq hv))
  have hit := ex_elim (matchBody f) (ex_intro (matchBody f) accepted hi)
  exact .andI (.andE₁ hit) (equality_of_nonzero_eqb
    (CodedViableChain.nonzero_of_eq (match_at f L p v (firstValue f L p v)).eqSymm (.andE₂ hit)))
theorem first_spec (f : PR 2) (L p i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length L)) : Γ ⊢[PRAAx]
    lt (first f L p i) (length L) ⋏ (key f L p (first f L p i) ≐ key f L p i) :=
  first_found f L p _ i hi (.eqRefl _)
theorem first_minimal (f : PR 2) (L p v i : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (firstValue f L p v)) : Γ ⊢[PRAAx] neg (key f L p i ≐ v) := by
  refine .impI ?_
  have z := ex_least (matchBody f) hi
  exact one_ne_zero _ (((match_at f L p v i).wk.eqTrans (eqb_of_eq Prf.hyp0)).eqSymm.eqTrans z.wk)
theorem first_le (f : PR 2) (L p i : PTm n) : Γ ⊢[PRAAx] le (first f L p i) i :=
  .orE (lt_or_le i (first f L p i))
    (.botE _ (.impE (first_minimal f L p (key f L p i) i Prf.hyp0) (.eqRefl _))) Prf.hyp0
theorem first_idempotent (f : PR 2) (L p i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length L)) : Γ ⊢[PRAAx]
    first f L p (first f L p i) ≐ first f L p i :=
  firstValue_congr f (.eqRefl _) (.eqRefl _) (.andE₂ (first_spec f L p i hi))

theorem representatives_length (f : PR 2) (L p : PTm n) : Γ ⊢[PRAAx]
    length (representatives f L p) ≐ groupCount f L p := FilteredEnumerationCode.list_length _ _ _
theorem group_count_bound (f : PR 2) (L p : PTm n) : Γ ⊢[PRAAx]
    le (groupCount f L p) (length L) := FilteredEnumerationCode.count_le _ _ _
theorem representative_bound (f : PR 2) (L p g : PTm n) (hg : Γ ⊢[PRAAx] lt g (groupCount f L p)) :
    Γ ⊢[PRAAx] lt (representative f L p g) (length L) := FilteredEnumerationCode.entry_bound _ _ _ _ hg
theorem representative_fixed (f : PR 2) (L p g : PTm n) (hg : Γ ⊢[PRAAx] lt g (groupCount f L p)) :
    Γ ⊢[PRAAx] first f L p (representative f L p g) ≐ representative f L p g :=
  equality_of_nonzero_eqb (CodedViableChain.nonzero_of_eq (rep_at f L p _).eqSymm
    (FilteredEnumerationCode.entry_valid (repBody f) (length L) (data L p) g hg))
theorem representatives_increasing (f : PR 2) (L p g h : PTm n)
    (hgh : Γ ⊢[PRAAx] lt g h) (hh : Γ ⊢[PRAAx] lt h (groupCount f L p)) : Γ ⊢[PRAAx]
    lt (representative f L p g) (representative f L p h) := FilteredEnumerationCode.increasing _ _ _ _ _ hgh hh
theorem first_retained (f : PR 2) (L p i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length L)) : Γ ⊢[PRAAx]
    neg (inst2 (repBody f) (first f L p i) (data L p) ≐ zero) :=
  nonzero_of_one ((rep_at f L p _).eqTrans (eqb_of_eq (first_idempotent f L p i hi)))
theorem groupOf_spec (f : PR 2) (L p i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length L)) : Γ ⊢[PRAAx]
    lt (groupOf f L p i) (groupCount f L p) ⋏
      (representative f L p (groupOf f L p i) ≐ first f L p i) :=
  FilteredEnumerationCode.listed (repBody f) (length L) (data L p) (first f L p i)
    (.andE₁ (first_spec f L p i hi)) (first_retained f L p i hi)
theorem groupOf_key (f : PR 2) (L p i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length L)) : Γ ⊢[PRAAx]
    key f L p (representative f L p (groupOf f L p i)) ≐ key f L p i :=
  (key_congr f (.eqRefl _) (.eqRefl _) (.andE₂ (groupOf_spec f L p i hi))).eqTrans
    (.andE₂ (first_spec f L p i hi))
theorem representative_rank (f : PR 2) (L p g : PTm n) (hg : Γ ⊢[PRAAx] lt g (groupCount f L p)) :
    Γ ⊢[PRAAx] FilteredEnumeration.rank (repBody f) (representative f L p g) (data L p) ≐ g :=
  (congrAp2 (sumF (BoundedReflection.sgB (repBody f)))
    (FilteredEnumerationCode.list_lookup (repBody f) (length L) (data L p) g hg) (.eqRefl _)).eqTrans
      (.andE₂ (.andE₂ (FilteredEnumeration.sel_spec (repBody f) hg)))
theorem representative_congr (f : PR 2) {L L' p p' g g' : PTm n}
    (hL : Γ ⊢[PRAAx] L ≐ L') (hp : Γ ⊢[PRAAx] p ≐ p') (hg : Γ ⊢[PRAAx] g ≐ g') :
    Γ ⊢[PRAAx] representative f L p g ≐ representative f L' p' g' := by
  ipra_congr (representative f (var 0) (var 1) (var 2) : PTm 3) with [hL, hp, hg]
theorem unique_group (f : PR 2) (L p g h : PTm n)
    (hg : Γ ⊢[PRAAx] lt g (groupCount f L p)) (hh : Γ ⊢[PRAAx] lt h (groupCount f L p))
    (hk : Γ ⊢[PRAAx] key f L p (representative f L p g) ≐ key f L p (representative f L p h)) :
    Γ ⊢[PRAAx] g ≐ h := by
  have er := (representative_fixed f L p g hg).eqSymm.eqTrans
    ((firstValue_congr f (.eqRefl _) (.eqRefl _) hk).eqTrans (representative_fixed f L p h hh))
  exact (representative_rank f L p g hg).eqSymm.eqTrans
    ((congrAp2 (sumF (BoundedReflection.sgB (repBody f))) er (.eqRefl _)).eqTrans (representative_rank f L p h hh))
theorem group_characterization (f : PR 2) (L p i g : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length L)) (hg : Γ ⊢[PRAAx] lt g (groupCount f L p)) : Γ ⊢[PRAAx]
    Fm.iff (key f L p i ≐ key f L p (representative f L p g)) (g ≐ groupOf f L p i) := by
  refine .andI (.impI ?_) (.impI ?_)
  · exact unique_group f L p g _ hg.wk ((Prf.andE₁ (groupOf_spec f L p i hi)).wk)
      (Prf.hyp0.eqSymm.eqTrans (groupOf_key f L p i hi).wk.eqSymm)
  · exact (groupOf_key f L p i hi).wk.eqSymm.eqTrans
      (key_congr f (.eqRefl _) (.eqRefl _) (representative_congr f (.eqRefl _) (.eqRefl _) Prf.hyp0.eqSymm))

theorem members_length (f : PR 2) (L p v : PTm n) : Γ ⊢[PRAAx]
    length (members f L p v) ≐ memberCount f L p v := FilteredEnumerationCode.list_length _ _ _
theorem fiber_length (f : PR 2) (L p g : PTm n) : Γ ⊢[PRAAx]
    length (fiber f L p g) ≐ fiberCount f L p g := members_length _ _ _ _
theorem member_bound (f : PR 2) (L p v r : PTm n)
    (hr : Γ ⊢[PRAAx] lt r (memberCount f L p v)) : Γ ⊢[PRAAx]
    lt (entry (members f L p v) r) (length L) := FilteredEnumerationCode.entry_bound _ _ _ _ hr
theorem member_key (f : PR 2) (L p v r : PTm n)
    (hr : Γ ⊢[PRAAx] lt r (memberCount f L p v)) : Γ ⊢[PRAAx]
    key f L p (entry (members f L p v) r) ≐ v :=
  equality_of_nonzero_eqb (CodedViableChain.nonzero_of_eq (match_at f L p v _).eqSymm
    (FilteredEnumerationCode.entry_valid _ _ _ _ hr))
theorem members_increasing (f : PR 2) (L p v r s : PTm n)
    (hrs : Γ ⊢[PRAAx] lt r s) (hs : Γ ⊢[PRAAx] lt s (memberCount f L p v)) : Γ ⊢[PRAAx]
    lt (entry (members f L p v) r) (entry (members f L p v) s) :=
  FilteredEnumerationCode.increasing _ _ _ _ _ hrs hs
theorem members_complete (f : PR 2) (L p v i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length L))
    (hk : Γ ⊢[PRAAx] key f L p i ≐ v) : Γ ⊢[PRAAx]
    lt (FilteredEnumeration.rank (matchBody f) i (matchData L p v)) (memberCount f L p v) ⋏
      (entry (members f L p v) (FilteredEnumeration.rank (matchBody f) i (matchData L p v)) ≐ i) :=
  FilteredEnumerationCode.listed _ _ _ _ hi (nonzero_of_one ((match_at f L p v i).eqTrans (eqb_of_eq hk)))
theorem fiber_bound (f : PR 2) (L p g r : PTm n) (hr : Γ ⊢[PRAAx] lt r (fiberCount f L p g)) :
    Γ ⊢[PRAAx] lt (entry (fiber f L p g) r) (length L) := member_bound _ _ _ _ _ hr
theorem fiber_key (f : PR 2) (L p g r : PTm n) (hr : Γ ⊢[PRAAx] lt r (fiberCount f L p g)) :
    Γ ⊢[PRAAx] key f L p (entry (fiber f L p g) r) ≐ key f L p (representative f L p g) := member_key _ _ _ _ _ hr
theorem fiber_nonempty (f : PR 2) (L p g : PTm n) (hg : Γ ⊢[PRAAx] lt g (groupCount f L p)) :
    Γ ⊢[PRAAx] le one (fiberCount f L p g) :=
  le_trans (zero_lt_succ _) (.andE₁ (members_complete f L p _ _ (representative_bound f L p g hg) (.eqRefl _)))
theorem fiber_disjoint (f : PR 2) (L p g h r s : PTm n)
    (hg : Γ ⊢[PRAAx] lt g (groupCount f L p)) (hh : Γ ⊢[PRAAx] lt h (groupCount f L p))
    (hr : Γ ⊢[PRAAx] lt r (fiberCount f L p g)) (hs : Γ ⊢[PRAAx] lt s (fiberCount f L p h))
    (he : Γ ⊢[PRAAx] entry (fiber f L p g) r ≐ entry (fiber f L p h) s) : Γ ⊢[PRAAx] g ≐ h :=
  unique_group f L p g h hg hh ((fiber_key f L p g r hr).eqSymm.eqTrans
    ((key_congr f (.eqRefl _) (.eqRefl _) he).eqTrans (fiber_key f L p h s hs)))

def slotOf (f : PR 2) (L p i : PTm n) : PTm n :=
  FilteredEnumeration.rank (matchBody f) i (matchData L p (key f L p (representative f L p (groupOf f L p i))))
@[simp] theorem subst_slotOf {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (L p i : PTm n) :
    Syn.subst σ (slotOf f L p i) = slotOf f (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ i) := by
  simp [slotOf,FilteredEnumeration.rank]
theorem coverage (f : PR 2) (L p i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length L)) : Γ ⊢[PRAAx]
    lt (groupOf f L p i) (groupCount f L p) ⋏
      (lt (slotOf f L p i) (fiberCount f L p (groupOf f L p i)) ⋏
        (entry (fiber f L p (groupOf f L p i)) (slotOf f L p i) ≐ i)) :=
  .andI (.andE₁ (groupOf_spec f L p i hi))
    (members_complete f L p _ i hi (groupOf_key f L p i hi).eqSymm)

/-! ## The computed cardinal partition, through genuine finite Fubini -/

def incidence (f : PR 2) (L p g i : PTm n) : PTm n :=
  Signum.sg (eqb (key f L p i) (key f L p (representative f L p g)))
def incidenceBody (f : PR 2) : PTm 3 := incidence f (fstT (var 2)) (sndT (var 2)) (var 0) (var 1)
def sizeBody (f : PR 2) : PTm 2 := fiberCount f (fstT (var 1)) (sndT (var 1)) (var 0)
def partitionTotal (f : PR 2) (L p : PTm n) : PTm n := ap2 (sumF (sizeBody f)) (groupCount f L p) (data L p)
@[simp] theorem subst_incidence {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (L p g i : PTm n) :
    Syn.subst σ (incidence f L p g i) = incidence f (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ g) (Syn.subst σ i) := by
  simp [incidence,Signum.sg]
@[simp] theorem subst_partitionTotal {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (L p : PTm n) :
    Syn.subst σ (partitionTotal f L p) = partitionTotal f (Syn.subst σ L) (Syn.subst σ p) := by simp [partitionTotal]

theorem incidence_congr (f : PR 2) {L L' p p' g g' i i' : PTm n}
    (hL : Γ ⊢[PRAAx] L ≐ L') (hp : Γ ⊢[PRAAx] p ≐ p')
    (hg : Γ ⊢[PRAAx] g ≐ g') (hi : Γ ⊢[PRAAx] i ≐ i') : Γ ⊢[PRAAx]
    incidence f L p g i ≐ incidence f L' p' g' i' := by
  ipra_congr (incidence f (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hL, hp, hg, hi]
theorem incidence_at (f : PR 2) (L p g i : PTm n) : Γ ⊢[PRAAx]
    inst3 (incidenceBody f) g i (data L p) ≐ incidence f L p g i := by
  simpa [incidenceBody,inst3,data] using incidence_congr f (fst_pair L p) (snd_pair L p) (.eqRefl g) (.eqRefl i)
theorem row_at (f : PR 2) (L p g i : PTm n) : Γ ⊢[PRAAx]
    inst2 (rowB (incidenceBody f)) i (pairT g (data L p)) ≐ incidence f L p g i := by
  rw [inst2_rowB]
  exact (congrInst3 (incidenceBody f) (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans (incidence_at f L p g i)
theorem column_at (f : PR 2) (L p g i : PTm n) : Γ ⊢[PRAAx]
    inst2 (colB (incidenceBody f)) g (pairT i (data L p)) ≐ incidence f L p g i := by
  rw [inst2_colB]
  exact (congrInst3 (incidenceBody f) (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqTrans (incidence_at f L p g i)
theorem row_count (f : PR 2) (L p g : PTm n) : Γ ⊢[PRAAx]
    fiberCount f L p g ≐ ap2 (sumF (rowB (incidenceBody f))) (length L) (pairT g (data L p)) := by
  apply sum_congr_bounded
  refine .allI (.impI ?_)
  rw [BoundedReflection.inst2_sgB]
  have e := congrMonus (Γ := lt (var 0) (Syn.shift (length L)) :: Γ.map Fm.shift) (.eqRefl one) (congrMonus (.eqRefl one)
    (match_at f (Syn.shift L) (Syn.shift p)
      (key f (Syn.shift L) (Syn.shift p) (representative f (Syn.shift L) (Syn.shift p) (Syn.shift g))) (var 0)))
  simpa only [Syn.shift,subst_matchData,subst_key,subst_representative,subst_data,subst_pairT] using
    e.eqTrans (row_at f (Syn.shift L) (Syn.shift p) (Syn.shift g) (var 0)).eqSymm
theorem sg_eqb (a b : PTm n) : Γ ⊢[PRAAx] Signum.sg (eqb a b) ≐ eqb a b := by
  refine .orE (eqb_cases a b) ?_ ?_
  · exact ((congrMonus (.eqRefl one) (congrMonus (.eqRefl one) Prf.hyp0)).eqTrans
      ((congrMonus (.eqRefl one) (monus_zero one)).eqTrans (monus_self one))).eqTrans Prf.hyp0.eqSymm
  · exact ((congrMonus (.eqRefl one) (congrMonus (.eqRefl one) Prf.hyp0)).eqTrans
      ((congrMonus (.eqRefl one) (monus_self one)).eqTrans (monus_zero one))).eqTrans Prf.hyp0.eqSymm
theorem incidence_delta (f : PR 2) (L p g i : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length L)) (hg : Γ ⊢[PRAAx] lt g (groupCount f L p)) : Γ ⊢[PRAAx]
    incidence f L p g i ≐ eqb g (groupOf f L p i) := by
  apply (sg_eqb _ _).eqTrans
  refine .orE (eq_or_ne g (groupOf f L p i)) ?_ ?_
  · exact (eqb_of_eq ((group_characterization f L p i g hi hg).wk.iffMpr Prf.hyp0)).eqTrans
      (eqb_of_eq Prf.hyp0).eqSymm
  · have nk : neg (g ≐ groupOf f L p i) :: Γ ⊢[PRAAx]
        neg (key f L p i ≐ key f L p (representative f L p g)) := by
      refine .impI (.impE Prf.hyp1 ?_)
      exact (group_characterization f L p i g hi hg).wk.wk.iffMp Prf.hyp0
    exact (eqb_of_ne nk).eqTrans (eqb_of_ne Prf.hyp0).eqSymm
theorem column_unit (f : PR 2) (L p i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length L)) : Γ ⊢[PRAAx]
    ap2 (sumF (colB (incidenceBody f))) (groupCount f L p) (pairT i (data L p)) ≐ one := by
  have total : Γ ⊢[PRAAx] ap2 (sumF (colB (incidenceBody f))) (groupCount f L p) (pairT i (data L p)) ≐
      dS (one : PTm 2) (groupCount f L p) (groupOf f L p i) zero := by
    apply sum_congr_bounded
    refine .allI (.impI ?_)
    rw [inst2_dB]
    have range : lt (var 0) (Syn.shift (groupCount f L p)) :: Γ.map Fm.shift ⊢[PRAAx]
        lt (Syn.shift i) (length (Syn.shift L)) := by simpa only [Fm.shift,subst_lt,SequenceComposition.subst_length,Syn.shift] using hi.shift.wk
    have target : lt (var 0) (Syn.shift (groupCount f L p)) :: Γ.map Fm.shift ⊢[PRAAx]
        incidence f (Syn.shift L) (Syn.shift p) (var 0) (Syn.shift i) ≐ eqb (var 0) (groupOf f (Syn.shift L) (Syn.shift p) (Syn.shift i)) :=
      incidence_delta f _ _ _ _ range (by simpa only [subst_groupCount,Syn.shift] using (Prf.hyp0 : lt (var 0) (Syn.shift (groupCount f L p)) :: Γ.map Fm.shift ⊢[PRAAx] _))
    have symm : ∀ (a b : PTm (n+1)), (lt (var 0) (Syn.shift (groupCount f L p)) :: Γ.map Fm.shift) ⊢[PRAAx]
        eqb a b ≐ eqb b a := fun a b => congrMonus (.eqRefl _) (add_comm _ _)
    have right := (congrMul (Γ := lt (var 0) (Syn.shift (groupCount f L p)) :: Γ.map Fm.shift)
      (eqb_congr (fst_pair (groupOf f (Syn.shift L) (Syn.shift p) (Syn.shift i)) zero) (.eqRefl (var 0)))
      (.eqRefl one)).eqTrans ((mul_comm _ one).eqTrans (one_mul _))
    simpa only [Syn.shift,subst_pairT,subst_data,subst_groupOf,inst2,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      (column_at f (Syn.shift L) (Syn.shift p) (var 0) (Syn.shift i)).eqTrans
        (target.eqTrans ((symm _ _).eqTrans right.eqSymm))
  have delta := sum_delta (one : PTm 2) (x := zero) (.andE₁ (groupOf_spec f L p i hi))
  exact total.eqTrans (by simpa only [dS,inst2,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using delta)

theorem fiberCount_congr (f : PR 2) {L L' p p' g g' : PTm n}
    (hL : Γ ⊢[PRAAx] L ≐ L') (hp : Γ ⊢[PRAAx] p ≐ p') (hg : Γ ⊢[PRAAx] g ≐ g') :
    Γ ⊢[PRAAx] fiberCount f L p g ≐ fiberCount f L' p' g' := by
  ipra_congr (fiberCount f (var 0) (var 1) (var 2) : PTm 3) with [hL, hp, hg]
theorem size_at (f : PR 2) (L p g : PTm n) : Γ ⊢[PRAAx]
    inst2 (sizeBody f) g (data L p) ≐ fiberCount f L p g := by
  simpa [sizeBody,inst2,data] using fiberCount_congr f (fst_pair L p) (snd_pair L p) (.eqRefl g)
theorem sum_units (N x : PTm n) : Γ ⊢[PRAAx] ap2 (sumF (one : PTm 2)) N x ≐ N := by
  have all : Γ ⊢[PRAAx] .all (ap2 (sumF (one : PTm 2)) (var 0) (Syn.shift x) ≐ var 0) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,subst_ap2,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact sum_zero _ _
    · simp only [Fm.subst_eq,subst_ap2,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      have s := sum_succ' (Γ := (ap2 (sumF (one : PTm 2)) (var 0) (Syn.shift x) ≐ var 0) :: Γ.map Fm.shift)
        (one : PTm 2) (var 0) (Syn.shift x)
      have e := (congrAdd (Prf.hyp0 : (ap2 (sumF (one : PTm 2)) (var 0) (Syn.shift x) ≐ var 0) :: Γ.map Fm.shift ⊢[PRAAx] _)
        (.eqRefl one)).eqTrans (succ_eq_add_one (var 0)).eqSymm
      exact s.eqTrans (by simpa [inst2] using e)
  simpa only [Fm.subst_eq,subst_ap2,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

/-- This is equality for the computed sum, not an output field set equal to
the original length. Both Fubini bounds are numerical runtime terms. -/
theorem cardinal_partition (f : PR 2) (L p : PTm n) : Γ ⊢[PRAAx]
    partitionTotal f L p ≐ length L := by
  have rows : Γ ⊢[PRAAx] partitionTotal f L p ≐
      ap2 (sumF (oB (incidenceBody f))) (groupCount f L p) (pairT (length L) (data L p)) := by
    apply sum_congr_bounded
    refine .allI (.impI ?_)
    have e := (size_at (Γ := lt (var 0) (Syn.shift (groupCount f L p)) :: Γ.map Fm.shift)
      f (Syn.shift L) (Syn.shift p) (var 0)).eqTrans
      ((row_count f (Syn.shift L) (Syn.shift p) (var 0)).eqTrans
        (oB_at (incidenceBody f) (var 0) (length (Syn.shift L)) (data (Syn.shift L) (Syn.shift p))).eqSymm)
    simpa only [Syn.shift,subst_pairT,SequenceComposition.subst_length,subst_data] using e
  have columns : Γ ⊢[PRAAx]
      ap2 (sumF (pB (incidenceBody f))) (length L) (pairT (groupCount f L p) (data L p)) ≐
        ap2 (sumF (one : PTm 2)) (length L) zero := by
    apply sum_congr_bounded
    refine .allI (.impI ?_)
    rw [inst2_pB]
    have point : lt (var 0) (Syn.shift (length L)) :: Γ.map Fm.shift ⊢[PRAAx]
        ap2 (sumF (colB (incidenceBody f))) (groupCount f (Syn.shift L) (Syn.shift p))
          (pairT (var 0) (data (Syn.shift L) (Syn.shift p))) ≐ one :=
      column_unit f _ _ _ (by simpa only [Syn.shift,SequenceComposition.subst_length] using
        (Prf.hyp0 : lt (var 0) (Syn.shift (length L)) :: Γ.map Fm.shift ⊢[PRAAx] _))
    have decode := congrAp2 (Γ := lt (var 0) (Syn.shift (length L)) :: Γ.map Fm.shift)
      (sumF (colB (incidenceBody f))) (fst_pair (groupCount f (Syn.shift L) (Syn.shift p))
        (data (Syn.shift L) (Syn.shift p)))
      (congrPairT (.eqRefl (var 0)) (snd_pair (groupCount f (Syn.shift L) (Syn.shift p)) (data (Syn.shift L) (Syn.shift p))))
    simpa only [Syn.shift,subst_pairT,subst_groupCount,subst_data,inst2,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using decode.eqTrans point
  exact rows.eqTrans ((fubini (incidenceBody f) (groupCount f L p) (length L) (data L p)).eqTrans
    (columns.eqTrans (sum_units (length L) zero)))

theorem same_key_group (f : PR 2) (L p i j : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length L)) (hj : Γ ⊢[PRAAx] lt j (length L)) : Γ ⊢[PRAAx]
    Fm.iff (key f L p i ≐ key f L p j) (groupOf f L p i ≐ groupOf f L p j) := by
  refine .andI (.impI ?_) (.impI ?_)
  · exact unique_group f L p _ _ ((Prf.andE₁ (groupOf_spec f L p i hi)).wk)
      ((Prf.andE₁ (groupOf_spec f L p j hj)).wk)
      ((groupOf_key f L p i hi).wk.eqTrans (Prf.hyp0.eqTrans (groupOf_key f L p j hj).wk.eqSymm))
  · exact (groupOf_key f L p i hi).wk.eqSymm.eqTrans
      ((key_congr f (.eqRefl _) (.eqRefl _) (representative_congr f (.eqRefl _) (.eqRefl _) Prf.hyp0)).eqTrans
        (groupOf_key f L p j hj).wk)

/-! ## Actual stored fibers and literal returned fields -/

def fiberBody (f : PR 2) : PTm 2 := fiber f (fstT (var 1)) (sndT (var 1)) (var 0)
def fiberLists (f : PR 2) (L p : PTm n) : PTm n := sequence (fiberBody f) (groupCount f L p) (data L p)
def sizes (f : PR 2) (L p : PTm n) : PTm n := sequence (sizeBody f) (groupCount f L p) (data L p)
def output (f : PR 2) (L p : PTm n) : PTm n :=
  pairT (representatives f L p) (pairT (fiberLists f L p) (pairT (sizes f L p) (partitionTotal f L p)))
def outputF (f : PR 2) : PR 2 := PTm.toPR (output f (var 0) (var 1))
def run (f : PR 2) (L p : PTm n) : PTm n := ap2 (outputF f) L p
@[simp] theorem subst_fiberLists {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (L p : PTm n) :
    Syn.subst σ (fiberLists f L p) = fiberLists f (Syn.subst σ L) (Syn.subst σ p) := by simp [fiberLists]
@[simp] theorem subst_sizes {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (L p : PTm n) :
    Syn.subst σ (sizes f L p) = sizes f (Syn.subst σ L) (Syn.subst σ p) := by simp [sizes]
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (L p : PTm n) :
    Syn.subst σ (output f L p) = output f (Syn.subst σ L) (Syn.subst σ p) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (L p : PTm n) :
    Syn.subst σ (run f L p) = run f (Syn.subst σ L) (Syn.subst σ p) := by simp [run]
theorem fiber_congr (f : PR 2) {L L' p p' g g' : PTm n}
    (hL : Γ ⊢[PRAAx] L ≐ L') (hp : Γ ⊢[PRAAx] p ≐ p') (hg : Γ ⊢[PRAAx] g ≐ g') :
    Γ ⊢[PRAAx] fiber f L p g ≐ fiber f L' p' g' := by
  ipra_congr (fiber f (var 0) (var 1) (var 2) : PTm 3) with [hL, hp, hg]
theorem fiber_body_at (f : PR 2) (L p g : PTm n) : Γ ⊢[PRAAx]
    inst2 (fiberBody f) g (data L p) ≐ fiber f L p g := by
  simpa [fiberBody,inst2,data] using fiber_congr f (fst_pair L p) (snd_pair L p) (.eqRefl g)
theorem fiberLists_length (f : PR 2) (L p : PTm n) : Γ ⊢[PRAAx]
    length (fiberLists f L p) ≐ groupCount f L p := MasterCertificate.sequence_length _ _ _
theorem sizes_length (f : PR 2) (L p : PTm n) : Γ ⊢[PRAAx]
    length (sizes f L p) ≐ groupCount f L p := MasterCertificate.sequence_length _ _ _
theorem fiberLists_lookup (f : PR 2) (L p g : PTm n) (hg : Γ ⊢[PRAAx] lt g (groupCount f L p)) :
    Γ ⊢[PRAAx] entry (fiberLists f L p) g ≐ fiber f L p g :=
  (MasterCertificate.sequence_decode (fiberBody f) hg).eqTrans (fiber_body_at f L p g)
theorem sizes_lookup (f : PR 2) (L p g : PTm n) (hg : Γ ⊢[PRAAx] lt g (groupCount f L p)) :
    Γ ⊢[PRAAx] entry (sizes f L p) g ≐ fiberCount f L p g :=
  (MasterCertificate.sequence_decode (sizeBody f) hg).eqTrans (size_at f L p g)
theorem representatives_code_bound (f : PR 2) (L p : PTm n) : Γ ⊢[PRAAx]
    lt (representatives f L p) (FilteredEnumerationCode.codeBound (repBody f) (length L) (data L p)) :=
  FilteredEnumerationCode.size_bound _ _ _
theorem fiber_code_bound (f : PR 2) (L p g : PTm n) : Γ ⊢[PRAAx]
    lt (fiber f L p g) (FilteredEnumerationCode.codeBound (matchBody f) (length L)
      (matchData L p (key f L p (representative f L p g)))) := FilteredEnumerationCode.size_bound _ _ _
theorem empty_groups (f : PR 2) (L p : PTm n) (h : Γ ⊢[PRAAx] length L ≐ zero) :
    Γ ⊢[PRAAx] groupCount f L p ≐ zero :=
  le_antisymm (le_congr (.eqRefl _) h (group_count_bound f L p)) (zero_le _)
theorem empty_partition (f : PR 2) (L p : PTm n) (h : Γ ⊢[PRAAx] length L ≐ zero) :
    Γ ⊢[PRAAx] partitionTotal f L p ≐ zero := (cardinal_partition f L p).eqTrans h
theorem program_at (f : PR 2) (L p : PTm n) : Γ ⊢[PRAAx] run f L p ≐ output f L p := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output f (var 0) (var 1)) ![L,p]
theorem returned_representatives (f : PR 2) (L p : PTm n) : Γ ⊢[PRAAx]
    fstT (run f L p) ≐ representatives f L p := (congrFst (program_at f L p)).eqTrans (fst_pair _ _)
theorem returned_fibers (f : PR 2) (L p : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run f L p)) ≐ fiberLists f L p :=
  (congrFst ((congrSnd (program_at f L p)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_sizes (f : PR 2) (L p : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run f L p))) ≐ sizes f L p :=
  (congrFst ((congrSnd ((congrSnd (program_at f L p)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_total (f : PR 2) (L p : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run f L p))) ≐ partitionTotal f L p :=
  (congrSnd ((congrSnd ((congrSnd (program_at f L p)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_cardinal_partition (f : PR 2) (L p : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run f L p))) ≐ length L := (returned_total f L p).eqTrans (cardinal_partition f L p)
theorem returned_fiber_lookup (f : PR 2) (L p g : PTm n) (hg : Γ ⊢[PRAAx] lt g (groupCount f L p)) :
    Γ ⊢[PRAAx] entry (fstT (sndT (run f L p))) g ≐ fiber f L p g :=
  (entry_congr (returned_fibers f L p) (.eqRefl _)).eqTrans (fiberLists_lookup f L p g hg)
theorem returned_size_lookup (f : PR 2) (L p g : PTm n) (hg : Γ ⊢[PRAAx] lt g (groupCount f L p)) :
    Γ ⊢[PRAAx] entry (fstT (sndT (sndT (run f L p)))) g ≐ length (fiber f L p g) :=
  (entry_congr (returned_sizes f L p) (.eqRefl _)).eqTrans ((sizes_lookup f L p g hg).eqTrans (fiber_length f L p g).eqSymm)

theorem grouping_lengths_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((length (representatives f (var 0) (var 1)) ≐ groupCount f (var 0) (var 1)) ⋏
      ((length (fiberLists f (var 0) (var 1)) ≐ groupCount f (var 0) (var 1)) ⋏
        (length (sizes f (var 0) (var 1)) ≐ groupCount f (var 0) (var 1)))) :=
  closeUniv 2 (.andI (representatives_length f _ _) (.andI (fiberLists_length f _ _) (sizes_length f _ _)))
theorem grouping_coverage_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (length (var 0)) ⟶
      (lt (groupOf f (var 0) (var 1) (var 2)) (groupCount f (var 0) (var 1)) ⋏
        (lt (slotOf f (var 0) (var 1) (var 2)) (fiberCount f (var 0) (var 1) (groupOf f (var 0) (var 1) (var 2))) ⋏
          (entry (fiber f (var 0) (var 1) (groupOf f (var 0) (var 1) (var 2))) (slotOf f (var 0) (var 1) (var 2)) ≐ var 2)))) :=
  closeUniv 3 (.impI (coverage f _ _ _ Prf.hyp0))
theorem grouping_disjoint_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 2) (groupCount f (var 0) (var 1)) ⟶ lt (var 3) (groupCount f (var 0) (var 1)) ⟶
      lt (var 4) (fiberCount f (var 0) (var 1) (var 2)) ⟶ lt (var 5) (fiberCount f (var 0) (var 1) (var 3)) ⟶
        entry (fiber f (var 0) (var 1) (var 2)) (var 4) ≐ entry (fiber f (var 0) (var 1) (var 3)) (var 5) ⟶ var 2 ≐ var 3) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI
    (fiber_disjoint f _ _ _ _ _ _ (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0))))))
theorem grouping_partition_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (partitionTotal f (var 0) (var 1) ≐ length (var 0)) := closeUniv 2 (cardinal_partition f _ _)
theorem grouping_same_key_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (length (var 0)) ⟶ lt (var 3) (length (var 0)) ⟶
      Fm.iff (key f (var 0) (var 1) (var 2) ≐ key f (var 0) (var 1) (var 3))
        (groupOf f (var 0) (var 1) (var 2) ≐ groupOf f (var 0) (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (same_key_group f _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem grouping_program_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((run f (var 0) (var 1) ≐ output f (var 0) (var 1)) ⋏
      (sndT (sndT (sndT (run f (var 0) (var 1)))) ≐ length (var 0))) :=
  closeUniv 2 (.andI (program_at f _ _) (returned_cardinal_partition f _ _))
theorem grouping_returned_fiber_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (groupCount f (var 0) (var 1)) ⟶
      ((entry (fstT (sndT (run f (var 0) (var 1)))) (var 2) ≐ fiber f (var 0) (var 1) (var 2)) ⋏
        (entry (fstT (sndT (sndT (run f (var 0) (var 1))))) (var 2) ≐ length (fiber f (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.impI (.andI (returned_fiber_lookup f _ _ _ Prf.hyp0) (returned_size_lookup f _ _ _ Prf.hyp0)))
theorem grouping_empty_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (length (var 0) ≐ zero ⟶ ((groupCount f (var 0) (var 1) ≐ zero) ⋏ (partitionTotal f (var 0) (var 1) ≐ zero))) :=
  closeUniv 2 (.impI (.andI (empty_groups f _ _ Prf.hyp0) (empty_partition f _ _ Prf.hyp0)))

end LeanProofs.IPRA.Foundations.FiniteFiberGrouping
