import IPRADerivations.Foundations.RealizerLeastSearch
import IPRADerivations.Foundations.FiniteQueryDemand

/-!
# Actual finite Herbrand capsules

FIBER section 3.5: a capsule retains a finite candidate list and the finite
disjunction that some decoded member is valid. Generic logical mapping and
invariant elimination work for arbitrary fixed formulas. A fixed bounded
formula additionally has a real compiled checker and least-member program.
No decision procedure for arbitrary formulas, supplied list-coverage law or
global capsule-correctness contract is assumed. Least means first in list
order, as in the source reference program, not minimum numerical value.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.HerbrandCapsule

open_ipra exports
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Foundations.RealizerComposition (sequence_mono)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def memberAt (A : Fm PTm 2) (q w : PTm n) : Fm PTm n := A.subst ![q,w]
def publicAt (B : Fm PTm 1) (q : PTm n) : Fm PTm n := B.subst ![q]
def contains (A : Fm PTm 2) (W q : PTm n) : Fm PTm n :=
  .ex (lt (var 0) (length (Syn.shift W)) ⋏ memberAt A (Syn.shift q) (entry (Syn.shift W) (var 0)))
def candidates (f : PTm 2) (N x : PTm n) : PTm n := sequence f N x
def listF (f : PTm 2) : PR 2 := PTm.toPR (candidates f (var 0) (var 1))
def runList (f : PTm 2) (N x : PTm n) : PTm n := ap2 (listF f) N x
def valueCap (f : PTm 2) (N x : PTm n) : PTm n := succ (finiteMaximum f N x)
def codeBound (f : PTm 2) (N x : PTm n) : PTm n :=
  succ (sequence (var 1) N (valueCap f N x))

@[simp] theorem subst_memberAt {m : ℕ} (σ : Fin n → PTm m) (A : Fm PTm 2) (q w : PTm n) :
    (memberAt A q w).subst σ = memberAt A (Syn.subst σ q) (Syn.subst σ w) := by
  simp only [memberAt,Fm.subst_subst]
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem subst_publicAt {m : ℕ} (σ : Fin n → PTm m) (B : Fm PTm 1) (q : PTm n) :
    (publicAt B q).subst σ = publicAt B (Syn.subst σ q) := by
  simp only [publicAt,Fm.subst_subst]
  congr 1
  funext i
  fin_cases i
  rfl
@[simp] theorem subst_contains {m : ℕ} (σ : Fin n → PTm m) (A : Fm PTm 2) (W q : PTm n) :
    (contains A W q).subst σ = contains A (Syn.subst σ W) (Syn.subst σ q) := by
  simp only [contains, Fm.subst_ex, Fm.subst_and, subst_lt, SequenceComposition.subst_length, subst_memberAt,
    MasterCertificate.subst_entry, Syn.subst_var, Syn.up_zero, Syn.subst_shift, Syn.shift_subst, Syn.up_succ]
@[simp] theorem subst_candidates {m : ℕ} (σ : Fin n → PTm m) (f : PTm 2) (N x : PTm n) :
    Syn.subst σ (candidates f N x) = candidates f (Syn.subst σ N) (Syn.subst σ x) := by simp [candidates]
ipra_subst valueCap
ipra_subst codeBound

theorem member_congr (A : Fm PTm 2) {q q' w w' : PTm n}
    (hq : Γ ⊢[PRAAx] q ≐ q') (hw : Γ ⊢[PRAAx] w ≐ w') (h : Γ ⊢[PRAAx] memberAt A q w) :
    Γ ⊢[PRAAx] memberAt A q' w' :=
  Prf.eqSubst A ![q,w] ![q',w'] (fun i => by fin_cases i; exact hq; exact hw) h
theorem contains_intro (A : Fm PTm 2) (W q i : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length W)) (h : Γ ⊢[PRAAx] memberAt A q (entry W i)) :
    Γ ⊢[PRAAx] contains A W q := by
  apply Prf.exI i
  simpa only [contains,Fm.subst_and,subst_lt,SequenceComposition.subst_length,subst_memberAt,
    MasterCertificate.subst_entry,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.andI hi h
theorem contains_nonempty (A : Fm PTm 2) (W q : PTm n) (h : Γ ⊢[PRAAx] contains A W q) :
    Γ ⊢[PRAAx] lt zero (length W) := by
  refine .exE h ?_
  let Δ := (lt (var 0) (length (Syn.shift W)) ⋏ memberAt A (Syn.shift q) (entry (Syn.shift W) (var 0))) :: Γ.map Fm.shift
  have bound : Δ ⊢[PRAAx] lt zero (length (Syn.shift W)) := lt_of_le_of_lt (zero_le _) (Prf.andE₁ Prf.hyp0)
  simpa only [Δ,Fm.shift,subst_lt,SequenceComposition.subst_length,ConciseIPRA.PTm.subst_zero,Syn.shift] using bound
theorem empty_rejected (A : Fm PTm 2) (W q : PTm n) (hW : Γ ⊢[PRAAx] length W ≐ zero) :
    Γ ⊢[PRAAx] neg (contains A W q) := by
  refine .impI ?_
  exact lt_irrefl zero _ (lt_congr (.eqRefl _) hW.wk (contains_nonempty A W q Prf.hyp0))

theorem candidates_length (f : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx] length (candidates f N x) ≐ N :=
  MasterCertificate.sequence_length _ _ _
theorem candidates_lookup (f : PTm 2) (N x i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] entry (candidates f N x) i ≐ inst2 f i x := MasterCertificate.sequence_decode f hi
theorem candidates_program (f : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx] runList f N x ≐ candidates f N x := by
  simpa [runList,listF,ap2] using toPR_eq (Γ := Γ) (candidates f (var 0) (var 1)) ![N,x]
theorem candidates_value_bound (f : PTm 2) (N x i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] lt (entry (candidates f N x) i) (valueCap f N x) :=
  lt_congr (candidates_lookup f N x i hi).eqSymm (.eqRefl _)
    (Order.lt_succ_of_le (finiteMaximum_at f hi))
theorem candidates_code_bound (f : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] lt (candidates f N x) (codeBound f N x) := by
  have points : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 f (var 0) (Syn.shift x)) (inst2 (var 1 : PTm 2) (var 0) (Syn.shift (valueCap f N x)))) := by
    refine .allI (.impI ?_)
    have bound := le_trans (finiteMaximum_at (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) f Prf.hyp0)
      (le_succ_self (finiteMaximum f (Syn.shift N) (Syn.shift x)))
    simpa only [inst2,Syn.subst_var,Matrix.cons_val_one,Matrix.cons_val_zero,Matrix.head_cons,Matrix.tail_cons,Syn.shift,subst_valueCap,valueCap,ConciseIPRA.PTm.subst_succ,subst_finiteMaximum] using bound
  exact Order.lt_succ_of_le (sequence_mono f (var 1) N x (valueCap f N x) points)

/-- The actual compiled finite disjunction over the actual list decoder. -/
def checkerFormula (A : BFm 2) : BFm 2 :=
  .ex (length (var 0)) (A.subst ![var 2,entry (var 1) (var 0)])
def verifierF (A : BFm 2) : PR 2 := BoundedSyntax.bitF (checkerFormula A)
def check (A : BFm 2) (W q : PTm n) : PTm n := ap2 (verifierF A) W q
theorem checker_meaning (A : BFm 2) (W q : PTm n) :
    (BoundedSyntax.formula (checkerFormula A)).subst ![W,q] = contains (BoundedSyntax.formula A) W q := by
  simp only [checkerFormula, BoundedSyntax.formula, BoundedSyntax.formula_subst, Fm.subst_ex, Fm.subst_and, subst_lt,
    Fm.subst_subst, contains, memberAt]
  apply congrArg Fm.ex
  congr 1
  · simp [Syn.up,Syn.shift]
  · congr 1
    funext i
    fin_cases i <;> simp [Syn.up, Syn.shift]

theorem check_reflection (A : BFm 2) (W q : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (check A W q ≐ one) (contains (BoundedSyntax.formula A) W q) := by
  have e := BoundedSyntax.program_correct (checkerFormula A) ![W,q] (Γ := Γ)
  exact (RealizerMasterInterface.eq_one_iff e).iffTrans (by
    simpa only [checker_meaning] using BoundedSyntax.bounded_reflection (Γ := Γ) (checkerFormula A) ![W,q])
theorem check_cases (A : BFm 2) (W q : PTm n) : Γ ⊢[PRAAx]
    (check A W q ≐ zero) ⋎ (check A W q ≐ one) := by
  have e := BoundedSyntax.program_correct (checkerFormula A) ![W,q] (Γ := Γ)
  exact .orE (BoundedSyntax.bit_cases (checkerFormula A) ![W,q])
    (.orI₁ (e.wk.eqTrans Prf.hyp0)) (.orI₂ (e.wk.eqTrans Prf.hyp0))
theorem check_empty (A : BFm 2) (W q : PTm n) (hW : Γ ⊢[PRAAx] length W ≐ zero) :
    Γ ⊢[PRAAx] check A W q ≐ zero := by
  refine .orE (check_cases A W q) Prf.hyp0 ?_
  exact .botE _ (.impE (empty_rejected (BoundedSyntax.formula A) W q hW).wk
    ((check_reflection A W q).iffMp Prf.hyp0))
theorem generated_member (A : BFm 2) (f : PTm 2) (N x q i : PTm n)
    (hi : Γ ⊢[PRAAx] lt i N) (h : Γ ⊢[PRAAx] memberAt (BoundedSyntax.formula A) q (inst2 f i x)) :
    Γ ⊢[PRAAx] check A (candidates f N x) q ≐ one :=
  (check_reflection A _ q).iffMpr (contains_intro (BoundedSyntax.formula A) _ q i
    (lt_congr (.eqRefl _) (candidates_length f N x).eqSymm hi)
    (member_congr _ (.eqRefl _) (candidates_lookup f N x i hi).eqSymm h))

def mappedBody (U : PR 2) : PTm 2 := ap2 U (entry (fstT (var 1)) (var 0)) (sndT (var 1))
def mapped (U : PR 2) (W q : PTm n) : PTm n := sequence (mappedBody U) (length W) (pairT W q)
def mapF (U : PR 2) : PR 2 := PTm.toPR (mapped U (var 0) (var 1))
ipra_subst mapped
theorem map_body_at (U : PR 2) (W q i : PTm n) : Γ ⊢[PRAAx]
    inst2 (mappedBody U) i (pairT W q) ≐ ap2 U (entry W i) q := by
  simpa [mappedBody,inst2] using congrAp2 U (entry_congr (fst_pair W q) (.eqRefl i)) (snd_pair W q)
theorem mapped_length (U : PR 2) (W q : PTm n) : Γ ⊢[PRAAx] length (mapped U W q) ≐ length W :=
  MasterCertificate.sequence_length _ _ _
theorem mapped_lookup (U : PR 2) (W q i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length W)) :
    Γ ⊢[PRAAx] entry (mapped U W q) i ≐ ap2 U (entry W i) q :=
  (MasterCertificate.sequence_decode (mappedBody U) hi).eqTrans (map_body_at U W q i)
theorem map_program (U : PR 2) (W q : PTm n) : Γ ⊢[PRAAx] ap2 (mapF U) W q ≐ mapped U W q := by
  simpa [mapF,ap2] using toPR_eq (Γ := Γ) (mapped U (var 0) (var 1)) ![W,q]

/-- Only a valid member is mapped; validity of every listed candidate is
neither assumed nor needed. The finite witness index remains local. -/
theorem map_contains (A B : Fm PTm 2) (U : PR 2)
    (hU : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (q w : PTm k),
      (Δ ⊢[PRAAx] memberAt A q w) → (Δ ⊢[PRAAx] memberAt B q (ap2 U w q)))
    (W q : PTm n) (h : Γ ⊢[PRAAx] contains A W q) :
    Γ ⊢[PRAAx] contains B (mapped U W q) q := by
  refine .exE h ?_
  let Δ := (lt (var 0) (length (Syn.shift W)) ⋏ memberAt A (Syn.shift q) (entry (Syn.shift W) (var 0))) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift W)) := .andE₁ Prf.hyp0
  have hb := hU (Syn.shift q) (entry (Syn.shift W) (var 0)) (Prf.andE₂ (Prf.hyp0 : Δ ⊢[PRAAx] _))
  have out := contains_intro B (mapped U (Syn.shift W) (Syn.shift q)) (Syn.shift q) (var 0)
    (lt_congr (.eqRefl _) (mapped_length U (Syn.shift W) (Syn.shift q)).eqSymm hi)
    (member_congr B (.eqRefl _) (mapped_lookup U (Syn.shift W) (Syn.shift q) (var 0) hi).eqSymm hb)
  simpa only [Δ,Fm.shift,subst_contains,subst_mapped,Syn.shift] using out
theorem map_verified (A B : BFm 2) (U : PR 2)
    (hU : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (q w : PTm k),
      (Δ ⊢[PRAAx] memberAt (BoundedSyntax.formula A) q w) →
      (Δ ⊢[PRAAx] memberAt (BoundedSyntax.formula B) q (ap2 U w q)))
    (W q : PTm n) (h : Γ ⊢[PRAAx] check A W q ≐ one) :
    Γ ⊢[PRAAx] check B (mapped U W q) q ≐ one :=
  (check_reflection B _ _).iffMpr (map_contains _ _ U hU W q ((check_reflection A W q).iffMp h))

/-- A fixed public conclusion has no candidate or index variable. This is
the invariant finite-disjunction elimination advertised by the source. -/
theorem invariant_eliminate (A : Fm PTm 2) (B : Fm PTm 1)
    (hB : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (q w : PTm k),
      (Δ ⊢[PRAAx] memberAt A q w) → (Δ ⊢[PRAAx] publicAt B q))
    (W q : PTm n) (h : Γ ⊢[PRAAx] contains A W q) : Γ ⊢[PRAAx] publicAt B q := by
  refine .exE h ?_
  let Δ := (lt (var 0) (length (Syn.shift W)) ⋏ memberAt A (Syn.shift q) (entry (Syn.shift W) (var 0))) :: Γ.map Fm.shift
  have out := hB (Syn.shift q) (entry (Syn.shift W) (var 0)) (Prf.andE₂ (Prf.hyp0 : Δ ⊢[PRAAx] _))
  simpa only [Δ,Fm.shift,subst_publicAt,Syn.shift] using out
theorem verified_invariant (A : BFm 2) (B : Fm PTm 1)
    (hB : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (q w : PTm k),
      (Δ ⊢[PRAAx] memberAt (BoundedSyntax.formula A) q w) → (Δ ⊢[PRAAx] publicAt B q))
    (W q : PTm n) (h : Γ ⊢[PRAAx] check A W q ≐ one) : Γ ⊢[PRAAx] publicAt B q :=
  invariant_eliminate _ B hB W q ((check_reflection A W q).iffMp h)

def enumeration (B : PTm n) : PTm n := candidates (var 0) B zero
def possible (A : Fm PTm 2) (B q : PTm n) : Fm PTm n :=
  .ex (lt (var 0) (Syn.shift B) ⋏ memberAt A (Syn.shift q) (var 0))
ipra_subst enumeration
@[simp] theorem subst_possible {m : ℕ} (σ : Fin n → PTm m) (A : Fm PTm 2) (B q : PTm n) :
    (possible A B q).subst σ = possible A (Syn.subst σ B) (Syn.subst σ q) := by
  simp only [possible,Fm.subst_ex,Fm.subst_and,subst_lt,subst_memberAt,Syn.subst_var,Syn.up_zero,
    Syn.subst_shift,Syn.shift_subst,Syn.up_succ]
theorem enumeration_length (B : PTm n) : Γ ⊢[PRAAx] length (enumeration B) ≐ B := candidates_length _ _ _
theorem enumeration_lookup (B i : PTm n) (hi : Γ ⊢[PRAAx] lt i B) : Γ ⊢[PRAAx] entry (enumeration B) i ≐ i :=
  candidates_lookup (var 0) B zero i hi
theorem enumeration_complete (A : Fm PTm 2) (B q : PTm n) (h : Γ ⊢[PRAAx] possible A B q) :
    Γ ⊢[PRAAx] contains A (enumeration B) q := by
  refine .exE h ?_
  let Δ := (lt (var 0) (Syn.shift B) ⋏ memberAt A (Syn.shift q) (var 0)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (Syn.shift B) := .andE₁ Prf.hyp0
  have out := contains_intro A (enumeration (Syn.shift B)) (Syn.shift q) (var 0)
    (lt_congr (.eqRefl _) (enumeration_length (Syn.shift B)).eqSymm hi)
    (member_congr A (.eqRefl _) (enumeration_lookup (Syn.shift B) (var 0) hi).eqSymm (.andE₂ Prf.hyp0))
  simpa only [Δ,Fm.shift,subst_contains,subst_enumeration,Syn.shift] using out
theorem enumeration_sound (A : Fm PTm 2) (B q : PTm n) (h : Γ ⊢[PRAAx] contains A (enumeration B) q) :
    Γ ⊢[PRAAx] possible A B q := by
  refine .exE h ?_
  let Δ := (lt (var 0) (length (Syn.shift (enumeration B))) ⋏
    memberAt A (Syn.shift q) (entry (Syn.shift (enumeration B)) (var 0))) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (Syn.shift B) :=
    lt_congr (.eqRefl _) (enumeration_length (Syn.shift B))
      (by simpa only [Δ,Syn.shift,subst_enumeration] using (Prf.andE₁ (Prf.hyp0 : Δ ⊢[PRAAx] _)))
  have ha : Δ ⊢[PRAAx] memberAt A (Syn.shift q) (var 0) := member_congr A (.eqRefl _)
    (enumeration_lookup (Syn.shift B) (var 0) hi)
    (by simpa only [Δ,Syn.shift,subst_enumeration] using (Prf.andE₂ (Prf.hyp0 : Δ ⊢[PRAAx] _)))
  have out : Δ ⊢[PRAAx] possible A (Syn.shift B) (Syn.shift q) := by
    apply Prf.exI (var 0)
    simpa only [possible,Fm.subst_and,subst_lt,subst_memberAt,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.andI hi ha
  simpa only [Δ,Fm.shift,subst_possible,Syn.shift] using out
theorem enumeration_verified (A : BFm 2) (B q : PTm n)
    (h : Γ ⊢[PRAAx] possible (BoundedSyntax.formula A) B q) :
    Γ ⊢[PRAAx] check A (enumeration B) q ≐ one :=
  (check_reflection A _ _).iffMpr (enumeration_complete _ B q h)

def memberBit (A : BFm 2) (W q i : PTm n) : PTm n := ap2 (BoundedSyntax.bitF A) q (entry W i)
def searchData (W q : PTm n) : PTm n := pairT W q
def searchBody (A : BFm 2) : PTm 2 := memberBit A (fstT (var 1)) (sndT (var 1)) (var 0)
def leastIndex (A : BFm 2) (W q : PTm n) : PTm n :=
  BooleanizationCorollaries.first (searchBody A) (length W) (searchData W q)
def chosen (A : BFm 2) (W q : PTm n) : PTm n := entry W (leastIndex A W q)
@[simp] theorem subst_memberBit {m : ℕ} (σ : Fin n → PTm m) (A : BFm 2) (W q i : PTm n) :
    Syn.subst σ (memberBit A W q i) = memberBit A (Syn.subst σ W) (Syn.subst σ q) (Syn.subst σ i) := by simp [memberBit]
ipra_subst searchData
ipra_subst leastIndex [BooleanizationCorollaries.first, Search.mu]
ipra_subst chosen
theorem member_bit_reflection (A : BFm 2) (W q i : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (memberBit A W q i ≐ one) (memberAt (BoundedSyntax.formula A) q (entry W i)) := by
  have e := BoundedSyntax.program_correct A ![q,entry W i] (Γ := Γ)
  exact (RealizerMasterInterface.eq_one_iff e).iffTrans (BoundedSyntax.bounded_reflection A ![q,entry W i])
theorem member_bit_cases (A : BFm 2) (W q i : PTm n) : Γ ⊢[PRAAx]
    (memberBit A W q i ≐ zero) ⋎ (memberBit A W q i ≐ one) := by
  have e := BoundedSyntax.program_correct A ![q,entry W i] (Γ := Γ)
  exact .orE (BoundedSyntax.bit_cases A ![q,entry W i])
    (.orI₁ (e.wk.eqTrans Prf.hyp0)) (.orI₂ (e.wk.eqTrans Prf.hyp0))
theorem search_body_at (A : BFm 2) (W q i : PTm n) : Γ ⊢[PRAAx]
    inst2 (searchBody A) i (searchData W q) ≐ memberBit A W q i := by
  simpa [searchBody,memberBit,searchData,inst2] using
    congrAp2 (BoundedSyntax.bitF A) (snd_pair W q) (entry_congr (fst_pair W q) (.eqRefl i))
theorem search_body_cases (A : BFm 2) (W q i : PTm n) : Γ ⊢[PRAAx]
    (inst2 (searchBody A) i (searchData W q) ≐ zero) ⋎
      (inst2 (searchBody A) i (searchData W q) ≐ one) := by
  have e := search_body_at (Γ := Γ) A W q i
  exact .orE (member_bit_cases A W q i) (.orI₁ (e.wk.eqTrans Prf.hyp0)) (.orI₂ (e.wk.eqTrans Prf.hyp0))
theorem least_bound (A : BFm 2) (W q : PTm n) : Γ ⊢[PRAAx] le (leastIndex A W q) (length W) :=
  BooleanizationCorollaries.first_le _ _ _
theorem least_found (A : BFm 2) (W q : PTm n) (hi : Γ ⊢[PRAAx] lt (leastIndex A W q) (length W)) :
    Γ ⊢[PRAAx] memberAt (BoundedSyntax.formula A) q (chosen A W q) :=
  (member_bit_reflection A W q _).iffMp
    ((search_body_at A W q _).eqSymm.eqTrans
      (BooleanizationCorollaries.first_found _ (search_body_cases A W q _) hi))
theorem least_before (A : BFm 2) (W q i : PTm n) (hi : Γ ⊢[PRAAx] lt i (leastIndex A W q)) :
    Γ ⊢[PRAAx] neg (memberAt (BoundedSyntax.formula A) q (entry W i)) := by
  have rejected := (search_body_at (Γ := Γ) A W q i).eqSymm.eqTrans
    (BooleanizationCorollaries.first_before _ (search_body_cases A W q i) hi)
  refine .impI ?_
  have accepted := (member_bit_reflection (Γ := memberAt (BoundedSyntax.formula A) q (entry W i) :: Γ) A W q i).iffMpr Prf.hyp0
  exact BoundedReflection.one_ne_zero _ (accepted.eqSymm.eqTrans rejected.wk)
theorem member_bounds_index (A : BFm 2) (W q i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length W))
    (ha : Γ ⊢[PRAAx] memberAt (BoundedSyntax.formula A) q (entry W i)) : Γ ⊢[PRAAx]
    lt (leastIndex A W q) (length W) ⋏ le (leastIndex A W q) i := by
  have accepted := (member_bit_reflection A W q i).iffMpr ha
  have z := (congrMonus (.eqRefl one) ((search_body_at A W q i).eqTrans accepted)).eqTrans (monus_self one)
  have found := Search.search_found (f := BooleanizationCorollaries.nf (searchBody A))
    (by simpa only [BooleanizationCorollaries.inst2_nf] using z) hi
  exact .andI (.andE₁ found) (.andE₂ (.andE₂ found))
theorem verified_range (A : BFm 2) (W q : PTm n) (h : Γ ⊢[PRAAx] check A W q ≐ one) :
    Γ ⊢[PRAAx] lt (leastIndex A W q) (length W) := by
  refine .exE ((check_reflection A W q).iffMp h) ?_
  let Δ := (lt (var 0) (length (Syn.shift W)) ⋏
    memberAt (BoundedSyntax.formula A) (Syn.shift q) (entry (Syn.shift W) (var 0))) :: Γ.map Fm.shift
  have bound := Prf.andE₁ (member_bounds_index (Γ := Δ) A (Syn.shift W) (Syn.shift q) (var 0)
    (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0))
  simpa only [Δ,Fm.shift,subst_lt,subst_leastIndex,SequenceComposition.subst_length,Syn.shift] using bound
theorem verified_chosen (A : BFm 2) (W q : PTm n) (h : Γ ⊢[PRAAx] check A W q ≐ one) :
    Γ ⊢[PRAAx] memberAt (BoundedSyntax.formula A) q (chosen A W q) := least_found A W q (verified_range A W q h)
theorem rejected_default (A : BFm 2) (W q : PTm n) (h : Γ ⊢[PRAAx] check A W q ≐ zero) :
    Γ ⊢[PRAAx] leastIndex A W q ≐ length W := by
  refine le_antisymm (least_bound A W q) ?_
  refine .orE (lt_or_le (leastIndex A W q) (length W)) ?_ Prf.hyp0
  let Δ := lt (leastIndex A W q) (length W) :: Γ
  have accepted : Δ ⊢[PRAAx] check A W q ≐ one :=
    (check_reflection A W q).iffMpr (contains_intro _ W q _ Prf.hyp0 (least_found A W q Prf.hyp0))
  exact .botE _ (BoundedReflection.one_ne_zero _ (accepted.eqSymm.eqTrans h.wk))
theorem default_rejected (A : BFm 2) (W q : PTm n) (h : Γ ⊢[PRAAx] leastIndex A W q ≐ length W) :
    Γ ⊢[PRAAx] check A W q ≐ zero := by
  refine .orE (check_cases A W q) Prf.hyp0 ?_
  have range := verified_range (Γ := (check A W q ≐ one) :: Γ) A W q Prf.hyp0
  exact lt_irrefl (length W) _ (lt_congr h.wk (.eqRefl _) range)
theorem least_empty (A : BFm 2) (W q : PTm n) (h : Γ ⊢[PRAAx] length W ≐ zero) :
    Γ ⊢[PRAAx] leastIndex A W q ≐ zero :=
  le_antisymm (le_congr (.eqRefl _) h (least_bound A W q)) (zero_le _)
theorem enumeration_chosen_is_index (A : BFm 2) (B q : PTm n)
    (h : Γ ⊢[PRAAx] possible (BoundedSyntax.formula A) B q) : Γ ⊢[PRAAx]
    chosen A (enumeration B) q ≐ leastIndex A (enumeration B) q :=
  enumeration_lookup B _ (lt_congr (.eqRefl _) (enumeration_length B)
    (verified_range A _ q (enumeration_verified A B q h)))

def familyPossible (A : Fm PTm 2) (f : PTm 2) (N x q : PTm n) : Fm PTm n :=
  .ex (lt (var 0) (Syn.shift N) ⋏ memberAt A (Syn.shift q) (inst2 f (var 0) (Syn.shift x)))
theorem generated_possible (A : BFm 2) (f : PTm 2) (N x q : PTm n)
    (h : Γ ⊢[PRAAx] familyPossible (BoundedSyntax.formula A) f N x q) :
    Γ ⊢[PRAAx] check A (candidates f N x) q ≐ one := by
  refine .exE h ?_
  let Δ := (lt (var 0) (Syn.shift N) ⋏
    memberAt (BoundedSyntax.formula A) (Syn.shift q) (inst2 f (var 0) (Syn.shift x))) :: Γ.map Fm.shift
  have out := generated_member (Γ := Δ) A f (Syn.shift N) (Syn.shift x) (Syn.shift q) (var 0)
    (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0)
  simpa only [Δ,Fm.shift,Fm.subst_eq,check,subst_ap2,subst_candidates,Syn.shift,ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] using out

def capsule (f : PTm 2) (A : BFm 2) (N x q : PTm n) : PTm n :=
  pairT (candidates f N x) (pairT (valueCap f N x) (pairT (codeBound f N x) (check A (candidates f N x) q)))
def capsuleF (f : PTm 2) (A : BFm 2) : PR 3 := PTm.toPR (capsule f A (var 0) (var 1) (var 2))
def runCapsule (f : PTm 2) (A : BFm 2) (N x q : PTm n) : PTm n := ap3 (capsuleF f A) N x q
def selection (A : BFm 2) (W q : PTm n) : PTm n := pairT (leastIndex A W q) (chosen A W q)
def selectionF (A : BFm 2) : PR 2 := PTm.toPR (selection A (var 0) (var 1))
def runSelection (A : BFm 2) (W q : PTm n) : PTm n := ap2 (selectionF A) W q
ipra_subst check
ipra_subst capsule
ipra_subst selection
theorem capsule_program (f : PTm 2) (A : BFm 2) (N x q : PTm n) : Γ ⊢[PRAAx]
    runCapsule f A N x q ≐ capsule f A N x q := by
  simpa [runCapsule,capsuleF,ap3] using toPR_eq (Γ := Γ) (capsule f A (var 0) (var 1) (var 2)) ![N,x,q]
theorem selection_program (A : BFm 2) (W q : PTm n) : Γ ⊢[PRAAx] runSelection A W q ≐ selection A W q := by
  simpa [runSelection,selectionF,ap2] using toPR_eq (Γ := Γ) (selection A (var 0) (var 1)) ![W,q]
theorem returned_list (f : PTm 2) (A : BFm 2) (N x q : PTm n) : Γ ⊢[PRAAx]
    fstT (runCapsule f A N x q) ≐ candidates f N x := (congrFst (capsule_program f A N x q)).eqTrans (fst_pair _ _)
theorem returned_value_cap (f : PTm 2) (A : BFm 2) (N x q : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (runCapsule f A N x q)) ≐ valueCap f N x :=
  (congrFst ((congrSnd (capsule_program f A N x q)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_code_bound (f : PTm 2) (A : BFm 2) (N x q : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (runCapsule f A N x q))) ≐ codeBound f N x :=
  (congrFst ((congrSnd ((congrSnd (capsule_program f A N x q)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_check (f : PTm 2) (A : BFm 2) (N x q : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (runCapsule f A N x q))) ≐ check A (candidates f N x) q :=
  (congrSnd ((congrSnd ((congrSnd (capsule_program f A N x q)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_index (A : BFm 2) (W q : PTm n) : Γ ⊢[PRAAx] fstT (runSelection A W q) ≐ leastIndex A W q :=
  (congrFst (selection_program A W q)).eqTrans (fst_pair _ _)
theorem returned_member (A : BFm 2) (W q : PTm n) : Γ ⊢[PRAAx] sndT (runSelection A W q) ≐ chosen A W q :=
  (congrSnd (selection_program A W q)).eqTrans (snd_pair _ _)
theorem returned_bounds (f : PTm 2) (A : BFm 2) (N x q i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    lt (entry (fstT (runCapsule f A N x q)) i) (fstT (sndT (runCapsule f A N x q))) ⋏
      lt (fstT (runCapsule f A N x q)) (fstT (sndT (sndT (runCapsule f A N x q)))) :=
  .andI (lt_congr (entry_congr (returned_list f A N x q) (.eqRefl _)).eqSymm (returned_value_cap f A N x q).eqSymm
    (candidates_value_bound f N x i hi))
    (lt_congr (returned_list f A N x q).eqSymm (returned_code_bound f A N x q).eqSymm (candidates_code_bound f N x))
theorem returned_verified (f : PTm 2) (A : BFm 2) (N x q : PTm n)
    (h : Γ ⊢[PRAAx] familyPossible (BoundedSyntax.formula A) f N x q) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (runCapsule f A N x q))) ≐ one :=
  (returned_check f A N x q).eqTrans (generated_possible A f N x q h)
theorem returned_selection (A : BFm 2) (W q : PTm n) (h : Γ ⊢[PRAAx] check A W q ≐ one) : Γ ⊢[PRAAx]
    lt (fstT (runSelection A W q)) (length W) ⋏
      memberAt (BoundedSyntax.formula A) q (sndT (runSelection A W q)) :=
  .andI (lt_congr (returned_index A W q).eqSymm (.eqRefl _) (verified_range A W q h))
    (member_congr _ (.eqRefl _) (returned_member A W q).eqSymm (verified_chosen A W q h))

/-! ## Closed endpoints preserve the runtime lists and numerical bounds -/

theorem capsule_disjunction_closed (A : BFm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (Fm.iff (check A (var 0) (var 1) ≐ one) (contains (BoundedSyntax.formula A) (var 0) (var 1))) :=
  closeUniv 2 (check_reflection A _ _)
theorem capsule_empty_closed (A : BFm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (length (var 0) ≐ zero ⟶ check A (var 0) (var 1) ≐ zero) :=
  closeUniv 2 (.impI (check_empty A _ _ Prf.hyp0))
theorem capsule_list_program_closed (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (runList f (var 0) (var 1) ≐ candidates f (var 0) (var 1) ⋏
      (length (candidates f (var 0) (var 1)) ≐ var 0 ⋏ lt (candidates f (var 0) (var 1)) (codeBound f (var 0) (var 1)))) :=
  closeUniv 2 (.andI (candidates_program f _ _) (.andI (candidates_length f _ _) (candidates_code_bound f _ _)))
theorem capsule_lookup_closed (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 0) ⟶ entry (candidates f (var 0) (var 1)) (var 2) ≐ inst2 f (var 2) (var 1) ⋏
      lt (entry (candidates f (var 0) (var 1)) (var 2)) (valueCap f (var 0) (var 1))) :=
  closeUniv 3 (.impI (.andI (candidates_lookup f _ _ _ Prf.hyp0) (candidates_value_bound f _ _ _ Prf.hyp0)))
theorem capsule_enumeration_closed (A : BFm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (Fm.iff (check A (enumeration (var 0)) (var 1) ≐ one)
      (possible (BoundedSyntax.formula A) (var 0) (var 1))) := closeUniv 2
  (.andI (.impI (enumeration_sound _ _ _ ((check_reflection A _ _).iffMp Prf.hyp0)))
    (.impI (enumeration_verified A _ _ Prf.hyp0)))
theorem capsule_generated_closed (A : BFm 2) (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (familyPossible (BoundedSyntax.formula A) f (var 0) (var 1) (var 2) ⟶
      check A (candidates f (var 0) (var 1)) (var 2) ≐ one) :=
  closeUniv 3 (.impI (generated_possible A f _ _ _ Prf.hyp0))
theorem capsule_mapping_closed (A B : BFm 2) (U : PR 2)
    (hU : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (q w : PTm k),
      (Δ ⊢[PRAAx] memberAt (BoundedSyntax.formula A) q w) →
      (Δ ⊢[PRAAx] memberAt (BoundedSyntax.formula B) q (ap2 U w q))) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (check A (var 0) (var 1) ≐ one ⟶ check B (mapped U (var 0) (var 1)) (var 1) ≐ one) :=
  closeUniv 2 (.impI (map_verified A B U hU _ _ Prf.hyp0))
theorem capsule_invariant_closed (A : BFm 2) (B : Fm PTm 1)
    (hB : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (q w : PTm k),
      (Δ ⊢[PRAAx] memberAt (BoundedSyntax.formula A) q w) → (Δ ⊢[PRAAx] publicAt B q)) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (check A (var 0) (var 1) ≐ one ⟶ publicAt B (var 1)) :=
  closeUniv 2 (.impI (verified_invariant A B hB _ _ Prf.hyp0))
theorem capsule_least_closed (A : BFm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (check A (var 0) (var 1) ≐ one ⟶
      lt (leastIndex A (var 0) (var 1)) (length (var 0)) ⋏
        (memberAt (BoundedSyntax.formula A) (var 1) (chosen A (var 0) (var 1)) ⋏
          .all (lt (var 0) (Syn.shift (leastIndex A (var 0) (var 1))) ⟶
            neg (memberAt (BoundedSyntax.formula A) (var 2) (entry (var 1) (var 0)))))) := by
  apply closeUniv 2
  refine .impI (.andI (verified_range A _ _ Prf.hyp0) (.andI (verified_chosen A _ _ Prf.hyp0) ?_))
  refine .allI (.impI ?_)
  exact least_before A (var 1) (var 2) (var 0)
    (.hyp (by simp [Syn.shift,Fin.succ_zero_eq_one,Fin.succ_one_eq_two]))
theorem capsule_default_closed (A : BFm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (Fm.iff (leastIndex A (var 0) (var 1) ≐ length (var 0)) (check A (var 0) (var 1) ≐ zero)) :=
  closeUniv 2 (.andI (.impI (default_rejected A _ _ Prf.hyp0)) (.impI (rejected_default A _ _ Prf.hyp0)))
theorem capsule_output_program_closed (f : PTm 2) (A : BFm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (runCapsule f A (var 0) (var 1) (var 2) ≐ capsule f A (var 0) (var 1) (var 2)) :=
  closeUniv 3 (capsule_program f A _ _ _)
theorem capsule_returned_selection_closed (A : BFm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (check A (var 0) (var 1) ≐ one ⟶
      lt (fstT (runSelection A (var 0) (var 1))) (length (var 0)) ⋏
        memberAt (BoundedSyntax.formula A) (var 1) (sndT (runSelection A (var 0) (var 1)))) :=
  closeUniv 2 (.impI (returned_selection A _ _ Prf.hyp0))

end LeanProofs.IPRA.Foundations.HerbrandCapsule
