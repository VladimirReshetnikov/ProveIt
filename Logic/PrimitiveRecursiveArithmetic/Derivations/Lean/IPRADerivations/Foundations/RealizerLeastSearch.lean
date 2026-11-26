import IPRADerivations.Foundations.RealizerMasterInterface
import IPRADerivations.Foundations.BoundedSelection
import IPRADerivations.Core.SubstCommand
import IPRADerivations.Core.Header

/-!
# An actual reflected least-search node over interface observations

FIBER C1's `search` node and Appendix A's `least`: the numerical exclusive
bound determines a genuine list of candidate queries. Complement search on
the compiled fixed predicate returns the first accepted index, or the bound.
The output retains the input master so its checker can independently check
both master validity and the selected index. Only the original local
same-query observation-invariance rule is needed for paired stability.
No search success, global run law or output contract is an input.

The demand is predetermined by query/parameter. Adaptive demand, cyclic
unrolling and certificate-dependent producer scopes remain separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.RealizerLeastSearch

open_ipra
open LeanProofs.IPRA.Foundations.RealizerComposition
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm)

variable {n : ℕ} {Γ : List (Fm PTm n)}

structure Code where
  bound : PR 2
  query : PR 3
  predicate : BFm 4

def queryBody (D : Code) : PTm 2 := ap3 D.query (var 0) (fstT (var 1)) (sndT (var 1))
def demands (D : Code) (q p : PTm n) : PTm n :=
  sequence (queryBody D) (ap2 D.bound q p) (pairT q p)
def demandF (D : Code) : PR 2 := PTm.toPR (demands D (var 0) (var 1))
def data (C q p : PTm n) : PTm n := pairT C (pairT q p)
def test (X : Interface) (D : Code) (C q p i : PTm n) : PTm n :=
  ap4 (BoundedSyntax.bitF D.predicate) i
    (ap3 X.observe (entry C i) (ap3 D.query i q p) p) q p
def accepted (X : Interface) (D : Code) (C q p i : PTm n) : Fm PTm n :=
  (BoundedSyntax.formula D.predicate).subst
    ![i,ap3 X.observe (entry C i) (ap3 D.query i q p) p,q,p]
def testBody (X : Interface) (D : Code) : PTm 2 :=
  test X D (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def selected (X : Interface) (D : Code) (C q p : PTm n) : PTm n :=
  BooleanizationCorollaries.first (testBody X D) (ap2 D.bound q p) (data C q p)

ipra_subst demands
ipra_subst data
ipra_subst test
@[simp] theorem subst_accepted {m : ℕ} (σ : Fin n → PTm m) (X : Interface) (D : Code) (C q p i : PTm n) :
    (accepted X D C q p i).subst σ = accepted X D (Syn.subst σ C) (Syn.subst σ q) (Syn.subst σ p) (Syn.subst σ i) := by
  unfold accepted
  rw [Fm.subst_subst]
  congr 1
  funext j
  fin_cases j <;> simp [Function.comp_def]
@[simp] theorem subst_selected {m : ℕ} (σ : Fin n → PTm m) (X : Interface) (D : Code) (C q p : PTm n) :
    Syn.subst σ (selected X D C q p) = selected X D (Syn.subst σ C) (Syn.subst σ q) (Syn.subst σ p) := by simp [selected,BooleanizationCorollaries.first,Search.mu]

theorem query_body_at (D : Code) (i q p : PTm n) : Γ ⊢[PRAAx]
    inst2 (queryBody D) i (pairT q p) ≐ ap3 D.query i q p := by
  simpa [queryBody,inst2] using congrAp3 D.query (.eqRefl i) (fst_pair q p) (snd_pair q p)
theorem demand_at (D : Code) (q p : PTm n) : Γ ⊢[PRAAx]
    ap2 (demandF D) q p ≐ demands D q p := by
  simpa [demandF,ap2] using toPR_eq (Γ := Γ) (demands D (var 0) (var 1)) ![q,p]
theorem demand_length (D : Code) (q p : PTm n) : Γ ⊢[PRAAx]
    length (demands D q p) ≐ ap2 D.bound q p := MasterCertificate.sequence_length _ _ _
theorem demand_lookup (D : Code) (q p i : PTm n) (hi : Γ ⊢[PRAAx] lt i (ap2 D.bound q p)) :
    Γ ⊢[PRAAx] entry (demands D q p) i ≐ ap3 D.query i q p :=
  (MasterCertificate.sequence_decode (queryBody D) hi).eqTrans (query_body_at D i q p)

theorem test_body_at (X : Interface) (D : Code) (C q p i : PTm n) : Γ ⊢[PRAAx]
    inst2 (testBody X D) i (data C q p) ≐ test X D C q p i := by
  simp only [testBody,subst_test,inst2,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    subst_fstT,subst_sndT]
  have hc : Γ ⊢[PRAAx] fstT (data C q p) ≐ C := fst_pair C (pairT q p)
  have hq : Γ ⊢[PRAAx] fstT (sndT (data C q p)) ≐ q :=
    (congrFst (snd_pair C (pairT q p))).eqTrans (fst_pair q p)
  have hp : Γ ⊢[PRAAx] sndT (sndT (data C q p)) ≐ p :=
    (congrSnd (snd_pair C (pairT q p))).eqTrans (snd_pair q p)
  apply congrApp (BoundedSyntax.bitF D.predicate)
  intro k
  fin_cases k
  · exact .eqRefl i
  · exact congrAp3 X.observe (SequenceComposition.entry_congr hc (.eqRefl i))
      (congrAp3 D.query (.eqRefl i) hq hp) hp
  · exact hq
  · exact hp
theorem test_reflection (X : Interface) (D : Code) (C q p i : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (test X D C q p i ≐ one) (accepted X D C q p i) := by
  have e := BoundedSyntax.program_correct D.predicate
    ![i,ap3 X.observe (entry C i) (ap3 D.query i q p) p,q,p] (Γ := Γ)
  exact (RealizerMasterInterface.eq_one_iff e).iffTrans
    (BoundedSyntax.bounded_reflection D.predicate ![i,ap3 X.observe (entry C i) (ap3 D.query i q p) p,q,p])
theorem test_cases (X : Interface) (D : Code) (C q p i : PTm n) : Γ ⊢[PRAAx]
    (test X D C q p i ≐ zero) ⋎ (test X D C q p i ≐ one) := by
  have e := BoundedSyntax.program_correct D.predicate
    ![i,ap3 X.observe (entry C i) (ap3 D.query i q p) p,q,p] (Γ := Γ)
  exact .orE (BoundedSyntax.bit_cases D.predicate ![i,ap3 X.observe (entry C i) (ap3 D.query i q p) p,q,p])
    (.orI₁ (e.wk.eqTrans Prf.hyp0)) (.orI₂ (e.wk.eqTrans Prf.hyp0))

theorem selected_bound (X : Interface) (D : Code) (C q p : PTm n) : Γ ⊢[PRAAx]
    le (selected X D C q p) (ap2 D.bound q p) := BooleanizationCorollaries.first_le _ _ _
theorem selected_found (X : Interface) (D : Code) (C q p : PTm n)
    (h : Γ ⊢[PRAAx] lt (selected X D C q p) (ap2 D.bound q p)) :
    Γ ⊢[PRAAx] accepted X D C q p (selected X D C q p) := by
  have e := test_body_at (Γ := Γ) X D C q p (selected X D C q p)
  have bit := test_cases (Γ := Γ) X D C q p (selected X D C q p)
  have b : Γ ⊢[PRAAx] (inst2 (testBody X D) (selected X D C q p) (data C q p) ≐ zero) ⋎
      (inst2 (testBody X D) (selected X D C q p) (data C q p) ≐ one) :=
    .orE bit (.orI₁ (e.wk.eqTrans Prf.hyp0)) (.orI₂ (e.wk.eqTrans Prf.hyp0))
  exact (test_reflection X D C q p _).iffMp (e.eqSymm.eqTrans (BooleanizationCorollaries.first_found _ b h))
theorem selected_before (X : Interface) (D : Code) (C q p i : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (selected X D C q p)) : Γ ⊢[PRAAx] test X D C q p i ≐ zero := by
  have e := test_body_at (Γ := Γ) X D C q p i
  have bit := test_cases (Γ := Γ) X D C q p i
  have b : Γ ⊢[PRAAx] (inst2 (testBody X D) i (data C q p) ≐ zero) ⋎
      (inst2 (testBody X D) i (data C q p) ≐ one) :=
    .orE bit (.orI₁ (e.wk.eqTrans Prf.hyp0)) (.orI₂ (e.wk.eqTrans Prf.hyp0))
  exact e.eqSymm.eqTrans (BooleanizationCorollaries.first_before _ b hi)
theorem accepted_bound (X : Interface) (D : Code) (C q p i : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (ap2 D.bound q p)) (ha : Γ ⊢[PRAAx] accepted X D C q p i) :
    Γ ⊢[PRAAx] lt (selected X D C q p) (ap2 D.bound q p) ⋏ le (selected X D C q p) i := by
  have bit := (test_reflection X D C q p i).iffMpr ha
  have z := (congrMonus (.eqRefl one) ((test_body_at X D C q p i).eqTrans bit)).eqTrans (monus_self one)
  have found := Search.search_found (f := BooleanizationCorollaries.nf (testBody X D)) (by
    simpa only [BooleanizationCorollaries.inst2_nf] using z) hi
  exact .andI (.andE₁ found) (.andE₂ (.andE₂ found))
theorem rejected_before (X : Interface) (D : Code) (C q p i : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (selected X D C q p)) :
    Γ ⊢[PRAAx] neg (accepted X D C q p i) := by
  refine .impI ?_
  have e := (test_reflection (Γ := accepted X D C q p i :: Γ) X D C q p i).iffMpr Prf.hyp0
  exact BoundedReflection.one_ne_zero _ (e.eqSymm.eqTrans (selected_before X D C q p i hi.wk))

theorem empty_bound (X : Interface) (D : Code) (C q p : PTm n)
    (hB : Γ ⊢[PRAAx] ap2 D.bound q p ≐ zero) : Γ ⊢[PRAAx] selected X D C q p ≐ zero :=
  le_antisymm (le_congr (.eqRefl _) hB (selected_bound X D C q p)) (zero_le _)

/-- The only client law: a fixed reflected test respects the declared relation
at the same candidate query. No selector or output law is a field. -/
structure Laws (X : Interface) (D : Code) : Prop where
  invariant : ∀ {n : ℕ} {Γ : List (Fm PTm n)} (i c c' q p : PTm n),
    (Γ ⊢[PRAAx] valid X c (ap3 D.query i q p) p) →
    (Γ ⊢[PRAAx] valid X c' (ap3 D.query i q p) p) →
    (Γ ⊢[PRAAx] related X c c' (ap3 D.query i q p) p) →
    (Γ ⊢[PRAAx] Fm.iff
      ((BoundedSyntax.formula D.predicate).subst ![i,ap3 X.observe c (ap3 D.query i q p) p,q,p])
      ((BoundedSyntax.formula D.predicate).subst ![i,ap3 X.observe c' (ap3 D.query i q p) p,q,p]))

theorem accepted_invariant {X : Interface} {D : Code} (h : Laws X D) (C C' q p i : PTm n)
    (hC : Γ ⊢[PRAAx] masterValid X (demands D q p) C p)
    (hC' : Γ ⊢[PRAAx] masterValid X (demands D q p) C' p)
    (hr : Γ ⊢[PRAAx] masterRelated X (demands D q p) C C' p)
    (hi : Γ ⊢[PRAAx] lt i (ap2 D.bound q p)) :
    Γ ⊢[PRAAx] Fm.iff (accepted X D C q p i) (accepted X D C' q p i) := by
  have hil := lt_congr (.eqRefl _) (demand_length D q p).eqSymm hi
  have e := demand_lookup D q p i hi
  have a := valid_congr X (.eqRefl _) e (.eqRefl _) (master_values_at X (.andE₂ (.andE₂ hC)) hil)
  have b := valid_congr X (.eqRefl _) e (.eqRefl _) (master_values_at X (.andE₂ (.andE₂ hC')) hil)
  have r := related_congr X (.eqRefl _) (.eqRefl _) e (.eqRefl _) (master_related_at X hr hil)
  exact h.invariant i (entry C i) (entry C' i) q p a b r

theorem selected_stable {X : Interface} {D : Code} (h : Laws X D) (C C' q p : PTm n)
    (hC : Γ ⊢[PRAAx] masterValid X (demands D q p) C p)
    (hC' : Γ ⊢[PRAAx] masterValid X (demands D q p) C' p)
    (hr : Γ ⊢[PRAAx] masterRelated X (demands D q p) C C' p) :
    Γ ⊢[PRAAx] selected X D C q p ≐ selected X D C' q p := by
  have left : Γ ⊢[PRAAx] le (selected X D C q p) (selected X D C' q p) := by
    refine .orE (lt_or_le (selected X D C' q p) (selected X D C q p)) ?_ Prf.hyp0
    let Δ := lt (selected X D C' q p) (selected X D C q p) :: Γ
    have hi : Δ ⊢[PRAAx] lt (selected X D C' q p) (ap2 D.bound q p) :=
      lt_of_lt_of_le Prf.hyp0 (selected_bound X D C q p).wk
    have ha := selected_found X D C' q p hi
    have hb := (accepted_invariant h C C' q p _ hC.wk hC'.wk hr.wk hi).iffMpr ha
    have one := (test_reflection X D C q p _).iffMpr hb
    have z := selected_before (Γ := Δ) X D C q p (selected X D C' q p) Prf.hyp0
    exact .botE _ (BoundedReflection.one_ne_zero _ (one.eqSymm.eqTrans z))
  have right : Γ ⊢[PRAAx] le (selected X D C' q p) (selected X D C q p) := by
    refine .orE (lt_or_le (selected X D C q p) (selected X D C' q p)) ?_ Prf.hyp0
    let Δ := lt (selected X D C q p) (selected X D C' q p) :: Γ
    have hi : Δ ⊢[PRAAx] lt (selected X D C q p) (ap2 D.bound q p) :=
      lt_of_lt_of_le Prf.hyp0 (selected_bound X D C' q p).wk
    have ha := selected_found X D C q p hi
    have hb := (accepted_invariant h C C' q p _ hC.wk hC'.wk hr.wk hi).iffMp ha
    have one := (test_reflection X D C' q p _).iffMpr hb
    have z := selected_before (Γ := Δ) X D C' q p (selected X D C q p) Prf.hyp0
    exact .botE _ (BoundedReflection.one_ne_zero _ (one.eqSymm.eqTrans z))
  exact le_antisymm left right

def noHit (X : Interface) (D : Code) (C q p : PTm n) : Fm PTm n :=
  .all (lt (var 0) (ap2 D.bound (Syn.shift q) (Syn.shift p)) ⟶
    (test X D (Syn.shift C) (Syn.shift q) (Syn.shift p) (var 0) ≐ zero))

theorem no_hit_at (X : Interface) (D : Code) (C q p i : PTm n)
    (h : Γ ⊢[PRAAx] noHit X D C q p) (hi : Γ ⊢[PRAAx] lt i (ap2 D.bound q p)) :
    Γ ⊢[PRAAx] test X D C q p i ≐ zero := by
  have one := Prf.allE i h
  simp only [noHit,Fm.subst_imp,Fm.subst_eq,subst_lt,subst_test,subst_ap2,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,ConciseIPRA.PTm.subst_zero] at one
  exact .impE one hi

theorem selected_default (X : Interface) (D : Code) (C q p : PTm n)
    (h : Γ ⊢[PRAAx] noHit X D C q p) :
    Γ ⊢[PRAAx] selected X D C q p ≐ ap2 D.bound q p := by
  refine le_antisymm (selected_bound X D C q p) ?_
  refine .orE (lt_or_le (selected X D C q p) (ap2 D.bound q p)) ?_ Prf.hyp0
  let Δ := lt (selected X D C q p) (ap2 D.bound q p) :: Γ
  have ha := selected_found (Γ := Δ) X D C q p Prf.hyp0
  have e := (test_reflection X D C q p _).iffMpr ha
  have z := no_hit_at (Γ := Δ) X D C q p (selected X D C q p) h.wk Prf.hyp0
  exact .botE _ (BoundedReflection.one_ne_zero _ (e.eqSymm.eqTrans z))

theorem default_no_hit (X : Interface) (D : Code) (C q p : PTm n)
    (h : Γ ⊢[PRAAx] selected X D C q p ≐ ap2 D.bound q p) :
    Γ ⊢[PRAAx] noHit X D C q p := by
  refine .allI (.impI ?_)
  have shifted : Γ.map Fm.shift ⊢[PRAAx]
      selected X D (Syn.shift C) (Syn.shift q) (Syn.shift p) ≐ ap2 D.bound (Syn.shift q) (Syn.shift p) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  exact selected_before X D (Syn.shift C) (Syn.shift q) (Syn.shift p) (var 0)
    (lt_congr (.eqRefl _) shifted.wk.eqSymm Prf.hyp0)

theorem selected_congr (X : Interface) (D : Code) {C C' q q' p p' : PTm n}
    (hc : Γ ⊢[PRAAx] C ≐ C') (hq : Γ ⊢[PRAAx] q ≐ q') (hp : Γ ⊢[PRAAx] p ≐ p') :
    Γ ⊢[PRAAx] selected X D C q p ≐ selected X D C' q' p' := by
  have e := Prf.eqSubst (selected X D (var 0) (var 1) (var 2) ≐ var 3)
    ![C,q,p,selected X D C q p] ![C',q',p',selected X D C q p]
    (fun i => by fin_cases i; exact hc; exact hq; exact hp; exact .eqRefl _)
    (show Γ ⊢[PRAAx] (selected X D (var 0) (var 1) (var 2) ≐ var 3).subst
      ![C,q,p,selected X D C q p] from by simpa using Prf.eqRefl (selected X D C q p))
  simpa using e.eqSymm

def result (X : Interface) (D : Code) (C q p : PTm n) : PTm n := pairT C (selected X D C q p)
def transformF (X : Interface) (D : Code) : PR 3 := PTm.toPR (result X D (var 0) (var 1) (var 2))
def boundTerm (X : Interface) (D : Code) (q p : PTm n) : PTm n :=
  succ (pairT (masterBound X (demands D q p) p) (ap2 D.bound q p))
def verifierFormula (X : Interface) (D : Code) : BFm 3 :=
  .and (.eq (masterBit X (demands D (var 1) (var 2)) (fstT (var 0)) (var 2)) one)
    (.eq (sndT (var 0)) (selected X D (fstT (var 0)) (var 1) (var 2)))
def output (X : Interface) (D : Code) : Interface where
  query := PTm.toPR (one : PTm 2)
  bound := PTm.toPR (boundTerm X D (var 0) (var 1))
  verify := BoundedSyntax.bitF (verifierFormula X D)
  observe := PTm.toPR (sndT (var 0) : PTm 3)
  related := PTm.toPR (eqb (var 0) (var 1) : PTm 4)

ipra_subst result
ipra_subst boundTerm
theorem transform_at (X : Interface) (D : Code) (C q p : PTm n) : Γ ⊢[PRAAx]
    ap3 (transformF X D) C q p ≐ result X D C q p := by
  simpa [transformF,ap3] using toPR_eq (Γ := Γ) (result X D (var 0) (var 1) (var 2)) ![C,q,p]
theorem output_bound_at (X : Interface) (D : Code) (q p : PTm n) : Γ ⊢[PRAAx]
    ap2 (output X D).bound q p ≐ boundTerm X D q p := by
  simpa [output,ap2] using toPR_eq (Γ := Γ) (boundTerm X D (var 0) (var 1)) ![q,p]
theorem output_observation_at (X : Interface) (D : Code) (c q p : PTm n) : Γ ⊢[PRAAx]
    ap3 (output X D).observe c q p ≐ sndT c := by
  simpa [output,ap3] using toPR_eq (Γ := Γ) (sndT (var 0) : PTm 3) ![c,q,p]
theorem returned_index (X : Interface) (D : Code) (C q p : PTm n) : Γ ⊢[PRAAx]
    ap3 (output X D).observe (result X D C q p) q p ≐ selected X D C q p :=
  (output_observation_at X D _ _ _).eqTrans (snd_pair _ _)
theorem verifier_reflection (X : Interface) (D : Code) (c q p : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (ap3 (output X D).verify c q p ≐ one)
      ((masterBit X (demands D q p) (fstT c) p ≐ one) ⋏
        (sndT c ≐ selected X D (fstT c) q p)) := by
  have e := BoundedSyntax.program_correct (verifierFormula X D) ![c,q,p] (Γ := Γ)
  have h := (RealizerMasterInterface.eq_one_iff e).iffTrans
    (BoundedSyntax.bounded_reflection (verifierFormula X D) ![c,q,p])
  simpa [output,ap3,verifierFormula,BoundedSyntax.formula] using h
theorem verifier_sound (X : Interface) (D : Code) (c q p : PTm n)
    (h : Γ ⊢[PRAAx] ap3 (output X D).verify c q p ≐ one) : Γ ⊢[PRAAx]
    masterValid X (demands D q p) (fstT c) p ⋏ (sndT c ≐ selected X D (fstT c) q p) := by
  have hs := (verifier_reflection X D c q p).iffMp h
  exact .andI (masterBit_sound X _ _ _ (.andE₁ hs)) (.andE₂ hs)

theorem result_valid (X : Interface) (D : Code) (C q p : PTm n)
    (hC : Γ ⊢[PRAAx] masterValid X (demands D q p) C p) :
    Γ ⊢[PRAAx] valid (output X D) (result X D C q p) q p := by
  have cap := pair_mono (le_of_lt (.andE₁ hC)) (selected_bound X D C q p)
  have bound : Γ ⊢[PRAAx] lt (result X D C q p) (boundTerm X D q p) :=
    (succ_monus_succ _ _).eqTrans cap
  refine .andI (lt_congr (.eqRefl _) (output_bound_at X D q p).eqSymm bound) ?_
  apply (verifier_reflection X D _ q p).iffMpr
  have hc := fst_pair (Γ := Γ) C (selected X D C q p)
  have hv := masterValid_congr X (.eqRefl _) hc.eqSymm (.eqRefl _) hC
  exact .andI (masterBit_complete X _ _ _ hv)
    ((snd_pair _ _).eqTrans (selected_congr X D hc (.eqRefl _) (.eqRefl _)).eqSymm)

theorem result_related {X : Interface} {D : Code} (h : Laws X D) (C C' q p : PTm n)
    (hC : Γ ⊢[PRAAx] masterValid X (demands D q p) C p)
    (hC' : Γ ⊢[PRAAx] masterValid X (demands D q p) C' p)
    (hr : Γ ⊢[PRAAx] masterRelated X (demands D q p) C C' p) : Γ ⊢[PRAAx]
    related (output X D) (result X D C q p) (result X D C' q p) q p := by
  have sel := selected_stable h C C' q p hC hC' hr
  have obs := (returned_index X D C q p).eqTrans (sel.eqTrans (returned_index X D C' q p).eqSymm)
  have e : Γ ⊢[PRAAx] ap4 (output X D).related
      (ap3 (output X D).observe (result X D C q p) q p)
      (ap3 (output X D).observe (result X D C' q p) q p) q p ≐
      eqb (ap3 (output X D).observe (result X D C q p) q p)
        (ap3 (output X D).observe (result X D C' q p) q p) := by
    simpa [output,ap4] using toPR_eq (Γ := Γ) (eqb (var 0) (var 1) : PTm 4)
      ![ap3 (output X D).observe (result X D C q p) q p,
        ap3 (output X D).observe (result X D C' q p) q p,q,p]
  exact e.eqTrans (eqb_of_eq obs)

def existsHit (X : Interface) (D : Code) (C q p : PTm n) : Fm PTm n :=
  .ex (lt (var 0) (ap2 D.bound (Syn.shift q) (Syn.shift p)) ⋏
    accepted X D (Syn.shift C) (Syn.shift q) (Syn.shift p) (var 0))
theorem found_of_exists (X : Interface) (D : Code) (C q p : PTm n)
    (h : Γ ⊢[PRAAx] existsHit X D C q p) :
    Γ ⊢[PRAAx] lt (selected X D C q p) (ap2 D.bound q p) := by
  refine .exE h ?_
  let Δ := (lt (var 0) (ap2 D.bound (Syn.shift q) (Syn.shift p)) ⋏
    accepted X D (Syn.shift C) (Syn.shift q) (Syn.shift p) (var 0)) :: Γ.map Fm.shift
  have bound := accepted_bound (Γ := Δ) X D (Syn.shift C) (Syn.shift q) (Syn.shift p) (var 0)
    (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0)
  simpa only [Δ,existsHit,Fm.shift,subst_lt,subst_selected,subst_ap2,Syn.shift] using Prf.andE₁ bound

def specification (X : Interface) (D : Code) (C q p : PTm n) : Fm PTm n :=
  le (selected X D C q p) (ap2 D.bound q p) ⋏
    ((lt (selected X D C q p) (ap2 D.bound q p) ⟶ accepted X D C q p (selected X D C q p)) ⋏
      .all (lt (var 0) (Syn.shift (selected X D C q p)) ⟶
        (test X D (Syn.shift C) (Syn.shift q) (Syn.shift p) (var 0) ≐ zero)))
theorem selected_specification (X : Interface) (D : Code) (C q p : PTm n) :
    Γ ⊢[PRAAx] specification X D C q p := by
  refine .andI (selected_bound X D C q p) (.andI (.impI (selected_found X D C q p Prf.hyp0)) ?_)
  refine .allI (.impI ?_)
  exact selected_before X D (Syn.shift C) (Syn.shift q) (Syn.shift p) (var 0)
    (by simpa only [Syn.shift,subst_selected] using (Prf.hyp0 (Ax := PRAAx)
      (Γ := Γ.map Fm.shift) (φ := lt (var 0) (Syn.shift (selected X D C q p)))))

/-- The generated realizer's proofs are derived from the actual search and
its local observation law, rather than stored as client assumptions. -/
def realizer {X : Interface} {D : Code} (h : Laws X D) : Realizer X (output X D) where
  demand := demandF D
  transform := transformF X D
  guard := zero ≐ zero
  residuals := []
  sound := by
    apply valid_congr (output X D) (transform_at X D (var 0) (var 1) (var 2)).eqSymm (.eqRefl _) (.eqRefl _)
    apply result_valid
    exact masterValid_congr X (demand_at D (var 1) (var 2)) (.eqRefl _) (.eqRefl _) (.hyp (by simp))
  stable := by
    apply related_congr (output X D) (transform_at X D (var 0) (var 2) (var 3)).eqSymm
      (transform_at X D (var 1) (var 2) (var 3)).eqSymm (.eqRefl _) (.eqRefl _)
    apply result_related h
    · exact masterValid_congr X (demand_at D (var 2) (var 3)) (.eqRefl _) (.eqRefl _) (.hyp (by simp))
    · exact masterValid_congr X (demand_at D (var 2) (var 3)) (.eqRefl _) (.eqRefl _) (.hyp (by simp))
    · exact masterRelated_congr X (demand_at D (var 2) (var 3)) (.eqRefl _) (.eqRefl _) (.eqRefl _) (.hyp (by simp))

def code (X : Interface) (D : Code) : RealizerGraph.Code :=
  ⟨demandF D,transformF X D,zero ≐ zero,[]⟩
theorem realizer_code {X : Interface} {D : Code} (h : Laws X D) :
    RealizerGraph.Code.ofRealizer (realizer h) = code X D := rfl
def primitive {X : Interface} {D : Code} (h : Laws X D) : RealizerGraph.Primitive X (output X D) where
  code := code X D
  sound := (realizer h).sound
  stable := (realizer h).stable
def program {X : Interface} {D : Code} (h : Laws X D) : RealizerGraph.Program X (output X D) :=
  .primitive (primitive h)
theorem program_code {X : Interface} {D : Code} (h : Laws X D) :
    (program h).code = code X D := rfl

theorem least_search_specification_closed (X : Interface) (D : Code) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (specification X D (var 0) (var 1) (var 2)) :=
  closeUniv 3 (selected_specification X D _ _ _)
theorem least_search_default_closed (X : Interface) (D : Code) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (Fm.iff (selected X D (var 0) (var 1) (var 2) ≐ ap2 D.bound (var 1) (var 2))
        (noHit X D (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.andI (.impI (default_no_hit X D _ _ _ Prf.hyp0)) (.impI (selected_default X D _ _ _ Prf.hyp0)))
theorem least_search_success_closed (X : Interface) (D : Code) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (existsHit X D (var 0) (var 1) (var 2) ⟶
        lt (selected X D (var 0) (var 1) (var 2)) (ap2 D.bound (var 1) (var 2))) :=
  closeUniv 3 (.impI (found_of_exists X D _ _ _ Prf.hyp0))
theorem least_search_empty_closed (X : Interface) (D : Code) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (ap2 D.bound (var 1) (var 2) ≐ zero ⟶ selected X D (var 0) (var 1) (var 2) ≐ zero) :=
  closeUniv 3 (.impI (empty_bound X D _ _ _ Prf.hyp0))
theorem least_search_checker_closed (X : Interface) (D : Code) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (ap3 (output X D).verify (var 0) (var 1) (var 2) ≐ one ⟶
        (masterValid X (demands D (var 1) (var 2)) (fstT (var 0)) (var 2) ⋏
          sndT (var 0) ≐ selected X D (fstT (var 0)) (var 1) (var 2))) :=
  closeUniv 3 (.impI (verifier_sound X D _ _ _ Prf.hyp0))
theorem least_search_programs_closed (X : Interface) (D : Code) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (ap2 (demandF D) (var 1) (var 2) ≐ demands D (var 1) (var 2) ⋏
        (ap3 (transformF X D) (var 0) (var 1) (var 2) ≐ result X D (var 0) (var 1) (var 2) ⋏
          ap3 (output X D).observe (result X D (var 0) (var 1) (var 2)) (var 1) (var 2) ≐
            selected X D (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.andI (demand_at D _ _) (.andI (transform_at X D _ _ _) (returned_index X D _ _ _)))
theorem least_search_soundness {X : Interface} {D : Code} (h : Laws X D) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (soundFormula (realizer h)) :=
  bounded_realizer_soundness (realizer h)
theorem least_search_stability {X : Interface} {D : Code} (h : Laws X D) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (stabilityFormula (realizer h)) :=
  bounded_realizer_stability (realizer h)
theorem least_search_sealed {X : Interface} {D : Code} (h : Laws X D) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (sealedFormula (realizer h)) :=
  bounded_realizer_sealed (realizer h)
theorem least_search_metadata {X : Interface} {D : Code} (h : Laws X D) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (metadataFormula (realizer h)) :=
  realizer_program_metadata (realizer h)

end LeanProofs.IPRA.Foundations.RealizerLeastSearch
