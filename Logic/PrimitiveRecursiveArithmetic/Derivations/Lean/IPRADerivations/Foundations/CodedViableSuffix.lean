import IPRADerivations.Foundations.CodedViableChain

/-!
# Coded viable suffixes at an arbitrary numerical level

The actual PR4 iterator uses the original viability rows and stores all remaining
candidates. Its independent code bound uses only B, the horizon and the starting
level. The converse checks an arbitrary numerical sequence by object formulas
and genuine QF induction, without an external admissibility rule bundle.
-/
set_option autoImplicit false
namespace LeanProofs.IPRA.Foundations.CodedViableSuffix
open_ipra exports
open LeanProofs.IPRA.Foundations.BackwardViability
open LeanProofs.IPRA.Foundations.BackwardViability.Instance
open LeanProofs.IPRA.Foundations.ViableChain
open LeanProofs.IPRA.Foundations.CodedViableChain (g_values t_values nonzero_of_eq pair_mono)
open LeanProofs.IPRA.Foundations.MasterCertificate (sequence entry stack stack_succ stack_zero)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr subst_length)
variable {n : ℕ} {Γ : List (Fm PTm n)}

def remaining (I : Instance) (i p : PTm n) : PTm n := monus (I.h p) i
def suffixStep (I : Instance) : PTm 5 :=
  I.nxt (monus (I.h (var 4)) (var 2 + succ (var 0))) (var 1) (var 4)
def suffixF (I : Instance) : PR 4 := recDef (var 1 : PTm 3) (suffixStep I)
def suffixChain (I : Instance) (t i a p : PTm n) : PTm n := PTm.app (suffixF I) ![t,i,a,p]
def data (i a p : PTm n) : PTm n := pairT i (pairT a p)
def suffixBody (I : Instance) : PTm 2 :=
  suffixChain I (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1)))
def suffixCode (I : Instance) (i a p : PTm n) : PTm n :=
  sequence (suffixBody I) (succ (remaining I i p)) (data i a p)
def outputF (I : Instance) : PR 3 := PTm.toPR (suffixCode I (var 0) (var 1) (var 2))
def viableSuffixStart (I : Instance) (i a p : PTm n) : Fm PTm n :=
  lt a (I.bd i p) ⋏ I.V (remaining I i p) a p ≐ one

def localSuffix (I : Instance) (S i p : PTm n) : Fm PTm n := .all
  (le (var 0) (remaining I (Syn.shift i) (Syn.shift p)) ⟶
    (lt (entry (Syn.shift S) (var 0)) (I.bd (Syn.shift i + var 0) (Syn.shift p)) ⋏
      neg (I.g (Syn.shift i + var 0) (entry (Syn.shift S) (var 0)) (Syn.shift p) ≐ zero)))
def edgeSuffix (I : Instance) (S i p : PTm n) : Fm PTm n := .all
  (lt (var 0) (remaining I (Syn.shift i) (Syn.shift p)) ⟶
    neg (I.t (Syn.shift i + var 0) (entry (Syn.shift S) (var 0))
      (entry (Syn.shift S) (succ (var 0))) (Syn.shift p) ≐ zero))
def admissibleSuffix (I : Instance) (S i p : PTm n) : Fm PTm n :=
  length S ≐ succ (remaining I i p) ⋏ (localSuffix I S i p ⋏ edgeSuffix I S i p)
def boundStep (I : Instance) : PTm 4 := pairT (I.bd (var 2 + var 0) (var 3)) (var 1)
def boundF (I : Instance) : PR 3 := recDef (zero : PTm 2) (boundStep I)
def boundStack (I : Instance) (r i p : PTm n) : PTm n := PTm.app (boundF I) ![r,i,p]
def codeBound (I : Instance) (i p : PTm n) : PTm n :=
  succ (pairT (succ (remaining I i p)) (boundStack I (succ (remaining I i p)) i p))
def hasSuffix (I : Instance) (i a p : PTm n) : Fm PTm n := .ex
  (lt (var 0) (codeBound I (Syn.shift i) (Syn.shift p)) ⋏
    (admissibleSuffix I (var 0) (Syn.shift i) (Syn.shift p) ⋏ entry (var 0) zero ≐ Syn.shift a))

ipra_subst remaining
@[simp] theorem subst_suffixChain {m : ℕ} (σ : Fin n → PTm m) (I : Instance) (t i a p : PTm n) :
    Syn.subst σ (suffixChain I t i a p) = suffixChain I (Syn.subst σ t) (Syn.subst σ i)
      (Syn.subst σ a) (Syn.subst σ p) := by
  simp only [suffixChain,ConciseIPRA.PTm.subst_app]
  congr 1; funext j; fin_cases j <;> rfl
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (i a p : PTm n) :
    Syn.subst σ (data i a p) = data (Syn.subst σ i) (Syn.subst σ a) (Syn.subst σ p) := by simp [data]
ipra_subst suffixCode
ipra_subst viableSuffixStart
ipra_subst localSuffix [Syn.subst_shift, Syn.shift_subst]
ipra_subst edgeSuffix [Syn.subst_shift, Syn.shift_subst]
ipra_subst admissibleSuffix
@[simp] theorem subst_boundStack {m : ℕ} (σ : Fin n → PTm m) (I : Instance) (r i p : PTm n) :
    Syn.subst σ (boundStack I r i p) = boundStack I (Syn.subst σ r) (Syn.subst σ i) (Syn.subst σ p) := by
  simp only [boundStack,ConciseIPRA.PTm.subst_app]
  congr 1; funext j; fin_cases j <;> rfl
@[simp] theorem subst_codeBound {m : ℕ} (σ : Fin n → PTm m) (I : Instance) (i p : PTm n) :
    Syn.subst σ (codeBound I i p) = codeBound I (Syn.subst σ i) (Syn.subst σ p) := by simp [codeBound]
ipra_subst hasSuffix [Syn.subst_shift, Syn.shift_subst]

theorem suffix_zero (I : Instance) (i a p : PTm n) : Γ ⊢[PRAAx] suffixChain I zero i a p ≐ a := by
  simpa only [suffixChain, suffixF, Syn.subst_var, Matrix.cons_val_one, Matrix.cons_val_zero]
    using rec_zero_vecCons (Γ := Γ) (var 1 : PTm 3) (suffixStep I) ![i,a,p]

theorem suffix_succ (I : Instance) (t i a p : PTm n) : Γ ⊢[PRAAx]
    suffixChain I (succ t) i a p ≐
      I.nxt (monus (I.h p) (i + succ t)) (suffixChain I t i a p) p := by
  simpa [suffixChain, suffixF, suffixStep]
    using rec_succ_vecCons (Γ := Γ) (var 1 : PTm 3) (suffixStep I) t ![i,a,p]

theorem absolute_le (I : Instance) {i p t : PTm n}
    (hi : Γ ⊢[PRAAx] le i (I.h p)) (ht : Γ ⊢[PRAAx] le t (remaining I i p)) :
    Γ ⊢[PRAAx] le (i+t) (I.h p) :=
  le_congr (.eqRefl _) (eq_add_of_le hi).eqSymm (add_le_add₂ (le_refl i) ht)
theorem absolute_lt (I : Instance) {i p t : PTm n}
    (hi : Γ ⊢[PRAAx] le i (I.h p)) (ht : Γ ⊢[PRAAx] lt t (remaining I i p)) :
    Γ ⊢[PRAAx] lt (i+t) (I.h p) := by
  have h := absolute_le I hi ht
  exact le_congr (by ipra_ring : Γ ⊢[PRAAx] i+succ t ≐ succ (i+t)) (.eqRefl _) h

theorem absolute_reverse (I : Instance) {i p j : PTm n}
    (hi : Γ ⊢[PRAAx] le i (I.h p)) (hj : Γ ⊢[PRAAx] le j (remaining I i p)) :
    Γ ⊢[PRAAx] i + monus (remaining I i p) j ≐ monus (I.h p) j := by
  have hjH := le_trans hj (ChainViability.monus_le _ _)
  ipra_lc [remaining] natEq (eq_add_of_le hjH) - natEq (eq_add_of_le hi) - natEq (eq_add_of_le hj)

theorem nxt_index_congr (I : Instance) {j k a p : PTm n} (h : Γ ⊢[PRAAx] j ≐ k) :
    Γ ⊢[PRAAx] I.nxt j a p ≐ I.nxt k a p := by
  ipra_congr (I.nxt (var 0) (var 1) (var 2) : PTm 3) with [h, .eqRefl a, .eqRefl p]

/-- Unfold the original viability table at an arbitrary absolute level. -/
theorem viable_step (I : Instance) {l c p : PTm n} (hl : Γ ⊢[PRAAx] lt l (I.h p))
    (hb : Γ ⊢[PRAAx] lt c (I.bd l p))
    (hv : Γ ⊢[PRAAx] I.V (monus (I.h p) l) c p ≐ one) : Γ ⊢[PRAAx]
    neg (I.g l c p ≐ zero) ⋏
      (lt (I.nxt (monus (I.h p) (succ l)) c p) (I.bd (succ l) p) ⋏
        (neg (I.t l c (I.nxt (monus (I.h p) (succ l)) c p) p ≐ zero) ⋏
          I.V (monus (I.h p) (succ l)) (I.nxt (monus (I.h p) (succ l)) c p) p ≐ one)) := by
  have a1 := monus_succ_sub hl
  have a2 := monus_sub hl
  have a3 := succ_monus hl
  have u := V_unfold I (lt_congr (.eqRefl _) (bd_congr I a1.eqSymm) hb)
    ((V_congr I a3 (.eqRefl _)).eqTrans hv)
  exact .andI (nonzero_of_eq (g_congr I a1.eqSymm) (Prf.andE₁ u))
    (.andI (lt_congr (.eqRefl _) (bd_congr I a2) (Prf.andE₁ (Prf.andE₂ u)))
      (.andI (nonzero_of_eq (t_congr I a1.eqSymm) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ u))))
        (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ u)))))

theorem viable_local (I : Instance) {l c p : PTm n} (hl : Γ ⊢[PRAAx] le l (I.h p))
    (hb : Γ ⊢[PRAAx] lt c (I.bd l p))
    (hv : Γ ⊢[PRAAx] I.V (monus (I.h p) l) c p ≐ one) : Γ ⊢[PRAAx]
    neg (I.g l c p ≐ zero) := by
  refine .orE (lt_or_eq_of_le hl) ?_ ?_
  · exact Prf.andE₁ (viable_step I Prf.hyp0 hb.wk hv.wk)
  · have eq : (l ≐ I.h p)::Γ ⊢[PRAAx] l ≐ I.h p := Prf.hyp0
    have z := (congrMonus (Γ := (l ≐ I.h p)::Γ) (.eqRefl (I.h p)) eq).eqTrans (monus_self _)
    have hbh := lt_congr (.eqRefl _) (bd_congr I eq) hb.wk
    have v0 := (V_zero I hbh).eqSymm.eqTrans ((V_congr I z.eqSymm (.eqRefl _)).eqTrans hv.wk)
    refine .impI (BoundedReflection.one_ne_zero _ (v0.wk.eqSymm.eqTrans (BoundedFormulas.sg_of_zero ?_)))
    exact (g_congr I eq.wk.eqSymm).eqTrans Prf.hyp0

theorem suffix_step (I : Instance) {t i a p : PTm n}
    (hi : Γ ⊢[PRAAx] le i (I.h p)) (ht : Γ ⊢[PRAAx] lt t (remaining I i p))
    (hb : Γ ⊢[PRAAx] lt (suffixChain I t i a p) (I.bd (i+t) p))
    (hv : Γ ⊢[PRAAx] I.V (monus (I.h p) (i+t)) (suffixChain I t i a p) p ≐ one) : Γ ⊢[PRAAx]
    neg (I.g (i+t) (suffixChain I t i a p) p ≐ zero) ⋏
      (neg (I.t (i+t) (suffixChain I t i a p) (suffixChain I (succ t) i a p) p ≐ zero) ⋏
        (lt (suffixChain I (succ t) i a p) (I.bd (i+succ t) p) ⋏
          I.V (monus (I.h p) (i+succ t)) (suffixChain I (succ t) i a p) p ≐ one)) := by
  have e : Γ ⊢[PRAAx] i+succ t ≐ succ (i+t) := by ipra_ring
  have cs := (suffix_succ I t i a p).eqTrans (nxt_index_congr I (congrMonus (.eqRefl _) e))
  have u := viable_step I (absolute_lt I hi ht) hb hv
  exact .andI (Prf.andE₁ u)
    (.andI (nonzero_of_eq (t_values I _ _ _ _ _ _ (.eqRefl _) cs) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ u))))
      (.andI (lt_congr cs.eqSymm (bd_congr I e.eqSymm) (Prf.andE₁ (Prf.andE₂ u)))
        ((V_congr I (congrMonus (.eqRefl _) e) cs).eqTrans (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ u))))))

def invariant (I : Instance) (i a p t : PTm n) : Fm PTm n :=
  le t (remaining I i p) ⟶ (lt (suffixChain I t i a p) (I.bd (i+t) p) ⋏
    I.V (monus (I.h p) (i+t)) (suffixChain I t i a p) p ≐ one)
ipra_subst invariant

theorem suffix_invariant (I : Instance) (i a p t : PTm n)
    (hi : Γ ⊢[PRAAx] le i (I.h p)) (h : Γ ⊢[PRAAx] viableSuffixStart I i a p)
    (ht : Γ ⊢[PRAAx] le t (remaining I i p)) : Γ ⊢[PRAAx]
    lt (suffixChain I t i a p) (I.bd (i+t) p) ⋏
      I.V (monus (I.h p) (i+t)) (suffixChain I t i a p) p ≐ one := by
  let j : PTm (n + 1) := var 0
  let P := lt (suffixChain I j (Syn.shift i) (Syn.shift a) (Syn.shift p))
      (I.bd (Syn.shift i + j) (Syn.shift p)) ⋏
    I.V (monus (I.h (Syn.shift p)) (Syn.shift i + j))
      (suffixChain I j (Syn.shift i) (Syn.shift a) (Syn.shift p)) (Syn.shift p) ≐ one
  have hs : Γ.map Fm.shift ⊢[PRAAx] viableSuffixStart I (Syn.shift i) (Syn.shift a) (Syn.shift p) := by
    simpa only [Fm.shift, subst_viableSuffixStart, Syn.shift] using h.shift
  have his : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift i) (I.h (Syn.shift p)) := by
    simpa only [Fm.shift, subst_le, Instance.subst_h, Syn.shift] using hi.shift
  have result : Γ ⊢[PRAAx] P.subst (Syn.inst t) := by
    refine qfIndAtMost ht ⟨lt_QF _ _, trivial⟩ ?_ ?_
    · simp [P, j]
      exact .andI (lt_congr (suffix_zero I i a p).eqSymm (bd_congr I (add_zero i).eqSymm) (Prf.andE₁ h))
        ((V_congr I (congrMonus (.eqRefl _) (add_zero i)) (suffix_zero I i a p)).eqTrans (Prf.andE₂ h))
    · have shiftBound : Syn.shift (remaining I i p) = remaining I (Syn.shift i) (Syn.shift p) := by simp [Syn.shift]
      simp [P, j, shiftBound]
      exact .impI (Prf.andE₂ (Prf.andE₂
        (suffix_step I his.wk.wk Prf.hyp0 (Prf.andE₁ Prf.hyp1) (Prf.andE₂ Prf.hyp1))))
  simpa [P, j] using result

theorem suffix_local (I : Instance) (i a p t : PTm n)
    (hi : Γ ⊢[PRAAx] le i (I.h p)) (h : Γ ⊢[PRAAx] viableSuffixStart I i a p)
    (ht : Γ ⊢[PRAAx] le t (remaining I i p)) : Γ ⊢[PRAAx]
    neg (I.g (i+t) (suffixChain I t i a p) p ≐ zero) := by
  have r := suffix_invariant I i a p t hi h ht
  exact viable_local I (absolute_le I hi ht) (Prf.andE₁ r) (Prf.andE₂ r)
theorem suffix_edge (I : Instance) (i a p t : PTm n)
    (hi : Γ ⊢[PRAAx] le i (I.h p)) (h : Γ ⊢[PRAAx] viableSuffixStart I i a p)
    (ht : Γ ⊢[PRAAx] lt t (remaining I i p)) : Γ ⊢[PRAAx]
    neg (I.t (i+t) (suffixChain I t i a p) (suffixChain I (succ t) i a p) p ≐ zero) := by
  have r := suffix_invariant I i a p t hi h (le_of_lt ht)
  exact Prf.andE₁ (Prf.andE₂ (suffix_step I hi ht (Prf.andE₁ r) (Prf.andE₂ r)))

theorem body_at (I : Instance) (t i a p : PTm n) : Γ ⊢[PRAAx]
    inst2 (suffixBody I) t (data i a p) ≐ suffixChain I t i a p := by
  simp only [suffixBody,inst2,subst_suffixChain,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  apply congrApp
  intro j
  fin_cases j
  · exact .eqRefl _
  · exact fst_pair _ _
  · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  · exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
theorem suffix_length (I : Instance) (i a p : PTm n) : Γ ⊢[PRAAx]
    length (suffixCode I i a p) ≐ succ (remaining I i p) := MasterCertificate.sequence_length _ _ _
theorem suffix_lookup (I : Instance) (i a p t : PTm n)
    (ht : Γ ⊢[PRAAx] le t (remaining I i p)) : Γ ⊢[PRAAx]
    entry (suffixCode I i a p) t ≐ suffixChain I t i a p :=
  (MasterCertificate.sequence_decode (suffixBody I) (x := data i a p)
    ((succ_monus_succ _ _).eqTrans ht)).eqTrans (body_at I t i a p)
theorem suffix_start (I : Instance) (i a p : PTm n) : Γ ⊢[PRAAx]
    entry (suffixCode I i a p) zero ≐ a :=
  (suffix_lookup I i a p zero (zero_le _)).eqTrans (suffix_zero I i a p)

theorem local_at (I : Instance) (S i p t : PTm n)
    (h : Γ ⊢[PRAAx] admissibleSuffix I S i p) (ht : Γ ⊢[PRAAx] le t (remaining I i p)) : Γ ⊢[PRAAx]
    lt (entry S t) (I.bd (i+t) p) ⋏ neg (I.g (i+t) (entry S t) p ≐ zero) := by
  have rule : Γ ⊢[PRAAx] le t (remaining I i p) ⟶
      (lt (entry S t) (I.bd (i+t) p) ⋏ neg (I.g (i+t) (entry S t) p ≐ zero)) := by
    simpa [localSuffix] using (Prf.andE₁ (Prf.andE₂ h)).allE t
  exact .impE rule ht
theorem edge_at (I : Instance) (S i p t : PTm n)
    (h : Γ ⊢[PRAAx] admissibleSuffix I S i p) (ht : Γ ⊢[PRAAx] lt t (remaining I i p)) : Γ ⊢[PRAAx]
    neg (I.t (i+t) (entry S t) (entry S (succ t)) p ≐ zero) := by
  have rule : Γ ⊢[PRAAx] lt t (remaining I i p) ⟶
      neg (I.t (i+t) (entry S t) (entry S (succ t)) p ≐ zero) := by
    simpa [edgeSuffix] using (Prf.andE₂ (Prf.andE₂ h)).allE t
  exact .impE rule ht

theorem produced_admissible (I : Instance) (i a p : PTm n)
    (hi : Γ ⊢[PRAAx] le i (I.h p)) (h : Γ ⊢[PRAAx] viableSuffixStart I i a p) : Γ ⊢[PRAAx]
    admissibleSuffix I (suffixCode I i a p) i p := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] viableSuffixStart I (Syn.shift i) (Syn.shift a) (Syn.shift p) := by
    simpa only [Fm.shift,subst_viableSuffixStart,Syn.shift] using h.shift
  have his : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift i) (I.h (Syn.shift p)) := by
    simpa only [Fm.shift,subst_le,Instance.subst_h,Syn.shift] using hi.shift
  refine .andI (suffix_length I i a p) (.andI ?_ ?_)
  · refine .allI (.impI ?_)
    have r := suffix_invariant I (Syn.shift i) (Syn.shift a) (Syn.shift p) (var 0) his.wk hs.wk Prf.hyp0
    simpa only [subst_suffixCode,Syn.shift] using
      (.andI (lt_congr (suffix_lookup I _ _ _ _ Prf.hyp0).eqSymm (.eqRefl _) (Prf.andE₁ r))
        (nonzero_of_eq (g_values I _ _ _ _ (suffix_lookup I _ _ _ _ Prf.hyp0))
          (suffix_local I _ _ _ _ his.wk hs.wk Prf.hyp0)))
  · refine .allI (.impI ?_)
    simpa only [subst_suffixCode,Syn.shift] using
      nonzero_of_eq (t_values I _ _ _ _ _ _
        (suffix_lookup I _ _ _ _ (le_of_lt Prf.hyp0)) (suffix_lookup I _ _ _ _ Prf.hyp0))
        (suffix_edge I _ _ _ _ his.wk hs.wk Prf.hyp0)

theorem coded_viable_zero (I : Instance) (S i p : PTm n)
    (hi : Γ ⊢[PRAAx] le i (I.h p)) (h : Γ ⊢[PRAAx] admissibleSuffix I S i p) : Γ ⊢[PRAAx]
    I.V zero (entry S (monus (remaining I i p) zero)) p ≐ one := by
  have terminal := local_at I S i p (remaining I i p) h (le_refl _)
  have e := (eq_add_of_le hi).eqSymm
  have hb := lt_congr (.eqRefl _) (bd_congr I e) (Prf.andE₁ terminal)
  have hg := nonzero_of_eq (g_congr I e.eqSymm) (Prf.andE₂ terminal)
  exact (V_congr I (.eqRefl _) (entry_congr (.eqRefl _) (monus_zero _))).eqTrans
    ((V_zero I hb).eqTrans (FiniteGluing.sg_of_ne hg))

theorem coded_viable_step (I : Instance) (S i p j : PTm n)
    (hi : Γ ⊢[PRAAx] le i (I.h p)) (h : Γ ⊢[PRAAx] admissibleSuffix I S i p)
    (hj : Γ ⊢[PRAAx] lt j (remaining I i p))
    (ih : Γ ⊢[PRAAx] I.V j (entry S (monus (remaining I i p) j)) p ≐ one) : Γ ⊢[PRAAx]
    I.V (succ j) (entry S (monus (remaining I i p) (succ j))) p ≐ one := by
  have now := local_at I S i p (monus (remaining I i p) (succ j)) h (ChainViability.monus_le _ _)
  have next := local_at I S i p (monus (remaining I i p) j) h (ChainViability.monus_le _ _)
  have edge := edge_at I S i p _ h (ChainViability.monus_succ_lt hj)
  have current := absolute_reverse I hi hj
  have following := absolute_reverse I hi (le_of_lt hj)
  have positions := entry_congr (Γ := Γ) (.eqRefl S) (succ_monus hj)
  have correct := nonzero_of_eq
    ((t_congr I current.eqSymm).eqTrans (t_values I _ _ _ _ _ _ (.eqRefl _) positions.eqSymm)) edge
  exact V_fold I (lt_congr (.eqRefl _) (bd_congr I current) (Prf.andE₁ now))
    (nonzero_of_eq (g_congr I current.eqSymm) (Prf.andE₂ now))
    (lt_congr (.eqRefl _) (bd_congr I following) (Prf.andE₁ next)) correct ih

def reverseLaw (I : Instance) (S i p j : PTm n) : Fm PTm n :=
  le j (remaining I i p) ⟶ I.V j (entry S (monus (remaining I i p) j)) p ≐ one
ipra_subst reverseLaw

theorem coded_viable (I : Instance) (S i p j : PTm n)
    (hi : Γ ⊢[PRAAx] le i (I.h p)) (h : Γ ⊢[PRAAx] admissibleSuffix I S i p)
    (hj : Γ ⊢[PRAAx] le j (remaining I i p)) : Γ ⊢[PRAAx]
    I.V j (entry S (monus (remaining I i p) j)) p ≐ one := by
  let P := I.V (var 0)
      (entry (Syn.shift S) (monus (remaining I (Syn.shift i) (Syn.shift p)) (var 0))) (Syn.shift p) ≐ one
  have hs : Γ.map Fm.shift ⊢[PRAAx] admissibleSuffix I (Syn.shift S) (Syn.shift i) (Syn.shift p) := by
    simpa only [Fm.shift, subst_admissibleSuffix, Syn.shift] using h.shift
  have his : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift i) (I.h (Syn.shift p)) := by
    simpa only [Fm.shift, subst_le, Instance.subst_h, Syn.shift] using hi.shift
  have result : Γ ⊢[PRAAx] P.subst (Syn.inst j) := by
    refine qfIndAtMost hj trivial ?_ ?_
    · simpa [P] using coded_viable_zero I S i p hi h
    · have shiftBound : Syn.shift (remaining I i p) = remaining I (Syn.shift i) (Syn.shift p) := by simp [Syn.shift]
      simp [P, shiftBound]
      exact .impI (coded_viable_step I _ _ _ _ his.wk.wk hs.wk.wk Prf.hyp0 Prf.hyp1)
  simpa [P] using result

theorem coded_start_viable (I : Instance) (S i p : PTm n)
    (hi : Γ ⊢[PRAAx] le i (I.h p)) (h : Γ ⊢[PRAAx] admissibleSuffix I S i p) : Γ ⊢[PRAAx]
    viableSuffixStart I i (entry S zero) p := by
  have loc := local_at I S i p zero h (zero_le _)
  exact .andI (lt_congr (.eqRefl _) (bd_congr I (add_zero i)) (Prf.andE₁ loc))
    ((V_congr I (.eqRefl _) (entry_congr (.eqRefl _) (monus_self _))).eqSymm.eqTrans
      (coded_viable I S i p (remaining I i p) hi h (le_refl _)))

theorem boundStack_zero (I : Instance) (i p : PTm n) : Γ ⊢[PRAAx]
    boundStack I zero i p ≐ zero := by
  simpa only [boundStack, boundF, ConciseIPRA.PTm.subst_zero]
    using rec_zero_vecCons (Γ := Γ) (zero : PTm 2) (boundStep I) ![i,p]

theorem boundStack_succ (I : Instance) (r i p : PTm n) : Γ ⊢[PRAAx]
    boundStack I (succ r) i p ≐ pairT (I.bd (i+r) p) (boundStack I r i p) := by
  simpa [boundF, boundStack, boundStep]
    using rec_succ_vecCons (Γ := Γ) (zero : PTm 2) (boundStep I) r ![i,p]

def sizeLaw (I : Instance) (i a p r : PTm n) : Fm PTm n :=
  le r (succ (remaining I i p)) ⟶ le (stack (suffixBody I) r (data i a p)) (boundStack I r i p)
ipra_subst sizeLaw [stack]

theorem stack_bound_step (I : Instance) (i a p r : PTm n)
    (hi : Γ ⊢[PRAAx] le i (I.h p)) (h : Γ ⊢[PRAAx] viableSuffixStart I i a p)
    (hr : Γ ⊢[PRAAx] le r (remaining I i p))
    (ih : Γ ⊢[PRAAx] le (stack (suffixBody I) r (data i a p)) (boundStack I r i p)) : Γ ⊢[PRAAx]
    le (stack (suffixBody I) (succ r) (data i a p)) (boundStack I (succ r) i p) := by
  have bound := le_of_lt (Prf.andE₁ (suffix_invariant I i a p r hi h hr))
  have actual := (stack_succ (Γ := Γ) (suffixBody I) r (data i a p)).eqTrans
    (congrPairT (body_at I r i a p) (.eqRefl _))
  exact le_congr actual.eqSymm (boundStack_succ I r i p).eqSymm (pair_mono bound ih)

theorem produced_size_bound (I : Instance) (i a p : PTm n)
    (hi : Γ ⊢[PRAAx] le i (I.h p)) (h : Γ ⊢[PRAAx] viableSuffixStart I i a p) : Γ ⊢[PRAAx]
    lt (suffixCode I i a p) (codeBound I i p) := by
  let P := le (stack (suffixBody I) (var 0) (data (Syn.shift i) (Syn.shift a) (Syn.shift p)))
    (boundStack I (var 0) (Syn.shift i) (Syn.shift p))
  have hs : Γ.map Fm.shift ⊢[PRAAx] viableSuffixStart I (Syn.shift i) (Syn.shift a) (Syn.shift p) := by
    simpa only [Fm.shift, subst_viableSuffixStart, Syn.shift] using h.shift
  have his : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift i) (I.h (Syn.shift p)) := by
    simpa only [Fm.shift, subst_le, Instance.subst_h, Syn.shift] using hi.shift
  have result : Γ ⊢[PRAAx] P.subst (Syn.inst (succ (remaining I i p))) := by
    refine qfIndUpTo (succ (remaining I i p)) (le_QF _ _) ?_ ?_
    · simpa [P] using le_congr (stack_zero (Γ := Γ) (suffixBody I) _).eqSymm
        (boundStack_zero I i p).eqSymm (le_refl zero)
    · have shiftBound : Syn.shift (succ (remaining I i p)) = succ (remaining I (Syn.shift i) (Syn.shift p)) := by simp [Syn.shift]
      simp [P, shiftBound]
      exact .impI (stack_bound_step I _ _ _ _ his.wk.wk hs.wk.wk
        ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0) Prf.hyp1)
  exact (succ_monus_succ _ _).eqTrans (pair_mono (le_refl _) (by simpa [P] using result))

theorem suffix_exists (I : Instance) (i a p : PTm n)
    (hi : Γ ⊢[PRAAx] le i (I.h p)) (h : Γ ⊢[PRAAx] viableSuffixStart I i a p) : Γ ⊢[PRAAx]
    hasSuffix I i a p := by
  apply Prf.exI (t := suffixCode I i a p)
  simpa [hasSuffix] using .andI (produced_size_bound I i a p hi h)
    (.andI (produced_admissible I i a p hi h) (suffix_start I i a p))

theorem exists_start_viable (I : Instance) (i a p : PTm n)
    (hi : Γ ⊢[PRAAx] le i (I.h p)) (h : Γ ⊢[PRAAx] hasSuffix I i a p) : Γ ⊢[PRAAx]
    viableSuffixStart I i a p := by
  refine .exE h ?_
  let Δ := (lt (var 0) (codeBound I (Syn.shift i) (Syn.shift p)) ⋏
    (admissibleSuffix I (var 0) (Syn.shift i) (Syn.shift p) ⋏ entry (var 0) zero ≐ Syn.shift a)) :: Γ.map Fm.shift
  have his : Δ ⊢[PRAAx] le (Syn.shift i) (I.h (Syn.shift p)) := by
    simpa only [Fm.shift,subst_le,Instance.subst_h,Syn.shift] using hi.shift.wk
  have correct := coded_start_viable (Γ := Δ) I (var 0) (Syn.shift i) (Syn.shift p) his
    (Prf.andE₁ (Prf.andE₂ Prf.hyp0))
  have initial : Δ ⊢[PRAAx] entry (var 0) zero ≐ Syn.shift a := Prf.andE₂ (Prf.andE₂ Prf.hyp0)
  have moved : Δ ⊢[PRAAx] viableSuffixStart I (Syn.shift i) (Syn.shift a) (Syn.shift p) :=
    .andI (lt_congr initial (.eqRefl _) (Prf.andE₁ correct))
      ((V_congr I (.eqRefl _) initial.eqSymm).eqTrans (Prf.andE₂ correct))
  simpa only [Δ,Fm.shift,subst_viableSuffixStart,Syn.shift] using moved

theorem coded_suffix_iff (I : Instance) (i a p : PTm n) (hi : Γ ⊢[PRAAx] le i (I.h p)) : Γ ⊢[PRAAx]
    Fm.iff (viableSuffixStart I i a p) (hasSuffix I i a p) :=
  .andI (.impI (suffix_exists I i a p hi.wk Prf.hyp0)) (.impI (exists_start_viable I i a p hi.wk Prf.hyp0))
theorem suffix_iff (I : Instance) (i a p : PTm n) (hi : Γ ⊢[PRAAx] le i (I.h p))
    (ha : Γ ⊢[PRAAx] lt a (I.bd i p)) : Γ ⊢[PRAAx]
    Fm.iff (I.V (remaining I i p) a p ≐ one) (hasSuffix I i a p) :=
  .andI (.impI (suffix_exists I i a p hi.wk (.andI ha.wk Prf.hyp0)))
    (.impI (Prf.andE₂ (exists_start_viable I i a p hi.wk Prf.hyp0)))

def boundProgramF (I : Instance) : PR 2 := PTm.toPR (codeBound I (var 0) (var 1))
def run (I : Instance) (i a p : PTm n) : PTm n := PTm.app (outputF I) ![i,a,p]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (I : Instance) (i a p : PTm n) :
    Syn.subst σ (run I i a p) = run I (Syn.subst σ i) (Syn.subst σ a) (Syn.subst σ p) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1; funext j; fin_cases j <;> rfl

theorem output_at (I : Instance) (i a p : PTm n) : Γ ⊢[PRAAx]
    run I i a p ≐ suffixCode I i a p := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (suffixCode I (var 0) (var 1) (var 2)) ![i,a,p]
theorem bound_program_at (I : Instance) (i p : PTm n) : Γ ⊢[PRAAx]
    ap2 (boundProgramF I) i p ≐ codeBound I i p := by
  simpa [boundProgramF,ap2] using toPR_eq (Γ := Γ) (codeBound I (var 0) (var 1)) ![i,p]
theorem returned_length (I : Instance) (i a p : PTm n) : Γ ⊢[PRAAx]
    length (run I i a p) ≐ succ (remaining I i p) :=
  (congrFst (output_at I i a p)).eqTrans (suffix_length I i a p)
theorem returned_start (I : Instance) (i a p : PTm n) : Γ ⊢[PRAAx]
    entry (run I i a p) zero ≐ a :=
  (entry_congr (output_at I i a p) (.eqRefl _)).eqTrans (suffix_start I i a p)
theorem returned_lookup (I : Instance) (i a p t : PTm n)
    (ht : Γ ⊢[PRAAx] le t (remaining I i p)) : Γ ⊢[PRAAx]
    entry (run I i a p) t ≐ suffixChain I t i a p :=
  (entry_congr (output_at I i a p) (.eqRefl _)).eqTrans (suffix_lookup I i a p t ht)
theorem returned_bound (I : Instance) (i a p : PTm n)
    (hi : Γ ⊢[PRAAx] le i (I.h p)) (h : Γ ⊢[PRAAx] viableSuffixStart I i a p) : Γ ⊢[PRAAx]
    lt (run I i a p) (codeBound I i p) :=
  lt_congr (output_at I i a p).eqSymm (.eqRefl _) (produced_size_bound I i a p hi h)
theorem returned_admissible (I : Instance) (i a p : PTm n)
    (hi : Γ ⊢[PRAAx] le i (I.h p)) (h : Γ ⊢[PRAAx] viableSuffixStart I i a p) : Γ ⊢[PRAAx]
    admissibleSuffix I (run I i a p) i p := by
  have e := output_at (Γ := Γ) I i a p
  simpa only [subst_admissibleSuffix,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Prf.eqSubst (admissibleSuffix I (var 0) (Syn.shift i) (Syn.shift p))
      (Syn.inst (suffixCode I i a p)) (Syn.inst (run I i a p)) (fun j => by
        cases j using Fin.cases
        · exact e.eqSymm
        · exact .eqRefl _)
      (by simpa using produced_admissible I i a p hi h)

theorem actual_suffix_recursion_closed (I : Instance) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (suffixChain I zero (var 2) (var 1) (var 0) ≐ var 1 ⋏
      suffixChain I (succ (var 3)) (var 2) (var 1) (var 0) ≐
        I.nxt (monus (I.h (var 0)) (var 2 + succ (var 3)))
          (suffixChain I (var 3) (var 2) (var 1) (var 0)) (var 0)) :=
  closeUniv 4 (.andI (suffix_zero I _ _ _) (suffix_succ I _ _ _ _))
theorem actual_suffix_program_closed (I : Instance) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run I (var 2) (var 1) (var 0) ≐ suffixCode I (var 2) (var 1) (var 0) ⋏
      (length (run I (var 2) (var 1) (var 0)) ≐ succ (remaining I (var 2) (var 0)) ⋏
        entry (run I (var 2) (var 1) (var 0)) zero ≐ var 1)) :=
  closeUniv 3 (.andI (output_at I _ _ _) (.andI (returned_length I _ _ _) (returned_start I _ _ _)))
theorem actual_suffix_lookup_closed (I : Instance) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (remaining I (var 2) (var 0)) ⟶
      entry (run I (var 2) (var 1) (var 0)) (var 3) ≐ suffixChain I (var 3) (var 2) (var 1) (var 0)) :=
  closeUniv 4 (.impI (returned_lookup I _ _ _ _ Prf.hyp0))
theorem produced_suffix_certificate_closed (I : Instance) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (I.h (var 0)) ⟶ viableSuffixStart I (var 2) (var 1) (var 0) ⟶
      (admissibleSuffix I (suffixCode I (var 2) (var 1) (var 0)) (var 2) (var 0) ⋏
        lt (suffixCode I (var 2) (var 1) (var 0)) (codeBound I (var 2) (var 0)))) :=
  closeUniv 3 (.impI (.impI (.andI (produced_admissible I _ _ _ Prf.hyp1 Prf.hyp0)
    (produced_size_bound I _ _ _ Prf.hyp1 Prf.hyp0))))
theorem arbitrary_coded_suffix_viable_closed (I : Instance) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 1) (I.h (var 0)) ⟶ admissibleSuffix I (var 2) (var 1) (var 0) ⟶
      le (var 3) (remaining I (var 1) (var 0)) ⟶
        I.V (var 3) (entry (var 2) (monus (remaining I (var 1) (var 0)) (var 3))) (var 0) ≐ one) :=
  closeUniv 4 (.impI (.impI (.impI (coded_viable I _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem coded_suffix_equivalence_closed (I : Instance) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (I.h (var 0)) ⟶
      Fm.iff (viableSuffixStart I (var 2) (var 1) (var 0)) (hasSuffix I (var 2) (var 1) (var 0))) :=
  closeUniv 3 (.impI (coded_suffix_iff I _ _ _ Prf.hyp0))
theorem source_suffix_equivalence_closed (I : Instance) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (I.h (var 0)) ⟶ lt (var 1) (I.bd (var 2) (var 0)) ⟶
      Fm.iff (I.V (remaining I (var 2) (var 0)) (var 1) (var 0) ≐ one)
        (hasSuffix I (var 2) (var 1) (var 0))) :=
  closeUniv 3 (.impI (.impI (suffix_iff I _ _ _ Prf.hyp1 Prf.hyp0)))
theorem independent_suffix_bound_closed (I : Instance) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 (boundProgramF I) (var 1) (var 0) ≐ codeBound I (var 1) (var 0)) :=
  closeUniv 2 (bound_program_at I _ _)
theorem returned_suffix_certificate_closed (I : Instance) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (I.h (var 0)) ⟶ viableSuffixStart I (var 2) (var 1) (var 0) ⟶
      (admissibleSuffix I (run I (var 2) (var 1) (var 0)) (var 2) (var 0) ⋏
        lt (run I (var 2) (var 1) (var 0)) (codeBound I (var 2) (var 0)))) :=
  closeUniv 3 (.impI (.impI (.andI (returned_admissible I _ _ _ Prf.hyp1 Prf.hyp0)
    (returned_bound I _ _ _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Foundations.CodedViableSuffix
