import IPRADerivations.Foundations.BoundedFormulas
import IPRADerivations.Core.ClockedDescent
import IPRADerivations.AnalyticNumberTheory.Totatives

/-!
# Finite master certificates

Packet: `foundations/fiber_ipra_2026-11-16`, Theorem `thm:master`.

A code is a pair of its length and a reverse list built from the checked
pairing functions. `entry code i` is a primitive-recursive decoder. The
length-dependent lookup equation is proved by quantifier-free induction.

For a bounded formula `A(c, query)` and a bound `b(query)`, the master code
stores the least accepted certificate at each query `query = ⟨i, x⟩`. A
pointwise bounded-totality hypothesis implies validity of every decoded
entry below the master length. All witnesses and the sequence code are
primitive recursive.
-/

namespace LeanProofs.IPRA.Foundations.MasterCertificate

open_ipra exports
open LeanProofs.IPRA.Foundations.BoundedFormulas

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Drop `k` heads of a paired reverse list. -/
abbrev drop (k code : PTm n) : PTm n := ClockedDescent.orb (sndT (var 0)) k code

@[simp] theorem subst_drop {m : ℕ} (σ : Fin n → PTm m) (k code : PTm n) :
    Syn.subst σ (drop k code) = drop (Syn.subst σ k) (Syn.subst σ code) :=
  ClockedDescent.subst_orb σ k code

theorem drop_zero (code : PTm n) : Γ ⊢[PRAAx] drop zero code ≐ code :=
  ClockedDescent.orb_zero code

theorem drop_succ (k code : PTm n) : Γ ⊢[PRAAx] drop (succ k) code ≐ sndT (drop k code) := by
  simpa [inst1] using ClockedDescent.orb_succ (Γ := Γ) (D := sndT (var 0)) k code

/-- Variables `0 = k`, `1 = head`, `2 = tail`. -/
private abbrev dropPushFormula : Fm PTm 3 :=
  drop (succ (var 0)) (pairT (var 1) (var 2)) ≐ drop (var 0) (var 2)

private theorem drop_push_open : ([] : List (Fm PTm 3)) ⊢[PRAAx] dropPushFormula := by
  ipra_ind [dropPushFormula, subst_drop, subst_pairT]
  · exact (drop_succ zero _).eqTrans ((congrSnd (drop_zero _)).eqTrans
      ((snd_pair _ _).eqTrans (drop_zero _).eqSymm))
  · exact (drop_succ _ _).eqTrans ((congrSnd Prf.hyp0).eqTrans (drop_succ _ _).eqSymm)

theorem drop_push (k head tail : PTm n) :
    Γ ⊢[PRAAx] drop (succ k) (pairT head tail) ≐ drop k tail := by
  have h := inst (Γ := Γ) drop_push_open (![k, head, tail] : Fin 3 → PTm n)
  simpa only [Fm.subst_eq, subst_drop, subst_pairT, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    ConciseIPRA.PTm.subst_succ] using h

/-- Prepend the next value. Step variables are the index, old stack and data. -/
def stackStep (values : PTm 2) : PTm 3 :=
  pairT (Syn.subst ![var 0, var 2] values) (var 1)

abbrev stackF (values : PTm 2) : PR 2 := rec2 zero (stackStep values)

/-- The reversed list of the first `N` values. -/
abbrev stack (values : PTm 2) (N x : PTm n) : PTm n := ap2 (stackF values) N x

theorem stack_zero (values : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] stack values zero x ≐ zero := by
  simpa using rec2_zero (Γ := Γ) zero (stackStep values) x

private theorem stack_step_at (values : PTm 2) (N previous x : PTm n) :
    Syn.subst ![N, previous, x] (stackStep values) = pairT (inst2 values N x) previous := by
  simp only [stackStep, subst_pairT, Syn.subst_subst, Syn.subst_var, Matrix.cons_val_one]
  congr 1
  simp only [inst2]
  congr 1
  funext i
  fin_cases i <;> simp

theorem stack_succ (values : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] stack values (succ N) x ≐ pairT (inst2 values N x) (stack values N x) := by
  have h := rec2_succ (Γ := Γ) zero (stackStep values) N x
  rw [stack_step_at] at h
  exact h

/-- A length and a reverse list constitute the sequence code. -/
def sequence (values : PTm 2) (N x : PTm n) : PTm n := pairT N (stack values N x)

/-- Decode index `i` using the length stored in the code. -/
def entry (code i : PTm n) : PTm n :=
  fstT (drop (monus (fstT code) (succ i)) (sndT code))

@[simp] theorem subst_sequence {m : ℕ} (values : PTm 2) (N x : PTm n) (σ : Fin n → PTm m) :
    Syn.subst σ (sequence values N x) = sequence values (Syn.subst σ N) (Syn.subst σ x) := by
  simp only [sequence, subst_pairT, subst_ap2]

@[simp] theorem subst_entry {m : ℕ} (code i : PTm n) (σ : Fin n → PTm m) :
    Syn.subst σ (entry code i) = entry (Syn.subst σ code) (Syn.subst σ i) := by
  simp only [entry, subst_fstT, subst_sndT, subst_drop, PTm.subst_monus, ConciseIPRA.PTm.subst_succ]

private abbrev rawEntry (values : PTm 2) (N i x : PTm n) : PTm n :=
  fstT (drop (monus N (succ i)) (stack values N x))

private theorem entry_sequence (values : PTm 2) (N i x : PTm n) :
    Γ ⊢[PRAAx] entry (sequence values N x) i ≐ rawEntry values N i x :=
  congrFst (congrAp2 _ (congrMonus (fst_pair _ _) (.eqRefl _)) (snd_pair _ _))

/-- Variables `0 = N`, `1 = i`, `2 = x`. -/
private abbrev lookupFormula (values : PTm 2) : Fm PTm 3 :=
  lt (var 1) (var 0) ⟶ rawEntry values (var 0) (var 1) (var 2) ≐ inst2 values (var 1) (var 2)

private theorem lookup_open (values : PTm 2) : ([] : List (Fm PTm 3)) ⊢[PRAAx] lookupFormula values := by
  ipra_ind (⟨lt_QF _ _, trivial⟩) [lookupFormula, rawEntry, subst_lt, subst_fstT, subst_drop, subst_ap2, subst_inst2]
  · exact .impI (lt_zero_absurd _ Prf.hyp0)
  · refine .impI ?_
    let Δ : List (Fm PTm 3) := lt (var 1) (succ (var 0)) :: [lookupFormula values]
    have hIndex : Δ ⊢[PRAAx] lt (var 1) (succ (var 0)) := Prf.hyp0
    refine .orE (lt_succ_cases hIndex) ?_ ?_
    · have hlt : (lt (var 1) (var 0) :: Δ) ⊢[PRAAx] lt (var 1) (var 0) := Prf.hyp0
      have depth := (succ_monus_succ (Γ := lt (var 1) (var 0) :: Δ) (var 0) (var 1)).eqTrans
        (monus_succ_of_lt hlt)
      have tail := congrFst ((congrAp2 _ depth (stack_succ values (var 0) (var 2))).eqTrans
        (drop_push (monus (var 0) (succ (var 1))) (inst2 values (var 0) (var 2)) (stack values (var 0) (var 2))))
      exact tail.eqTrans (Prf.impE Prf.hyp1.wk hlt)
    · let C := (var 1 ≐ var 0) :: Δ
      have hEq : C ⊢[PRAAx] var 1 ≐ var 0 := Prf.hyp0
      have depth : C ⊢[PRAAx] monus (succ (var 0)) (succ (var 1)) ≐ zero :=
        (succ_monus_succ _ _).eqTrans ((congrMonus (.eqRefl _) hEq).eqTrans (monus_self _))
      have head := congrFst ((congrAp2 _ depth (stack_succ values (var 0) (var 2))).eqTrans
        (drop_zero _))
      exact head.eqTrans ((fst_pair _ _).eqTrans (congrInst2 values hEq.eqSymm (.eqRefl _)))

/-- The primitive-recursive sequence decoder returns the value at every in-range index. -/
theorem sequence_decode (values : PTm 2) {N i x : PTm n} (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] entry (sequence values N x) i ≐ inst2 values i x := by
  have h := inst (Γ := Γ) (lookup_open values) (![N, i, x] : Fin 3 → PTm n)
  simp only [lookupFormula, rawEntry, Fm.subst_imp, Fm.subst_eq, subst_lt, subst_fstT,
    subst_drop, subst_ap2, subst_inst2, PTm.subst_monus, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, ConciseIPRA.PTm.subst_succ] at h
  exact (entry_sequence values N i x).eqTrans (Prf.impE h hi)

/-- The stored sequence length is exact. -/
theorem sequence_length (values : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] fstT (sequence values N x) ≐ N := fst_pair _ _

/-- The least accepted certificate for query `⟨i, x⟩`. -/
def certificate (b : PTm 1) (A : BF) : PTm 2 :=
  bfWit b A (pairT (var 0) (var 1))

private theorem certificate_at (b : PTm 1) (A : BF) (i x : PTm n) :
    inst2 (certificate b A) i x = bfWit b A (pairT i x) := by
  simp only [certificate, inst2, bfWit, BoundedReflection.wit, Search.mu,
    subst_ap2, at1_subst, subst_pairT, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one]

/-- Assemble all bounded least certificates by primitive recursion. -/
def master (b : PTm 1) (A : BF) (N x : PTm n) : PTm n :=
  sequence (certificate b A) N x

@[simp] theorem subst_master {m : ℕ} (b : PTm 1) (A : BF) (N x : PTm n)
    (σ : Fin n → PTm m) :
    Syn.subst σ (master b A N x) = master b A (Syn.subst σ N) (Syn.subst σ x) :=
  subst_sequence _ _ _ _

theorem master_decode (b : PTm 1) (A : BF) {N i x : PTm n} (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] entry (master b A N x) i ≐ bfWit b A (pairT i x) := by
  simpa only [master, certificate_at] using sequence_decode (certificate b A) (x := x) hi

/-- The code records precisely the requested number of certificates. -/
theorem master_length (b : PTm 1) (A : BF) (N x : PTm n) :
    Γ ⊢[PRAAx] fstT (master b A N x) ≐ N := sequence_length _ _ _

/-- Every query below `N` has an accepted certificate below its query bound. -/
def totality (b : PTm 1) (A : BF) (N x : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶
    fmAt (.ex b A) (n + 1) (pairT (var 0) (Syn.shift x)))

/-- Every in-range decoded entry is bounded and accepted by the verifier. -/
def validity (b : PTm 1) (A : BF) (N x : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶
    (lt (entry (master b A (Syn.shift N) (Syn.shift x)) (var 0))
        (at1 b (pairT (var 0) (Syn.shift x))) ⋏
      fmAt A (n + 1)
        (pairT (entry (master b A (Syn.shift N) (Syn.shift x)) (var 0))
          (pairT (var 0) (Syn.shift x)))))

private theorem fmAt_congr (A : BF) {u v : PTm n} (h : Γ ⊢[PRAAx] u ≐ v)
    (hu : Γ ⊢[PRAAx] fmAt A n u) : Γ ⊢[PRAAx] fmAt A n v := by
  have source : Γ ⊢[PRAAx] (fmAt A 1 (var 0)).subst ![u] := by
    simpa only [fmAt_subst, Syn.subst_var, Matrix.cons_val_zero] using hu
  have target := Prf.eqSubst (fmAt A 1 (var 0)) ![u] ![v]
    (fun i => by fin_cases i; exact h) source
  simpa only [fmAt_subst, Syn.subst_var, Matrix.cons_val_zero] using target

private alias pair_congr := Common.congrPairT

/-- `thm:master`: bounded pointwise totality validates the explicit PR master code. -/
theorem master_valid (b : PTm 1) (A : BF) (N x : PTm n)
    (hTotal : Γ ⊢[PRAAx] totality b A N x) : Γ ⊢[PRAAx] validity b A N x := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (Syn.shift N) := Prf.hyp0
  have hEx : Δ ⊢[PRAAx] fmAt (.ex b A) (n + 1) (pairT (var 0) (Syn.shift x)) :=
    Prf.impE hTotal.allOpen.wk hi
  have found := bf_choice b A (pairT (var 0) (Syn.shift x)) hEx
  have decoded := master_decode b A (x := Syn.shift x) hi
  exact .andI (lt_congr decoded.eqSymm (.eqRefl _) (Prf.andE₁ found))
    (fmAt_congr A (pair_congr decoded.eqSymm (.eqRefl _)) (Prf.andE₂ found))

/-- The master-certificate implication with natural variables `N` and `x`. -/
def masterFormula (b : PTm 1) (A : BF) : Fm PTm 2 :=
  totality b A (var 0) (var 1) ⟶ validity b A (var 0) (var 1)

/-- Universally closed object-theory master-certificate theorem. -/
theorem master_closed (b : PTm 1) (A : BF) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (masterFormula b A) :=
  closeUniv 2 (.impI (master_valid b A (var 0) (var 1) Prf.hyp0))

end LeanProofs.IPRA.Foundations.MasterCertificate

export_ipra Foundations.MasterCertificate (sequence_decode sequence_length stack stack_succ stack_zero subst_sequence)
